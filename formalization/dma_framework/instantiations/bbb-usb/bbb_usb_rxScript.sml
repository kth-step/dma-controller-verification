open HolKernel Parse boolLib bossLib;
open bbb_usb_stateTheory bbb_usb_functionsTheory;

val _ = new_theory "bbb_usb_rx";

Definition rx_fetch_bd_addresses:
rx_fetch_bd_addresses queue_id internal_state =
  if internal_state.qhp queue_id = 0w then
    ([], tag)
  else
    (get_bd_ras internal_state.registers (internal_state.qhp queue_id), tag)
End

(*
rx_fetch_bd(queue_id, internal_state, fetched_bd) ≔
	endpoint_id ≔ internal_state.current_rx_endpoint							//Scheduler updates current endpoint.
	endpoint ≔ internal_state.endpoint_rx endpoint_id
	endpoint.next_descriptor_pointer ≔ qhp[queue_id]							//Next descriptor pointer for previous BD.

	if endpoint.bd_index = 0b00 then											//SOP
		endpoint.start_buffer_address ≔ fetched_bd[4] + RXGCR[endpoint_id].RX_SOP_OFFSET
		endpoint.state ≔ transfer_data
		endpoint.number_of_written_bytes_of_dma_packet ≔ 0
		endpoint.sop_bd_queue_id ≔ queue_id										//Used by the scheduler to identify the channel with the SOP BD, when in state write_back_sop_bd1.
		endpoint.sop_bd_ra ≔ qhp[queue_id]										//Used by write back to find the SOP bd among the bds to write back.
	else
		endpoint.start_buffer_address ≔ fetched_bd[4]
		endpoint.state ≔ write_back_previous_bd									//Write back next descriptor pointer of previous BD in channel endpoint.previous_queue_id.

	endpoint.free_buffer_size ≔ fetched_bd[3][21:0]
	endpoint.number_of_written_bytes_to_buffer ≔ 0								//No bytes written yet.

	if fetched_bd.li.EOQ then
		qhp[queue_id] ≔ 0
		qtp[queue_id] ≔ 0
	else
		qhp[queue_id] ≔ li_to_next_bd_address(fetched_bd.li)

	return (internal_state, fetched_bd)
*)

Definition rx_fetch_bd:
(rx_fetch_bd queue_id internal_state NONE = (internal_state, NONE)) /\
(rx_fetch_bd queue_id internal_state (SOME (fetched_bd_bytes : 8 word list, tag : 8 word)) =
  if internal_state.qhp queue_id = 0w then
    (internal_state, NONE)
  else
    let endpoint_id = internal_state.current_rx_endpoint_id in
    let endpoint = internal_state.endpoints_rx endpoint_id in
    let registers = internal_state.registers in
    let (bd, li) = form_bd_li fetched_bd_bytes in
    let bd_ras = get_bd_ras registers (internal_state.qhp queue_id) in
    let bd_was = bd_ras in
    let next_descriptor_pointer = internal_state.qhp queue_id in
    let start_buffer_address = if endpoint.bd_index = 0w then (buffer_pointer bd) + ((23 >< 16) (registers.RXGCR endpoint_id)) else buffer_pointer bd in
    let state = if endpoint.bd_index = 0w then rx_transfer_data else rx_write_back_previous_bd in
    let number_of_written_bytes_of_dma_packet = if endpoint.bd_index = 0w then 0w else endpoint.number_of_written_bytes_of_dma_packet in
    let sop_bd_queue_id = if endpoint.bd_index = 0w then queue_id else endpoint.sop_bd_queue_id in
    let sop_bd_ra = if endpoint.bd_index = 0w then internal_state.qhp queue_id else endpoint.sop_bd_ra in
    let number_of_written_bytes_to_buffer = 0w in
    let endpoint = endpoint with <|
      next_descriptor_pointer := next_descriptor_pointer;
      start_buffer_address := start_buffer_address;
      state := state;
      number_of_written_bytes_of_dma_packet := number_of_written_bytes_of_dma_packet;
      sop_bd_queue_id := sop_bd_queue_id;
      sop_bd_ra := sop_bd_ra;
      number_of_written_bytes_to_buffer := number_of_written_bytes_to_buffer;
    |> in
    let qhp = if li_to_eoq li then 0w else li_to_next_bd_address registers li in
    let qtp = if li_to_eoq li then 0w else internal_state.qtp queue_id in
    let internal_state = internal_state with <| endpoints_rx := (endpoint_id =+ endpoint) internal_state.endpoints_rx;
                                                qhp := (queue_id =+ qhp) internal_state.qhp;
                                                qtp := (queue_id =+ qtp) internal_state.qtp |> in
      (internal_state, SOME (((bd, li), bd_ras, bd_was), no_update)))
End

(*
rx_process_replies_generate_requests(queue_id, internal_state, current_bd, replies) ≔
	endpoint_id ≔ internal_state.current_rx_endpoint							//Scheduler updates current endpoint.
	endpoint ≔ internal_state.endpoint_rx endpoint_id

	//Determince the number of bytes to write to memory.
	if LENGTH endpoint.usb_packet ≥ 64 ∧ endpoint.free_buffer_size ≥ 64 then
		number_of_bytes_to_write ≔ 64
	else if LENGTH usb_packet ≥ free_buffer_size then
		number_of_bytes_to_write ≔ endpoint.free_buffer_size
	else	//LENGTH usb_packet < free_buffer_size
		number_of_bytes_to_write ≔ LENGTH endpoint.usb_packet

	//Write part of USB packet to memory.
	start_address ≔ endpoint.start_buffer_address + endpoint.number_of_written_bytes_to_buffer
	end_address ≔ start_address + number_of_bytes_to_write - 1
	(bytes_to_write, endpoint.usb_packet) ≔ SPLIT number_of_bytes_to_write usb_packet

	endpoint.number_of_written_bytes_to_buffer ≔ endpoint.number_of_written_bytes_to_buffer + number_of_bytes_to_write

	//Determine whether the buffer is filled or the USB packet
	//completely written to memory.
	endpoint.free_buffer_size ≔ current_bd[3][21:0] - endpoint.number_of_written_bytes_to_buffer
	if LENGTH endpoint.usb_packet = 0 ∨ endpoint.free_buffer_size = 0 then
		endpoint.number_of_written_bytes_of_dma_packet ≔ endpoint.number_of_written_bytes_of_dma_packet + endpoint.number_of_written_bytes_to_buffer
		endpoint.state ≔ write_back_current_bd
		complete_flag ≔ true
	else
		complete_flag ≔ false

	//MEMORY WRITE REQUEST:	memory[end_address:start_address] ≔ bytes_to_write
	return (internal_state, ([start_address...end_address], bytes_to_write), complete_flag)
*)

Definition zero_or_positive_subtraction:
zero_or_positive_subtraction x y = (if x >=+ y then x - y else 0w)
End

Definition get_number_of_bytes_to_write:
get_number_of_bytes_to_write buffer_size offset usb_packet_length =
  if offset >= buffer_size then (* All data has been transferred. Nothing remains. *)
    0
  else if offset + 64 <= buffer_size /\ usb_packet_length >= 64 then
    64
  else if usb_packet_length >= buffer_size - offset then (* Remaining data in USB packet fills the buffer. *)
    buffer_size - offset
  else
    usb_packet_length
End

Definition rx_process_replies_generate_requests:
rx_process_replies_generate_requests internal_state (bd : num -> 32 word, li : 32 word) replies =
  let endpoint_id = internal_state.current_rx_endpoint_id in
  let endpoint = internal_state.endpoints_rx endpoint_id in
  let registers = internal_state.registers in
  let offset = endpoint.number_of_written_bytes_to_buffer + if endpoint.bd_index = 0w then (23 >< 16) (registers.RXGCR endpoint_id) else 0w in

  let number_of_bytes_to_write = get_number_of_bytes_to_write (w2n (buffer_length bd)) (w2n offset) (LENGTH endpoint.usb_packet) in
    if number_of_bytes_to_write > 0 then
      let start_address = buffer_pointer bd + offset in
      let write_addresses = generate_consecutive_addresses start_address number_of_bytes_to_write in

      let bytes_to_write = TAKE number_of_bytes_to_write endpoint.usb_packet in
      let address_bytes = ZIP (write_addresses, bytes_to_write) in
      let write_request = request_write address_bytes tag in
      let usb_packet = DROP number_of_bytes_to_write endpoint.usb_packet in
      let number_of_written_bytes_to_buffer = endpoint.number_of_written_bytes_to_buffer + n2w number_of_bytes_to_write in
      let number_of_written_bytes_of_dma_packet = endpoint.number_of_written_bytes_of_dma_packet + n2w number_of_bytes_to_write in
      let rx_sop_offset = if endpoint.bd_index = 0w then (23 >< 16) (registers.RXGCR endpoint_id) : 32 word else 0w in
      let buffer_size = if endpoint.bd_index = 0w then zero_or_positive_subtraction (buffer_length bd) rx_sop_offset else buffer_length bd in
      let free_buffer_size = zero_or_positive_subtraction buffer_size endpoint.number_of_written_bytes_to_buffer in
      let remaining_free_buffer_space = free_buffer_size - n2w number_of_bytes_to_write in
      let state = if remaining_free_buffer_space = 0w then rx_write_back_current_bd else endpoint.state in
      let endpoint = endpoint with <| usb_packet := usb_packet;
    	                              number_of_written_bytes_to_buffer := (15 >< 0) number_of_written_bytes_to_buffer;
    	                              number_of_written_bytes_of_dma_packet := (15 >< 0) number_of_written_bytes_of_dma_packet;
    	                              state := state;
    	                            |> in
      let internal_state = internal_state with endpoints_rx := (endpoint_id =+ endpoint) internal_state.endpoints_rx in
      let complete_flag = (remaining_free_buffer_space = 0w) in
    	(internal_state, [write_request], complete_flag)
    else
      let endpoint = endpoint with state := rx_write_back_current_bd in
      let internal_state = internal_state with endpoints_rx := (endpoint_id =+ endpoint) internal_state.endpoints_rx in
    	(internal_state, [], T)
End

(*
	if endpoint.state = write_back_current_bd then
		(bd, bd_ras, bd_was) ≔ LAST bds_to_write_back

		if LENGTH endpoint.usb_packet > 0 then																//Additional BDs needed.
			if endpoint.bd_index < 3 then
				endpoint.bd_index ≔ endpoint.bd_index + 1

			case cdma_rx.bd_index = 0b01:
				endpoint.next_queue_id ≔ RXHPCRA0.RX_HOST_FDQ1_QNUM[7:0]
			case cdma_rx.bd_index = 0b10:
				endpoint.next_queue_id ≔ RXHPCRB0.RX_HOST_FDQ2_QNUM[7:0]
			case cdma_rx.bd_index = 0b11:
				endpoint.next_queue_id ≔ RXHPCRB0.RX_HOST_FDQ3_QNUM[7:0]

			address_bytes5 ≔ []																				//Next descriptor pointer is written back for this non-EOP BD in the state write_back_previous_bd.
			endpoint.previous_queue_id ≔ queue_id															//previous_queue_id is used by the scheduler when the state is write_back_previous_bd
			endpoint.state ≔ fetch_bd
		else																								//USB packet written to memory. Write back last BD and SOP.
			endpoint.next_queue_id ≔ RXHPCRA0.RX_HOST_FDQ0_QNUM[7:0]
			endpoint.bd_index ≔ 0b00																		//Next BD is 1st.
			addresses_word5 ≔ word_addresses bd_was 5
			address_bytes5 ≔ ZIP (addresses_word5, TO_WORD32_BYTES 0)										//Generates 4 bytes from 0 (Null descriptor pointer).
			endpoint.state ≔ write_back_sop_bd1

		addresses_word3 ≔ word_addresses bd_was 3
		addresses_word4 ≔ word_addresses bd_was 4
		address_bytes3 ≔ ZIP (addresses_word3, TO_WORD32_BYTES endpoint.number_of_written_bytes_to_buffer)	//Generates 4 bytes from number_of_written_bytes_to_buffer.
		address_bytes4 ≔ ZIP (addresses_word4, TO_WORD32_BYTES endpoint.start_buffer_address)				//Generates 4 bytes from start_buffer_address.
		return (internal_state, address_bytes3 ++ address_bytes4 ++ address_bytes5, [])						//No released BDs.
*)
Definition find_next_queue_id:
find_next_queue_id registers endpoint endpoint_id current_bd_index =
  if LENGTH endpoint.usb_packet > 0 then
    if      current_bd_index = 1w then (23 >< 16) (registers.RXHPCRA endpoint_id)
    else if current_bd_index = 2w then ( 7 ><  0) (registers.RXHPCRB endpoint_id)
    else                               (23 >< 16) (registers.RXHPCRB endpoint_id)
  else
    (7 >< 0) (registers.RXHPCRA endpoint_id)
End

Definition find_next_bd_index:
find_next_bd_index endpoint =
  if LENGTH endpoint.usb_packet > 0 then
    if endpoint.bd_index <+ 3w then
      endpoint.bd_index + 1w
    else
      endpoint.bd_index
  else
    0w
End

Definition rx_write_back_current_bd:
(rx_write_back_current_bd queue_id internal_state endpoint_id [] = (internal_state, [], tag, [])) /\
(rx_write_back_current_bd queue_id internal_state endpoint_id (bd::bds : (((num -> 32 word) # 32 word) # 32 word list # 32 word list) list) =
  let endpoint = internal_state.endpoints_rx endpoint_id in
  let (bd_li, bd_ras, bd_was) = LAST (bd::bds) in
  let next_queue_id = find_next_queue_id internal_state.registers endpoint endpoint_id endpoint.bd_index in
  let bd_index = find_next_bd_index endpoint in
  let previous_queue_id = if LENGTH endpoint.usb_packet > 0 then queue_id else endpoint.previous_queue_id in
  let state = if LENGTH endpoint.usb_packet > 0 then rx_fetch_bd else rx_write_back_sop_bd1 in
  let address_bytes3 = merge_lists (word32aligned bd_was 3, word32_to_bytes endpoint.number_of_written_bytes_to_buffer) in
  let address_bytes4 = merge_lists (word32aligned bd_was 4, word32_to_bytes endpoint.start_buffer_address) in
  let address_bytes5 = if LENGTH endpoint.usb_packet > 0 then [] else merge_lists (word32aligned bd_was 5, word32_to_bytes 0w) in
  let endpoint = endpoint with <| current_queue_id := next_queue_id;
                                  bd_index := bd_index;
                                  previous_queue_id := previous_queue_id;
                                  state := state |> in
  let internal_state = internal_state with endpoints_rx := (endpoint_id =+ endpoint) internal_state.endpoints_rx in
    (internal_state, address_bytes3 ++ address_bytes4 ++ address_bytes5, tag, [] : (((num -> 32 word) # 32 word) # 32 word list # 32 word list) list)
)
End

(*	else if endpoint.state = write_back_previous_bd then
		(bd, bd_ras, bd_was) ≔ LAST bds_to_write_back
		addresses_word5 ≔ word_addresses bd_was 5
		address_bytes5 ≔ ZIP (addresses_word5, TO_WORD32_BYTES 	endpoint.next_descriptor_pointer)			//Generates 4 bytes from fetched_bd_address.
		endpoint.state ≔ transfer_data
		return (internal_state, address_bytes5, [(bd, bd_ras, bd_was)])										//Release current_bd.
*)
Definition rx_write_back_previous_bd:
(rx_write_back_previous_bd internal_state endpoint_id [] = (internal_state, [], tag, [])) /\
(rx_write_back_previous_bd internal_state endpoint_id (bd::bds) =
  let endpoint = internal_state.endpoints_rx endpoint_id in
  let (bd, bd_ras, bd_was) = LAST (bd::bds) in
  let address_bytes5 = merge_lists (word32aligned bd_was 5, word32_to_bytes endpoint.next_descriptor_pointer) in
  let endpoint = endpoint with state := rx_transfer_data in
  let internal_state = internal_state with endpoints_rx := (endpoint_id =+ endpoint) internal_state.endpoints_rx in
    (internal_state, address_bytes5, tag, [(bd, bd_ras, bd_was)])
)
End

(*	else if endpoint.state = write_back_sop_bd1 then
		(sop_bd, sop_bd_ras, sop_bd_was) ≔ FIND (\(bd, bd_ras, bd_was). HD bd_ras = endpoint.sop_bd_ra) bds_to_write_back

		addresses_word0 ≔ word_addresses sop_bd_was 0
		addresses_word1 ≔ word_addresses sop_bd_was 1
		addresses_word2 ≔ word_addresses sop_bd_was 2
		sop_bd_word1 ≔ sop_bd[1]
		sop_bd_word1[31:27] ≔ endpoint_id
		sop_bd_word1[26:21] ≔ environment.source_tag_channel
		sop_bd_word1[20:16] ≔ environment.source_tag_sub_channel
		sop_bd_word2 ≔ sop_bd[2]
		sop_bd_word2[31] ≔ environment.packet_error
		sop_bd_word2[30:26] ≔ environment.type_of_packet
		sop_bd_word2[19] ≔ environment.zero_length_packet_indicator
		address_bytes0 ≔ ZIP (addresses_word0, TO_WORD32_BYTES endpoint.number_of_written_bytes_of_dma_packet)
		address_bytes1 ≔ ZIP (addresses_word1, sop_bd_word1)
		address_bytes2 ≔ ZIP (addresses_word2, sop_bd_word2)

		endpoint.write_back_bd_queue_id ≔ RXGCR[endpoint_id].RX_DEFAULT_RQ_QNUM								//Append SOP BD to completion queue.

		endpoint.state ≔ write_back_sop_bd2
		return (internal_state, address_bytes0 ++ address_bytes1 ++ address_bytes2, [])						//Write back SOP but do not release it.
*)
Definition rx_write_back_sop_bd1:
(rx_write_back_sop_bd1 environment internal_state endpoint_id [] = (internal_state, [], tag, [])) /\
(rx_write_back_sop_bd1 environment internal_state endpoint_id (bd::bds) =
  let endpoint = internal_state.endpoints_rx endpoint_id in
    case FIND (\(bd, bd_ras, bd_was). HD bd_ras = endpoint.sop_bd_ra) (bd::bds) of
      NONE => (internal_state, [], tag, [])
    | SOME ((sop_bd, sop_li), sop_bd_ras, sop_bd_was) =>
      let addresses_word0 = word32aligned sop_bd_was 0 in
      let addresses_word1 = word32aligned sop_bd_was 1 in
      let addresses_word2 = word32aligned sop_bd_was 2 in
      let sop_bd_word0 = sop_bd 0 in
      let sop_bd_word1_15_0 = ((15 >< 0) (sop_bd 1)) : 16 word in
      let sop_bd_word1_20_0 = (environment.source_tag_sub_channel @@ sop_bd_word1_15_0) : 21 word in
      let sop_bd_word1_26_0 = (environment.source_tag_channel @@ sop_bd_word1_20_0) : 27 word in
      let sop_bd_word1 = (endpoint_id @@ sop_bd_word1_26_0) : 32 word in
      let sop_bd_word2_18_0 = ((18 >< 0) (sop_bd 2)) : 19 word in
      let sop_bd_word2_19_0 = (environment.zero_length_packet_indicator @@ sop_bd_word2_18_0) : 20 word in
      let sop_bd_word2_24_0 = (environment.type_of_packet @@ sop_bd_word2_19_0) : 25 word in
      let sop_bd_word2 = (environment.packet_error @@ sop_bd_word2_24_0) : 32 word in
      let address_bytes0 = merge_lists (addresses_word0, word32_to_bytes sop_bd_word0) in
      let address_bytes1 = merge_lists (addresses_word1, word32_to_bytes sop_bd_word1) in
      let address_bytes2 = merge_lists (addresses_word2, word32_to_bytes sop_bd_word2) in
      let endpoint = endpoint with <| write_back_bd_queue_id := (7 >< 0) (internal_state.registers.RXGCR endpoint_id);
                                      state := rx_write_back_sop_bd2 |> in
      let internal_state = internal_state with endpoints_rx := (endpoint_id =+ endpoint) internal_state.endpoints_rx in
        (internal_state, address_bytes0 ++ address_bytes1 ++ address_bytes2, tag, [])
)
End

(*	else if cdma_rx.state = write_back_sop_bd2 then
		(sop_bd, sop_bd_ras, sop_bd_was) ≔ FIND (\(bd, bd_ras, bd_was). HD bd_ras = endpoint.sop_bd_ra) bds_to_write_back

		if ctp[endpoint.write_back_bd_queue_id] = 0 then
			chp[endpoint.write_back_bd_queue_id] ≔ endpoint.sop_bd_ra
			endpoint.state ≔ fetch_bd																		//Process next BD, DMA/USB packet.
		else
			endpoint.state ≔ write_back_sop_bd3																//Schedule write back of previous tail SOP BD.

		ctp[endpoint.write_back_bd_queue_id] ≔ endpoint.sop_bd_ra
		li ≔ {next_bd_mr ≔ 0; next_bd_mr_index ≔ 0; next_bd_size ≔ 0; EOQ ≔ 1}							//Update linking information of the new tail SOP BD.
		li_address ≔ bd_address_to_li_address(HD sop_bd_was)
		return (internal_state, (li_address, li, 4), [])													//WRITE REQUEST memory4[li_address] ≔ li. No BD released since BDs might be appended.
*)
Definition rx_write_back_sop_bd2:
(rx_write_back_sop_bd2 internal_state endpoint_id [] = (internal_state, [], tag, [])) /\
(rx_write_back_sop_bd2 internal_state endpoint_id (bd::bds) =
  let endpoint = internal_state.endpoints_rx endpoint_id in
    case FIND (\(bd, bd_ras, bd_was). HD bd_ras = endpoint.sop_bd_ra) (bd::bds) of
      NONE => (internal_state, [], tag, [])
    | SOME ((sop_bd, sop_li), sop_bd_ras, sop_bd_was) =>
      let chp = if internal_state.ctp endpoint.write_back_bd_queue_id = 0w then endpoint.sop_bd_ra else internal_state.chp endpoint.write_back_bd_queue_id in
      let ctp = endpoint.sop_bd_ra in
      let state = if internal_state.ctp endpoint.write_back_bd_queue_id = 0w then rx_fetch_bd else rx_write_back_sop_bd3 in
      let li_bytes = form_li_bytes 0 0w 0w T in
      let li_addresses = DROP 32 sop_bd_was in
      let li_address_bytes = merge_lists (li_addresses, li_bytes) in
      let endpoint = endpoint with state := state in
      let internal_state = internal_state with <| chp := (endpoint.write_back_bd_queue_id =+ chp) internal_state.chp;
                                                  ctp := (endpoint.write_back_bd_queue_id =+ ctp) internal_state.ctp;
                                                  endpoints_rx := (endpoint_id =+ endpoint) internal_state.endpoints_rx |> in
        (internal_state, li_address_bytes, tag, [])
)
End

(*	else if endpoint.state = write_back_sop_bd3 then														//Append SOP BD to non-empty tail, by indicating completion queue and lram info to write.
		(sop_bd, sop_bd_ras, sop_bd_was) ≔ FIND (\(bd, bd_ras, bd_was). HD bd_ras = endpoint.sop_bd_ra) bds_to_write_back
		(mr, bd_mr_index) ≔ bd_mr_info(HD sop_bd_was)
		li ≔ {next_bd_mr ≔ mr; next_bd_mr_index ≔ bd_mr_index; next_bd_size ≔ bd_address_to_internal_4lsb(HD sop_bd_was); EOQ ≔ 0}		//Linking information of previous tail SOP BD.
		internal_state.completion_queue_write_backs ≔ internal_state.completion_queue_write_backs ++ [(ctp[endpoint.write_back_bd_queue_id], li)]	//Append SOP BD to completion queue with ID sop_bd[2][7:0] and value li.
		endpoint.state ≔ fetch_bd																			//Fetch next BD.
		return (internal_state, [], 0, [])																	//No released BDs since BDs might be appended.
*)
Definition rx_write_back_sop_bd3:
(rx_write_back_sop_bd3 internal_state endpoint_id [] = (internal_state, [], tag, [])) /\
(rx_write_back_sop_bd3 internal_state endpoint_id (bd::bds) =
  let endpoint = internal_state.endpoints_rx endpoint_id in
    case FIND (\(bd, bd_ras, bd_was). HD bd_ras = endpoint.sop_bd_ra) (bd::bds) of
      NONE => (internal_state, [], tag, [])
    | SOME ((sop_bd, sop_li), sop_bd_ras, sop_bd_was) =>
      let (mr, bd_mr_index) = bd_mr_info internal_state.registers (HD sop_bd_was) in
      let li_bytes = form_li_bytes mr bd_mr_index (bd_address_to_internal_4lsb (HD sop_bd_was)) F in
      let endpoint = endpoint with state := rx_fetch_bd in
      let completion_queue_write_backs_extension = [(internal_state.ctp endpoint.write_back_bd_queue_id, li_bytes)] in
      let completion_queue_write_backs = internal_state.completion_queue_write_backs ++ completion_queue_write_backs_extension in
      let internal_state = internal_state with <| endpoints_rx := (endpoint_id =+ endpoint) internal_state.endpoints_rx;
                                                  completion_queue_write_backs := completion_queue_write_backs
                                                |> in
        (internal_state, [], tag, [])
)
End

(*	//Write back a BD due to another SOP BD being appended to this SOP BD of a
	//completion queue. Scheduler sets state = write_back_bd_append_sop4 and
	//saves previous state in previous_state.
	else if endpoint.state = write_back_sop_bd4 then
		li ≔ SND (FIND (\(a, li). EXISTS (\(bd, bd_ras, bd_was). HD bd_ras = a) bds_to_write_back) internal_state.completion_queue_write_backs)
		(sop_bd, sop_bd_ras, sop_bd_was) ≔ FIND (\(bd, bd_ras, bd_was). EXISTS (\(a, li). HD bd_ras = a) internal_state.completion_queue_write_backs) bds_to_write_back
		li_address ≔ LAST 4 sop_bd_was
		internal_state.completion_queue_write_backs ≔ FILTER (\(a, li). HD sop_bd_ras != a) internal_state.completion_queue_write_backs
		endpoint.state ≔ internal_state.previous_state
		return (internal_state, (li_address, li), 4, [(sop_bd, sop_bd_ras, sop_bd_was)])	//MEMORY WRITE: memory4[li_address] ≔ li. Release SOP BD written back due to following SOP BD being written back.
*)
Definition rx_write_back_sop_bd4:
(rx_write_back_sop_bd4 internal_state endpoint_id [] = (internal_state, [], tag, [])) /\
(rx_write_back_sop_bd4 internal_state endpoint_id (bd::bds) =
  let endpoint = internal_state.endpoints_rx endpoint_id in
    case FIND (\(a, li_bytes). EXISTS (\(bd, bd_ras, bd_was). HD bd_ras = a) (bd::bds)) internal_state.completion_queue_write_backs of
      NONE => (internal_state, [], tag, [])
    | SOME (a, li_bytes) =>
    case FIND (\(bd, bd_ras, bd_was). HD bd_ras = a) (bd::bds) of
    | NONE => (internal_state, [], tag, [])
    | SOME (sop_bd, sop_bd_ras, sop_bd_was) =>
      let li_addresses = DROP 32 sop_bd_was in
      let endpoint = endpoint with state := internal_state.endpoint_previous_state_rx in
      let completion_queue_write_backs = FILTER (\a_li. a_li <> (a, li_bytes)) internal_state.completion_queue_write_backs in
      let internal_state = internal_state with <| endpoints_rx := (endpoint_id =+ endpoint) internal_state.endpoints_rx;
                                                  completion_queue_write_backs := completion_queue_write_backs
                                                |> in
        (internal_state, merge_lists (li_addresses, li_bytes), tag, [(sop_bd, sop_bd_ras, sop_bd_was)])
)
End

(*	//Register reads popping last SOP BD in completion queues instruct the
	//scheduler to set endpoint state to write_back_sop_bd5 and store
	//previous state in previous_state. No write back is needed, only
	//releasing the BDs.
	else if endpoint.state = write_back_sop_bd5 then
		endpoint.state ≔ internal_state.previous_state
		(sop_bd, sop_bd_ras, sop_bd_was) ≔ FIND (\(bd, bd_ras, bd_was). EXISTS (\a. HD bd_ras = a) internal_state.write_back_popped_bds) bds_to_write_back
		internal_state.write_back_popped_bds ≔ FILTER (\a. HD sop_bd_ras != a) internal_state.write_back_popped_bds
		return (internal_state, [], 0, [(sop_bd, sop_bd_ras, sop_bd_was)])	//NO MEMORY WRITE. Released BDs.
*)
Definition rx_write_back_sop_bd5:
(rx_write_back_sop_bd5 internal_state endpoint_id [] = (internal_state, [], tag, [])) /\
(rx_write_back_sop_bd5 internal_state endpoint_id (bd::bds) =
  let endpoint = internal_state.endpoints_rx endpoint_id in
    case FIND (\(bd, bd_ras, bd_was). EXISTS (\a. HD bd_ras = a) internal_state.write_back_popped_bds) (bd::bds) of
    | NONE => (internal_state, [], tag, [])
    | SOME (sop_bd, sop_bd_ras, sop_bd_was) =>
      let endpoint = endpoint with state := internal_state.endpoint_previous_state_rx in
      let write_back_popped_bds = FILTER (\a. HD sop_bd_ras <> a) internal_state.write_back_popped_bds in
      let internal_state = internal_state with <| endpoints_rx := (endpoint_id =+ endpoint) internal_state.endpoints_rx;
                                                  write_back_popped_bds := write_back_popped_bds
                                                |> in
        (internal_state, [], tag, [(sop_bd, sop_bd_ras, sop_bd_was)])
)
End

Definition rx_write_back_bd:
rx_write_back_bd queue_id environment internal_state bds_to_write_back =
  let endpoint_id = internal_state.current_rx_endpoint_id in
  let endpoint = internal_state.endpoints_rx endpoint_id in
    if endpoint.state = rx_write_back_current_bd then
      rx_write_back_current_bd queue_id internal_state endpoint_id bds_to_write_back
    else if endpoint.state = rx_write_back_previous_bd then
      rx_write_back_previous_bd internal_state endpoint_id bds_to_write_back
    else if endpoint.state = rx_write_back_sop_bd1 then
      rx_write_back_sop_bd1 environment internal_state endpoint_id bds_to_write_back
    else if endpoint.state = rx_write_back_sop_bd2 then
      rx_write_back_sop_bd2 internal_state endpoint_id bds_to_write_back
    else if endpoint.state = rx_write_back_sop_bd3 then
      rx_write_back_sop_bd3 internal_state endpoint_id bds_to_write_back
    else if endpoint.state = rx_write_back_sop_bd4 then
      rx_write_back_sop_bd4 internal_state endpoint_id bds_to_write_back
    else if endpoint.state = rx_write_back_sop_bd5 then
      rx_write_back_sop_bd5 internal_state endpoint_id bds_to_write_back
    else
      (internal_state, [], tag, [])
End

Definition rx_update_bd:
rx_update_bd (internal_state : internal_state_type) bd_ras_was = (internal_state, [], tag, update_incomplete)
End

Definition rx_update_bd_addresses:
rx_update_bd_addresses internal_state bd_ras_was = []
End

Definition rx_bd_transfer_ras_was:
rx_bd_transfer_ras_was internal_state ((current_bd : num -> 32 word), li : 32 word) =
  let ras = [] in

  let start_buffer_address = buffer_pointer current_bd in
  let buffer_size = buffer_length current_bd in
  let was = generate_consecutive_addresses start_buffer_address (w2n buffer_size) in
    (ras, was)
End

Definition rx_write_back_bd_addresses:
rx_write_back_bd_addresses queue_id environment internal_state bds_to_write_back =
  let (internal_state, address_bytes, tag, released_bds) = rx_write_back_bd queue_id environment internal_state bds_to_write_back in
    MAP FST address_bytes
End

val _ = export_theory();
