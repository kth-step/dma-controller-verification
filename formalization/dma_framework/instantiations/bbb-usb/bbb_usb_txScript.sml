open HolKernel Parse boolLib bossLib;
open stateTheory bbb_usb_stateTheory bbb_usb_functionsTheory;

val _ = new_theory "bbb_usb_tx";

(*
tx_fetch_bd_addresses(queue_id, internal_state)
	endpoint_id ≔ (queue_id - 32)/2
	endpoint ≔ internal_state.endpoint_tx endpoint_id

	if endpoint.sop then
		sop_bd_addresses ≔ bd_aligned_address(qhp[queue_id])
		sop_li_addresses ≔ bd_address_to_li_address(qhp[queue_id])				//Get linking information of next SOP.
		addresses = sop_bd_addresses ++ sop_li_addresses						//Get BD and its associated linking RAM addresses.
		number_of_addresses ≔ 36
	else
		addresses = bd_aligned_address(qhp[queue_id])
		number_of_addresses ≔ 32

	return (addresses, number_of_addresses)										//Read request: 1 BD = 8*4 words = 8*4 bytes = 32 bytes (+ 4 bytes for LI).
*)
Definition tx_fetch_bd_addresses:
tx_fetch_bd_addresses queue_id internal_state =
  if internal_state.qhp queue_id = 0w then
    ([], tag)
  else
    (get_bd_ras internal_state.registers (internal_state.qhp queue_id), tag)
End

(*
tx_fetch_bd(queue_id, internal_state, fetched_bd) ≔							//State = fetch_bd
	endpoint_id ≔ (queue_id - 32)/2
	endpoint ≔ internal_state.endpoint_tx endpoint_id

	if endpoint.sop then
		endpoint.sop_li ≔ fetched_bd.li

	bd_ras ≔ bd_ras(qhp[queue_id], bd_address_to_li_address(qhp[queue_id]))		//Compute all read addresses of a BD based on the start addresses of the BD and its linking RAM entry.
	bd_was ≔ bd_ras

	if fetched_bd[5] = 0 then													//Next BD pointer indicates that fetched BD is last of DMA packet.
		endpoint.sop ≔ true														//Next BD is a SOP.

		if fetched_bd.sop_li.EOQ then												//Update head and tail pointers of queue.
			qhp[queue_id] ≔ 0
			qtp[queue_id] ≔ 0
		else
			qhp[queue_id] ≔ li_to_next_bd_address(endpoint.sop_li)
	else
		endpoint.sop ≔ false													//Next BD is not a SOP.
		qhp[queue_id] ≔ fetched_bd[5]											//Next BD pointer.

	//Initialization for memory accesses.
	endpoint.number_of_data_bytes_read ≔ 0
	endpoint.state ≔ transfer_data

	return (internal_state, (fetched_bd, bd_ras, bd_was))						//Fetched BD is returned.
*)
Definition tx_fetch_bd:
(tx_fetch_bd queue_id internal_state NONE = (internal_state, NONE)) /\
(tx_fetch_bd queue_id internal_state (SOME (fetched_bd_bytes : 8 word list, tag : 8 word)) =
  if internal_state.qhp queue_id = 0w then
    (internal_state, NONE)
  else
    let endpoint_id = w2w ((queue_id - 32w) >>> 1) in
    let endpoint = internal_state.endpoints_tx endpoint_id in  
    let (bd, li) = form_bd_li fetched_bd_bytes in
    let bd_ras = get_bd_ras internal_state.registers (internal_state.qhp queue_id) in
    let bd_was = bd_ras in
    let sop = (next_bd_pointer bd = 0w) in
    let offset = word_bit 0 queue_id in (* Each TX endpoint manages 2 channels; sop_li exists for two channels therefore, identified by LSB. *)
    let sop_li = if endpoint.sop offset then li else endpoint.sop_li offset in
    let qhp = if next_bd_pointer bd = 0w then (if li_to_eoq sop_li then 0w else li_to_next_bd_address internal_state.registers sop_li) else next_bd_pointer bd in
    let qtp = if next_bd_pointer bd = 0w then (if li_to_eoq sop_li then 0w else internal_state.qtp queue_id) else internal_state.qtp queue_id in
    let endpoint = endpoint with <| sop_li := (offset =+ sop_li) endpoint.sop_li; sop := (offset =+ sop) endpoint.sop; number_of_data_bytes_read := 0w; state := tx_transfer_data |> in
    let endpoints_tx = (endpoint_id =+ endpoint) internal_state.endpoints_tx in
    let internal_state = internal_state with <| endpoints_tx := endpoints_tx; qhp := (queue_id =+ qhp) internal_state.qhp; qtp := (queue_id =+ qtp) internal_state.qtp |> in
      (internal_state, SOME (((bd, li), bd_ras, bd_was), no_update)))
End

Definition received_bytes:
(received_bytes [] = 0) /\
(received_bytes ((bytes, tag)::replies) = (LENGTH bytes) + (received_bytes replies))
End

(*
tx_process_replies_generate_requests(queue_id, internal_state, current_bd, replies)					//state = transfer_data.
	endpoint_id ≔ (queue_id - 32)/2
	endpoint ≔ internal_state.endpoint_tx endpoint_id

	endpoint.number_of_data_bytes_read ≔ endpoint.number_of_data_bytes_read + (\(read_request bytes tag). LENGTH bytes) (HD replies))
	if endpoint.number_of_data_bytes_read < current_bd[3][21:0] then				//Not all bytes read.
		if endpoint.number_of_data_bytes_read + 64 < current_bd[3][21:0] then		//This is not the last memory read of the current bd.
			read_size ≔ 64															//Each memory request is 64 bytes.
		else																		//BD now processed.
			read_size ≔ current_bd[3][21:0] - endpoint.number_of_data_bytes_read

		read_addresses ≔ current_bd[4] + endpoint.number_of_data_bytes_read			//read_size bytes starting at address current_bd[4].
		return (internal_state, read_addresses, read_size, not_complete)			//MEMORY READ.
	else																			//All bytes read and all BDS of DMA packet can be written back and appended to the completion queue.
		if eop_bd current_bd then													//BDs of packet processed.
			endpoint.state ≔ write_back_sop_bd1
		else
			endpoint.state ≔ fetch_bd												//Process next BD.

		return (internal_state, [], 0, complete)
*)

(*
Definition largest_request_size_without_overflow_out_of_bounds_rec:
largest_request_size_without_overflow_out_of_bounds_rec number_of_accessed_bytes buffer_size request_size =
  if request_size = 0w then
    (* Cannot happen due to the check number_of_bytes_read <+ buffer_length bd. *)
    request_size
  else if number_of_accessed_bytes + request_size <+ number_of_accessed_bytes then
    (* Total number of bytes to access shall not overflow. Try smaller request size. *)
    largest_request_size_without_overflow_out_of_bounds_rec number_of_accessed_bytes buffer_size (request_size - 1w)
  else if number_of_accessed_bytes + request_size <=+ buffer_size then
    (* Largest request size not causing overflow nor above the buffer size. *)
    request_size
  else
    (* Above buffer size, try smaller request_size. *)
    largest_request_size_without_overflow_out_of_bounds_rec number_of_accessed_bytes buffer_size (request_size - 1w)
End

Definition largest_request_size_without_overflow_out_of_bounds:
largest_request_size_without_overflow_out_of_bounds number_of_accessed_bytes buffer_size =
largest_request_size_without_overflow_out_of_bounds_rec number_of_accessed_bytes buffer_size (64w : 32 word)
End

Definition get_request_size:
get_request_size number_of_read_bytes buffer_size =
  (* Get valid request byte size without overflow that can be compared to number of accessed bytes and buffer size. *)
  let request_size =
    if number_of_read_bytes + 64w <+ number_of_read_bytes then
      UINT_MAXw - number_of_read_bytes
    else
      64w
  in
    if number_of_read_bytes + request_size <=+ buffer_size then
      request_size
    else
      buffer_size - number_of_read_bytes
End
*)

Definition get_request_size:
get_request_size number_of_read_bytes buffer_size =
  (* Transform to naturals so that overflow does not need to be taken into consideration. *)
  if w2n number_of_read_bytes + 64 <= w2n buffer_size then
    64
  else
    w2n buffer_size - w2n number_of_read_bytes
End

Definition tx_process_replies_generate_requests:
tx_process_replies_generate_requests (queue_id : 8 word) internal_state (bd, li : 32 word) replies =
  let endpoint_id = w2w ((queue_id - 32w) >>> 1) in
  let endpoint = internal_state.endpoints_tx endpoint_id in
  let number_of_read_bytes = w2w (endpoint.number_of_data_bytes_read + (n2w (received_bytes replies))) in
    if number_of_read_bytes <+ buffer_length bd then
      let request_size = get_request_size number_of_read_bytes (buffer_length bd) in
      let start_address = (buffer_pointer bd) + number_of_read_bytes in
      let read_addresses = generate_consecutive_addresses start_address request_size in
      let read_request = request_read read_addresses tag in
      let endpoint = endpoint with number_of_data_bytes_read := (21 >< 0) number_of_read_bytes in
      let internal_state = internal_state with endpoints_tx := (endpoint_id =+ endpoint) internal_state.endpoints_tx in
        (internal_state, [read_request], F)
    else
      let endpoint = endpoint with state := if eop_bd bd then tx_write_back_sop_bd1 else tx_fetch_bd in
      let internal_state = internal_state with endpoints_tx := (endpoint_id =+ endpoint) internal_state.endpoints_tx in
        (internal_state, [], T)
End

(*
tx_write_back_bd(queue_id, internal_state, bds_to_release) ≔
	endpoint_id ≔ (queue_id - 32)/2
	endpoint ≔ internal_state.endpoint_tx endpoint_id

	(sop_bd, sop_bd_ras, sop_bd_was)::packet_bds = get_dma_packet_bds_to_release(internal_state, endpoint.state, bds_to_release)

	if endpoint.state = write_back_sop_bd1 then
		if ctp[sop_bd[2][7:0]] = 0 then												//Field is 12 bits, but 8 bits cover all 156 channels.	Append SOP BD to empty tail.
			chp[sop_bd[2][7:0]] ≔ HD sop_bd_ras
			endpoint.state ≔ fetch_bd												//Fetch next BD.
		else
			endpoint.state ≔ write_back_sop_bd2

		ctp[sop_bd[2][7:0]] ≔ HD sop_bd_ras
		li ≔ {next_bd_mr ≔ 0; next_bd_mr_index ≔ 0; next_bd_size ≔ 0; EOQ ≔ 1}	//Update linking information of the new tail SOP BD.
		li_address ≔ HD (LAST 4 sop_bd_ras)
		return (internal_state, (li_address, li), 4, []) 							//MEMORY WRITE: memory4[li_address] ≔ li. No released BDs since BDs might be appended.

	else if endpoint.state = write_back_sop_bd2 then								//Append SOP BD to non-empty tail, by indicating completion queue and lram info to write.
		(mr, bd_mr_index) ≔ bd_mr_info(HD sop_bd_ras)
		li ≔ {next_bd_mr ≔ mr; next_bd_mr_index ≔ bd_mr_index; next_bd_size ≔ bd_address_to_internal_4lsb(sop_bd_ras); EOQ ≔ 0}		//Linking information of previous tail SOP BD.
		internal_state.completion_queue_write_backs ≔ internal_state.completion_queue_write_backs ++ [(ctp[sop_bd[2][7:0]], li)]		//Append SOP BD to completion queue with address ctp[sop_bd[2][7:0]] and value li.
		endpoint.state ≔ fetch_bd													//Fetch next BD.
		return (internal_state, [], 0, [])											//No released BDs since BDs might be appended.

	//Write back a BD due to another SOP BD being appended to this SOP BD of a
	//completion queue. Scheduler sets state = write_back_sop_bd3 and saves
	//previous state in previous_state.
	else if endpoint.state = write_back_sop_bd3 then
		li_address ≔ HD (LAST 4 sop_bd_was)
		li ≔ SND (FIND (\(a, li). HD sop_bd_ras = a) internal_state.completion_queue_write_backs)
		internal_state.completion_queue_write_backs ≔ REMOVE (\(a, li). HD sop_bd_ras = a) internal_state.completion_queue_write_backs
		endpoint.state ≔ internal_state.previous_state
		return (internal_state, (li_address, li), 4, (sop_bd, sop_bd_ras, sop_bd_was)::packet_bds)	//MEMORY WRITE: memory4[li_address] ≔ li. Released BDs.

	//Register reads popping last SOP BD in completion queues instruct the
	//scheduler to set endpoint state to write_back_bd_append_sop4 and store
	//previous state in previous_state. No write back is needed, only
	//releasing the BDs.
	else if endpoint.state = write_back_bd_append_sop4 then
		endpoint.state ≔ internal_state.previous_state
		internal_state.write_back_popped_bds ≔ FILTER (\a. HD sop_bd_ras != a) internal_state.write_back_popped_bds
		return (internal_state, [], 0, (sop_bd, sop_bd_ras, sop_bd_was)::packet_bds)	//NO MEMORY WRITE. Released BDs.
*)
Definition tx_write_back_sop_bd1:
tx_write_back_sop_bd1 internal_state endpoint_id (sop_bd, sop_li) sop_bd_was =
  let endpoint = internal_state.endpoints_tx endpoint_id in
  let bd_ra = HD sop_bd_was in (* read and write addresses of BDs are identical. *)
  let completion_queue_id = tx_completion_queue_id sop_bd in
  let chp = if internal_state.ctp completion_queue_id = 0w then (completion_queue_id =+ bd_ra) internal_state.chp else internal_state.chp in
  let ctp = (completion_queue_id =+ bd_ra) internal_state.ctp in
  let endpoint = endpoint with state := if internal_state.ctp completion_queue_id = 0w then tx_fetch_bd else tx_write_back_sop_bd2 in
  let li_bytes = form_li_bytes 0 0w 0w T in
  let li_addresses = DROP 32 sop_bd_was in
  let internal_state = internal_state with <| endpoints_tx := (endpoint_id =+ endpoint) internal_state.endpoints_tx; chp := chp; ctp := ctp |> in
    (internal_state, merge_lists (li_addresses, li_bytes), tag, [])
End

Definition tx_write_back_sop_bd2:
tx_write_back_sop_bd2 internal_state endpoint_id (sop_bd, sop_li) sop_bd_was =
  let endpoint = internal_state.endpoints_tx endpoint_id in
  let endpoint = endpoint with state := tx_fetch_bd in
  let bd_ra = HD sop_bd_was in (* read and write addresses of BDs are identical. *)
  let (mr, bd_mr_index) = bd_mr_info internal_state.registers bd_ra in
  let li = form_li_bytes mr bd_mr_index (bd_address_to_internal_4lsb bd_ra) F in
  let completion_queue_id = tx_completion_queue_id sop_bd in
  let bd_to_release_address = internal_state.ctp completion_queue_id in
  let internal_state = internal_state with <| endpoints_tx := (endpoint_id =+ endpoint) internal_state.endpoints_tx;
                                              completion_queue_write_backs := internal_state.completion_queue_write_backs ++ [(bd_to_release_address, li)];
                                            |> in
    (internal_state, [], tag, [])
End

Definition tx_write_back_sop_bd3:
tx_write_back_sop_bd3 internal_state endpoint_id (sop_bd_li, sop_bd_ras, sop_bd_was) packet_bds =
  case FIND (\(a, li_bytes). HD sop_bd_ras = a) internal_state.completion_queue_write_backs of
    NONE => (internal_state, [], tag, [])
  | SOME (a, li_bytes) =>
    let li_addresses = DROP 32 sop_bd_was in
    let endpoint = internal_state.endpoints_tx endpoint_id in
    let endpoint = endpoint with state := internal_state.endpoint_previous_state_tx in
    let internal_state = internal_state with <| endpoints_tx := (endpoint_id =+ endpoint) internal_state.endpoints_tx;
                                                completion_queue_write_backs := FILTER (\(a : 32 word, li). HD sop_bd_ras <> a) internal_state.completion_queue_write_backs;
                                              |> in
      (internal_state, merge_lists (li_addresses, li_bytes), tag, (sop_bd_li, sop_bd_ras, sop_bd_was)::packet_bds)
End

Definition tx_write_back_sop_bd4:
tx_write_back_sop_bd4 internal_state endpoint_id (sop_bd, sop_bd_ras, sop_bd_was) packet_bds =
  let endpoint = internal_state.endpoints_tx endpoint_id in
  let endpoint = endpoint with state := internal_state.endpoint_previous_state_tx in
  let internal_state = internal_state with <| endpoints_tx := (endpoint_id =+ endpoint) internal_state.endpoints_tx;
                                              write_back_popped_bds := FILTER (\a : 32 word. HD sop_bd_ras <> a) internal_state.write_back_popped_bds;
                                            |> in
    (internal_state, [], tag, (sop_bd, sop_bd_ras, sop_bd_was)::packet_bds)
End

Definition tx_write_back_bd:
tx_write_back_bd (queue_id : 8 word) (environment : environment_type) internal_state bds_to_write_back =
  let endpoint_id = w2w ((queue_id - 32w) >>> 1) in
  let endpoint = internal_state.endpoints_tx endpoint_id in
    case get_dma_packet_bds_to_release internal_state endpoint.state bds_to_write_back of
    | NONE => (internal_state, [], tag, [])
    | SOME [] => (internal_state, [], tag, [])
    | SOME ((sop_bd_li : (num -> 32 word) # 32 word, sop_bd_ras, sop_bd_was)::packet_bds) => 
      if endpoint.state = tx_write_back_sop_bd1 then
        tx_write_back_sop_bd1 internal_state endpoint_id sop_bd_li sop_bd_was
      else if endpoint.state = tx_write_back_sop_bd2 then
        tx_write_back_sop_bd2 internal_state endpoint_id sop_bd_li sop_bd_was
      else if endpoint.state = tx_write_back_sop_bd3 then
        tx_write_back_sop_bd3 internal_state endpoint_id (sop_bd_li, sop_bd_ras, sop_bd_was) packet_bds
      else if endpoint.state = tx_write_back_sop_bd4 then
        tx_write_back_sop_bd4 internal_state endpoint_id (sop_bd_li, sop_bd_ras, sop_bd_was) packet_bds
      else
        (internal_state, [], tag, [])
End

(* Unimplemented. *)
Definition tx_update_bd:
tx_update_bd internal_state bd_ras_was = (internal_state, [], tag, update_incomplete)
End

Definition tx_update_bd_addresses:
tx_update_bd_addresses internal_state bds_to_update = []
End

Definition tx_bd_transfer_ras_was:
tx_bd_transfer_ras_was internal_state (bd : num -> 32 word, li : 32 word) =
  let buffer_start_address = buffer_pointer bd in
  let buffer_byte_size = w2n (buffer_length bd) in
  let buffer_read_addresses = generate_consecutive_addresses buffer_start_address buffer_byte_size in
  let ras = buffer_read_addresses in
  let was = [] in
    (ras, was)
End

Definition tx_write_back_bd_addresses:
tx_write_back_bd_addresses (queue_id : 8 word) environment internal_state bds_to_write_back =
  let (internal_state, address_bytes, tag, released_bds) = tx_write_back_bd queue_id environment internal_state bds_to_write_back in
    MAP FST address_bytes
End

val _ = export_theory();

