open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory bbb_usb_txTheory bbb_usb_rxTheory;

val _ = new_theory "bbb_usb_scheduler";

(*
next_schedule_entry() ≝
	word_index ≔ scheduler_index >> 2	//4 entries per word.
	word ≔ WORD_[word_index]
	word_entry ≔ scheduler_index[1:0] << 3	//Entry bit offset.
	entry ≔ word[(word_entry + 7):word_entry]
	txrx ≔ entry[7]
	endpoint_id ≔ entry[4:0]
	return (txrx, endpoint_id)
*)
Definition next_schedule_entry:
next_schedule_entry internal_state =
  let word_index = w2w (internal_state.scheduler_index >> 2) : 6 word in
  let word = internal_state.registers.WORD word_index in
  let word_entry = w2n (((1 >< 0) internal_state.scheduler_index : 5 word) << 3) in
  let entry = (word_entry + 7 >< word_entry) word : 8 word in
  let txrx = if word_bit 7 entry then rx else tx in (* Zero means transmission, one means receptions. *)
  let endpoint_id = (4 >< 0) entry : 5 word in
    (txrx, endpoint_id)
End

(*
tx_dma_possible endpoint_id ≝
	txrx = tx ∧ TXGCR[endpoint_id][31] = 1 ∧ environment.CPPI_FIFO[endpoint_id].FIFO_full = 0
*)
Definition dma_possible_tx:
dma_possible_tx environment internal_state endpoint_id = (
  internal_state.current_endpoint_txrx = tx /\
  word_bit 31 (internal_state.registers.TXGCR endpoint_id) /\
  ~(environment.CPPI_FIFO_FULL endpoint_id)
)
End

(*
rx_dma_possible endpoint_id ≝
	txrx = rx ∧ RXGCR[endpoint_id][31] = 1 ∧ environment.CPPI_FIFO[endpoint_id].FIFO_empty = 0
*)
Definition dma_possible_rx:
dma_possible_rx environment internal_state endpoint_id = (
  internal_state.current_endpoint_txrx = rx /\
  word_bit 31 (internal_state.registers.RXGCR endpoint_id) /\
  ~(environment.CPPI_FIFO_EMPTY endpoint_id)
)
End


Definition current_operation_tx:
(current_operation_tx tx_fetch_bd = fetch_bd) /\
(current_operation_tx tx_transfer_data = transfer_data) /\
(current_operation_tx tx_write_back_sop_bd1 = write_back_bd) /\
(current_operation_tx tx_write_back_sop_bd2 = write_back_bd) /\
(current_operation_tx tx_write_back_sop_bd3 = write_back_bd) /\
(current_operation_tx tx_write_back_sop_bd4 = write_back_bd)
End

Definition current_operation_rx:
(current_operation_rx rx_fetch_bd = fetch_bd) /\
(current_operation_rx rx_transfer_data = transfer_data) /\
(current_operation_rx rx_write_back_bd_current_bd = write_back_bd) /\
(current_operation_rx rx_write_back_bd_previous_bd = write_back_bd) /\
(current_operation_rx rx_write_back_bd_sop_bd1 = write_back_bd) /\
(current_operation_rx rx_write_back_bd_sop_bd2 = write_back_bd) /\
(current_operation_rx rx_write_back_bd_sop_bd3 = write_back_bd) /\
(current_operation_rx rx_write_back_bd_sop_bd4 = write_back_bd) /\
(current_operation_rx rx_write_back_bd_sop_bd5 = write_back_bd)
End

Definition validate_queue_id:
  (validate_queue_id NONE = NONE) /\
  (validate_queue_id (SOME (internal_state, queue_id)) = if queue_id <=+ 91w then SOME (internal_state, queue_id) else NONE)
End

Definition endpoint_schedulable_tx:
endpoint_schedulable_tx environment internal_state (channels : ((num -> 32 word) # 32 word, 8, 32, 8) collected_channel_state_components_type) endpoint_id =
  let endpoint = internal_state.endpoints_tx endpoint_id in (* Check whether this endpoint is schedulable. *)
  let state = endpoint.state in
  let (pending_accesses, bds) = THE (channels endpoint.current_queue_id) in
  let fetching_bd_requests = pending_accesses.requests.fetching_bd in
  let fetching_bd_replies = pending_accesses.replies.fetching_bd in
  let new_queue_id = w2w environment.endpoint_tx_queue_id + (w2w endpoint_id)*2w + 32w : 8 word in (* Start working on a new queue. *)
  let offset = word_bit 0 new_queue_id in
  let internal_state_scheduled_queue_id =
    if state = tx_fetch_bd /\ endpoint.sop offset /\ IS_NONE fetching_bd_requests /\ IS_NONE fetching_bd_replies /\ internal_state.qhp new_queue_id <> 0w then
      (* Start working on a new queue and issue a BD to fetch request. *)
      let endpoint = endpoint with current_queue_id := new_queue_id in
      let internal_state = internal_state with endpoints_tx := (endpoint_id =+ endpoint) internal_state.endpoints_tx in
        SOME (internal_state, new_queue_id)
    else if state = tx_fetch_bd /\ IS_SOME fetching_bd_replies then
      (* Possible to process BD to fetch reply. *)
      SOME (internal_state, endpoint.current_queue_id)
    else if state = tx_transfer_data then
      SOME (internal_state, endpoint.current_queue_id)
    else if state = tx_write_back_sop_bd1 then
      SOME (internal_state, endpoint.current_queue_id)
    else if state = tx_write_back_sop_bd2 then
      SOME (internal_state, endpoint.current_queue_id)
(* These two cases are not handled here. *)
(*    else if state = tx_write_back_sop_bd3 then
      SOME (internal_state, endpoint.current_queue_id)
    else if state = tx_write_back_sop_bd4 then
      SOME (internal_state, endpoint.current_queue_id)*)
    else
      NONE
  in
    validate_queue_id internal_state_scheduled_queue_id
End

Definition endpoint_schedulable_rx:
endpoint_schedulable_rx environment internal_state (channels : ((num -> 32 word) # 32 word, 8, 32, 8) collected_channel_state_components_type) endpoint_id =
  let endpoint = internal_state.endpoints_rx endpoint_id in
  let state = endpoint.state in
  let (pending_accesses, bds) = THE (channels endpoint.current_queue_id) in
  let fetching_bd_requests = pending_accesses.requests.fetching_bd in
  let fetching_bd_replies = pending_accesses.replies.fetching_bd in
  let internal_state_scheduled_queue_id =
    if state = rx_fetch_bd /\ endpoint.bd_index = 0w (*SOP*) /\ IS_NONE fetching_bd_requests /\ IS_NONE fetching_bd_replies /\ LENGTH environment.new_usb_packet > 0 /\ internal_state.qhp endpoint.current_queue_id <> 0w then
      (* Start working on a new queue and issue a BD to fetch request. *)
      let endpoint = endpoint with usb_packet := environment.new_usb_packet in
      let internal_state = internal_state with endpoints_rx := (endpoint_id =+ endpoint) internal_state.endpoints_rx in
        SOME (internal_state, endpoint.current_queue_id)
    else if state = rx_fetch_bd /\ IS_SOME fetching_bd_replies then
      (* Possible to process BD to fetch reply. *)
      SOME (internal_state, endpoint.current_queue_id)
    else if state = rx_transfer_data then
      SOME (internal_state, endpoint.current_queue_id)
    else if state = rx_write_back_current_bd then
      SOME (internal_state, endpoint.current_queue_id)
    else if state = rx_write_back_previous_bd then
      SOME (internal_state, endpoint.previous_queue_id)
    else if state = rx_write_back_sop_bd1 then
      SOME (internal_state, endpoint.current_queue_id)
    else if state = rx_write_back_sop_bd2 then
      SOME (internal_state, endpoint.current_queue_id)
    else if state = rx_write_back_sop_bd3 then
      SOME (internal_state, endpoint.current_queue_id)
(* These two cases are not handled here. *)
(*    else if state = rx_write_back_sop_bd4 then
      SOME (internal_state, endpoint.current_queue_id)
    else if state = rx_write_back_sop_bd5 then
      SOME (internal_state, endpoint.current_queue_id)*)
    else
      NONE
  in
    validate_queue_id internal_state_scheduled_queue_id
End

Definition increment_scheduler:
increment_scheduler internal_state =
  if internal_state.scheduler_index = DMA_SCHED_CTRL_LAST_ENTRY internal_state.registers.DMA_SCHED_CTRL then
    internal_state with scheduler_index := 0w
  else
    internal_state with scheduler_index := internal_state.scheduler_index + 1w
End

Definition find_tx_rx_schedulable_endpoint:
find_tx_rx_schedulable_endpoint environment internal_state (channels : ((num -> 32 word) # 32 word, 8, 32, 8) collected_channel_state_components_type) number_of_iterations =
  if number_of_iterations = 0 then
    ((internal_state, 0w, fetch_bd), F) (* No schedulable endpoint. Cannot happen since device_scheduler does not schedule dma_channel in this case. *)
  else
    let (txrx, endpoint_id) = next_schedule_entry internal_state in
      case txrx of
        tx =>
        let internal_state_queue_id_option = endpoint_schedulable_tx environment internal_state channels endpoint_id in
          if IS_SOME internal_state_queue_id_option then
            let (internal_state, queue_id) = THE internal_state_queue_id_option in
              if dma_possible_tx environment internal_state endpoint_id then
                let operation = current_operation_tx (internal_state.endpoints_tx endpoint_id).state in
                  ((internal_state, queue_id, operation), T)
              else
                let internal_state = increment_scheduler internal_state in
                  find_tx_rx_schedulable_endpoint environment internal_state channels (number_of_iterations - 1)
          else
            let internal_state = increment_scheduler internal_state in
              find_tx_rx_schedulable_endpoint environment internal_state channels (number_of_iterations - 1)
      | rx =>
        let internal_state_queue_id_option = endpoint_schedulable_rx environment internal_state channels endpoint_id in
          if IS_SOME internal_state_queue_id_option then
            let (internal_state, queue_id) = THE internal_state_queue_id_option in
              if dma_possible_rx environment internal_state endpoint_id then
                let operation = current_operation_rx (internal_state.endpoints_rx endpoint_id).state in
                  ((internal_state, queue_id, operation), T)
              else
                let internal_state = increment_scheduler internal_state in
                  find_tx_rx_schedulable_endpoint environment internal_state channels (number_of_iterations - 1)
          else
            let internal_state = increment_scheduler internal_state in
              find_tx_rx_schedulable_endpoint environment internal_state channels (number_of_iterations - 1)
End

(*
-Scenario 1: Write back due to other BDs being written back.
	for channel_id being a tx channel
		bds_to_write_back ≔ (THE channels channel_id).queue.bds_to_write_back
		packet_bds ≔ get_dma_packets_bds(bds_to_write_back)
		if EXISTS (\(sop_bd, sop_bd_ras, sop_bd_was)::packet_bds. EXISTS (\(a, li). HD sop_bd_ras = a) internal_state.completion_queue_write_backs) packet_bds)	//BDs to write back.
			endpoint_id ≔ (channel_id - 32)/2
			endpoint ≔ internal_state.endpoint_tx endpoint_id
			endpoint.previous_state ≔ endpoint.state
			endpoint.state ≔ write_back_sop_bd3
			internal_state.endpoint_tx endpoint_id ≔ endpoint
			return (internal_state, SOME channel_id)
	return NONE
*)
Definition is_tx_sop_written_back:
is_tx_sop_written_back internal_state bds_to_write_back (channel_id : 8 word) =
  let packet_bds = get_dma_packets_bds bds_to_write_back in
  let packet_bds = FILTER (\bds. ~NULL bds) packet_bds in
  let sop_bds = MAP HD packet_bds in
    if EXISTS (\((sop_bd, sop_li), sop_bd_ras, sop_bd_was). EXISTS (\(a, li). HD sop_bd_ras = a) internal_state.completion_queue_write_backs) sop_bds then
      let endpoint_id = (w2w channel_id - 32w) >>> 1 in
      let endpoint = internal_state.endpoints_tx endpoint_id in
      let endpoint_previous_state_tx = endpoint.state in
      let endpoint = endpoint with state := tx_write_back_sop_bd3 in
      let internal_state = internal_state with <| endpoint_previous_state_tx := endpoint_previous_state_tx;
                                                  endpoints_tx := (endpoint_id =+ endpoint) internal_state.endpoints_tx |> in
        SOME (internal_state, channel_id, write_back_bd)
    else
      NONE
End

(*
-Scenario 2: Write back (release only) due to CPU emptying completion queue.
	for channel_id being a tx channel
		bds_to_write_back ≔ (THE channels channel_id).queue.bds_to_write_back
		packet_bds ≔ get_dma_packets_bds(bds_to_write_back)
		if EXISTS (\\(sop_bd, sop_bd_ras, sop_bd_was)::packet_bds. EXISTS (\a. HD sop_bd_ras = a) internal_state.write_back_popped_bds) packet_bds then
			endpoint_id ≔ (channel_id - 32)/2
			endpoint ≔ internal_state.endpoint_tx endpoint_id
			endpoint.previous_state ≔ endpoint.state
			endpoint.state ≔ write_back_sop_bd4
			internal_state.endpoint_tx endpoint_id ≔ endpoint
			return (internal_state, SOME channel_id)
	return NONE
*)
Definition is_tx_bd_popped:
is_tx_bd_popped internal_state bds_to_write_back (channel_id : 8 word) =
  let packet_bds = get_dma_packets_bds bds_to_write_back in
  let packet_bds = FILTER (\bds. ~NULL bds) packet_bds in
  let sop_bds = MAP HD packet_bds in
    if EXISTS (\((sop_bd, sop_li), sop_bd_ras, sop_bd_was). EXISTS (\a. HD sop_bd_ras = a) internal_state.write_back_popped_bds) sop_bds then
      let endpoint_id = (w2w channel_id - 32w) >>> 1 in
      let endpoint = internal_state.endpoints_tx endpoint_id in
      let endpoint_previous_state_tx = endpoint.state in
      let endpoint = endpoint with state := tx_write_back_sop_bd4 in
      let internal_state = internal_state with <| endpoint_previous_state_tx := endpoint_previous_state_tx;
                                                  endpoints_tx := (endpoint_id =+ endpoint) internal_state.endpoints_tx |> in
        SOME (internal_state, channel_id, write_back_bd)
    else
      NONE
End

val is_tx_write_back_tgoal = Hol_defn "is_tx_write_back" ‘
is_tx_write_back internal_state (channels : ((num -> 32 word) # 32 word, 8, 32, 8) collected_channel_state_components_type) (channel_id : 8 word) =
  if channel_id <+ 32w \/ 91w <+ channel_id then
    NONE
  else
    let (pending_accesses, (bds_to_update, bds_to_process, bds_to_write_back)) = THE (channels channel_id) in
    let is_sop_written_back = is_tx_sop_written_back internal_state bds_to_write_back channel_id in
    let is_bd_popped = is_tx_bd_popped internal_state bds_to_write_back channel_id in
      if IS_SOME is_sop_written_back then
        is_sop_written_back
      else if IS_SOME is_bd_popped then
        is_bd_popped
      else
        is_tx_write_back internal_state channels (channel_id - 1w)’

Definition MEASURE_CHANNEL_ID_IS_WRITE_BACK:
MEASURE_CHANNEL_ID_IS_WRITE_BACK (internal_state1, channels1, channel_id1) (internal_state2, channels2, channel_id2) =
  (channel_id1 <+ channel_id2)
End

Definition measure_channel_id_is_write_back:
measure_channel_id_is_write_back (internal_state, channels, channel_id) = w2n channel_id
End

Theorem WF_MEASURE_CHANNEL_ID_IS_WRITE_BACK_LEMMA:
WF (measure measure_channel_id_is_write_back)
Proof
REWRITE_TAC [prim_recTheory.WF_measure]
QED

Theorem GEQ_32_LEMMA:
!x : 8 word.
  32w <=+ x
  ==>
  x <> 0w
Proof
blastLib.BBLAST_TAC
QED

Theorem MEASURE_CHANNEL_ID_IS_WRITE_BACK_LEMMA:
MEASURE_CHANNEL_ID_IS_WRITE_BACK = measure measure_channel_id_is_write_back
Proof
REPEAT (fn (A, t) =>
 let val l = lhs t
     val r = rhs t in
 let val l_type = type_of l
     val r_type = type_of r
     val thm_type = ((type_of o #1 o dest_forall o concl) boolTheory.ETA_AX) in
 let val l_matching = match_type thm_type l_type
     val r_matching = match_type thm_type r_type in
 let val l_type_thm = INST_TYPE l_matching boolTheory.ETA_AX
     val r_type_thm = INST_TYPE r_matching boolTheory.ETA_AX in
 let val l_thm = SYM (SPEC l l_type_thm)
     val r_thm = SYM (SPEC r r_type_thm) in
   (ONCE_REWRITE_TAC [l_thm, r_thm] THEN ABS_TAC) (A, t)
 end end end end end) THEN
Cases_on ‘x’ THEN Cases_on ‘x'’ THEN Cases_on ‘r’ THEN Cases_on ‘r'’ THEN
ETAC prim_recTheory.measure_thm THEN
REWRITE_TAC [MEASURE_CHANNEL_ID_IS_WRITE_BACK, measure_channel_id_is_write_back] THEN
ETAC prim_recTheory.measure_thm THEN
ETAC prim_recTheory.measure_thm THEN
REWRITE_TAC [wordsTheory.WORD_LO]
QED

val (is_tx_write_back, is_tx_write_back_ind) = Defn.tprove (
(*Defn.tgoal*) is_tx_write_back_tgoal,
(fn (A, t) =>
  let val goal_type = (type_of o #1 o dest_exists) t in
  let val measure_type = type_of “MEASURE_CHANNEL_ID_IS_WRITE_BACK” in
  let val type_matching = match_type measure_type goal_type in
  let val type_r_measure_channel_id = inst type_matching “MEASURE_CHANNEL_ID_IS_WRITE_BACK”  in
    EXISTS_TAC type_r_measure_channel_id (A, t)
  end end end end) THEN
CONJS_TAC THENL
[
 REWRITE_TAC [MEASURE_CHANNEL_ID_IS_WRITE_BACK_LEMMA] THEN
 REWRITE_TAC [WF_MEASURE_CHANNEL_ID_IS_WRITE_BACK_LEMMA]
 ,
 INTRO_TAC THEN
 REWRITE_TAC [MEASURE_CHANNEL_ID_IS_WRITE_BACK] THEN
 ETAC boolTheory.DE_MORGAN_THM THEN
 ETAC wordsTheory.WORD_NOT_LOWER THEN
 IRTAC GEQ_32_LEMMA THEN
 IRTAC word_lemmasTheory.NEQ_ZERO_IMPLIES_PRE_LT_LEMMA THEN
 STAC
]
)

val is_tx_write_back = save_thm ("is_tx_write_back", is_tx_write_back)
val is_tx_write_back_ind = save_thm ("is_tx_write_back_ind", is_tx_write_back_ind)

(*
-Scenario 1: Write back due to other BDs being written back.
	for channel_id being a rx channel
		bds_to_write_back ≔ (THE channels channel_id).queue.bds_to_write_back
		if EXISTS (\(bd, bd_ras, bd_was). EXISTS (\(a, li). HD bd_ras = a) internal_state.completion_queue_write_backs) bds_to_write_back) then
			endpoint_id ≔ 0		//Any endpoint can be used since reception write backs from state write_back_sop_bd4 does not change any other state variables than endpoint.state which is restored.
			endpoint ≔ internal_state.endpoint_rx endpoint_id
			endpoint.previous_state ≔ endpoint.state
			endpoint.state ≔ write_back_sop_bd4
			internal_state.endpoint_rx endpoint_id ≔ endpoint
			return (internal_state, SOME channel_id)
	return NONE
*)
Definition is_rx_sop_written_back:
is_rx_sop_written_back internal_state bds_to_write_back (channel_id : 8 word) =
  if EXISTS (\((bd, li), bd_ras, bd_was). EXISTS (\(a, li). HD bd_ras = a) internal_state.completion_queue_write_backs) bds_to_write_back then
    let endpoint_id = 0w in
    let endpoint = internal_state.endpoints_rx endpoint_id in
    let endpoint_previous_state_rx = endpoint.state in
    let endpoint = endpoint with state := rx_write_back_sop_bd4 in
    let internal_state = internal_state with <| endpoint_previous_state_rx := endpoint_previous_state_rx;
                                                endpoints_rx := (endpoint_id =+ endpoint) internal_state.endpoints_rx
                                              |> in
      SOME (internal_state, channel_id, write_back_bd)
  else
    NONE
End

(*
-Scenario 2: Write back (release only) due to CPU emptying completion queue.
	for channel_id being a rx channel
		bds_to_write_back ≔ (THE channels channel_id).queue.bds_to_write_back
		if EXISTS (\(bd, bd_ras, bd_was). EXISTS (\a. HD bd_ras = a) internal_state.write_back_popped_bds) bds_to_write_back then
			endpoint_id ≔ 0		//Any endpoint can be used since reception write backs from state write_back_sop_bd5 does not change any other state variables than endpoint.state which is restored.
			endpoint ≔ internal_state.endpoint_rx endpoint_id
			endpoint.previous_state ≔ endpoint.state
			endpoint.state ≔ write_back_sop_bd5
			internal_state.endpoint_rx endpoint_id ≔ endpoint
			return (internal_state, SOME channel_id)
	return NONE
*)
Definition is_rx_bd_popped:
is_rx_bd_popped internal_state bds_to_write_back (channel_id : 8 word) =
  if EXISTS (\((bd, li), bd_ras, bd_was). EXISTS (\a. HD bd_ras = a) internal_state.write_back_popped_bds) bds_to_write_back then
    let endpoint_id = 0w in
    let endpoint = internal_state.endpoints_rx endpoint_id in
    let endpoint_previous_state_rx = endpoint.state in
    let endpoint = endpoint with state := rx_write_back_sop_bd5 in
    let internal_state = internal_state with <| endpoint_previous_state_rx := endpoint_previous_state_rx;
                                                endpoints_rx := (endpoint_id =+ endpoint) internal_state.endpoints_rx
                                              |> in
      SOME (internal_state, channel_id, write_back_bd)
  else
    NONE
End

val is_rx_write_back_tgoal = Hol_defn "is_tx_write_back" ‘
is_rx_write_back internal_state (channels : ((num -> 32 word) # 32 word, 8, 32, 8) collected_channel_state_components_type) (channel_id : 8 word) =
  if channel_id >=+ 32w then
    NONE
  else
    let (pending_accesses, (bds_to_update, bds_to_process, bds_to_write_back)) = THE (channels channel_id) in
    let is_sop_written_back = is_rx_sop_written_back internal_state bds_to_write_back channel_id in
    let is_bd_popped = is_rx_bd_popped internal_state bds_to_write_back channel_id in
      if IS_SOME is_sop_written_back then
        is_sop_written_back
      else if IS_SOME is_bd_popped then
        is_bd_popped
      else if channel_id <> 0w then
        is_rx_write_back internal_state channels (channel_id - 1w)
      else
        NONE’

val (is_rx_write_back, is_rx_write_back_ind) = Defn.tprove (
(*Defn.tgoal*) is_rx_write_back_tgoal,
(fn (A, t) =>
  let val goal_type = (type_of o #1 o dest_exists) t in
  let val measure_type = type_of “MEASURE_CHANNEL_ID_IS_WRITE_BACK” in
  let val type_matching = match_type measure_type goal_type in
  let val type_r_measure_channel_id = inst type_matching “MEASURE_CHANNEL_ID_IS_WRITE_BACK”  in
    EXISTS_TAC type_r_measure_channel_id (A, t)
  end end end end) THEN
CONJS_TAC THENL
[
 REWRITE_TAC [MEASURE_CHANNEL_ID_IS_WRITE_BACK_LEMMA] THEN
 REWRITE_TAC [WF_MEASURE_CHANNEL_ID_IS_WRITE_BACK_LEMMA]
 ,
 INTRO_TAC THEN
 REWRITE_TAC [MEASURE_CHANNEL_ID_IS_WRITE_BACK] THEN
 IRTAC word_lemmasTheory.NEQ_ZERO_IMPLIES_PRE_LT_LEMMA THEN
 STAC
]
)


val is_rx_write_back = save_thm ("is_rx_write_back", is_rx_write_back)
val is_rx_write_back_ind = save_thm ("is_rx_write_back_ind", is_rx_write_back_ind)

Definition find_schedulable_endpoint:
find_schedulable_endpoint environment (channels : ((num -> 32 word) # 32 word, 8, 32, 8) collected_channel_state_components_type) internal_state = (* 92 iterations is maximum. *)
  let tx_write_back = is_tx_write_back internal_state channels 91w in (* Transmission queues start from 91. *)
  let rx_write_back = is_rx_write_back internal_state channels 31w in (* Reception queues start from 31. *)
    if IS_SOME tx_write_back then
      (THE tx_write_back, T)
    else if IS_SOME rx_write_back then
      (THE rx_write_back, T)
    else
      find_tx_rx_schedulable_endpoint environment internal_state channels NUMBER_OF_QUEUES
End

Definition bbb_usb_dma_scheduler: (* Can update with received packet. *)
bbb_usb_dma_scheduler environment (function_state : 1 word option) internal_state ((channels, pending_register_memory_accesses) : ((num -> 32 word) # 32 word, 8, 32, 8) collected_dma_state_type) =
  FST (find_schedulable_endpoint environment channels internal_state)
End

(* Implements only USB DMA controller scheduling and no USB operations.
 *)
Definition bbb_usb_device_scheduler:
bbb_usb_device_scheduler environment (function_state : 1 word option) internal_state ((channels, (pending_register_related_memory_requests, pending_register_related_memory_replies)) : ((num -> 32 word) # 32 word, 8, 32, 8) collected_dma_state_type) =
  if ~NULL pending_register_related_memory_replies then
    dma_register_memory_access
  else if DMA_SCHED_CTRL_ENABLE internal_state.registers.DMA_SCHED_CTRL /\ environment.DMA_OPERATION /\ SND (find_schedulable_endpoint environment channels internal_state) then
    dma_operation
  else
    idle     
End

val _ = export_theory();
