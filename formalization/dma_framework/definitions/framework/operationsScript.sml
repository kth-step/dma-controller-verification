open HolKernel Parse boolLib bossLib helper_tactics stateTheory;

val _ = new_theory "operations";

(* This file contains utility functions used in the definitions of the four
 * abstraction layers of DMA controllers.
 *)

(* Function for updating memory. *)
Definition update_memory:
  (update_memory memory [] = memory) /\
  (update_memory memory ((address, byte)::address_bytes) = update_memory ((address =+ byte) memory) address_bytes)
End

(* Obtains address_bytes to write to memory from requests. *)
Definition request_to_address_bytes:
  (request_to_address_bytes (request_read addresses tag) = []) /\
  (request_to_address_bytes (request_write address_bytes tag) = address_bytes)
End


(*Types and functions for updating DMA channel queues.**************************)

(* A datatype holding a BD queue of a DMA channel.
 *)
Datatype: queue_update_type =
  fetch_queue      ((('bd_address_width, 'bd_type) bds_to_fetch_entry_type) list)
| update_queue     ((('bd_address_width, 'bd_type) bd_ras_was_type) list)
| process_queue    ((('bd_address_width, 'bd_type) bd_ras_was_type) list)
| write_back_queue ((('bd_address_width, 'bd_type) bd_ras_was_type) list)
End

(* Updates a specific queue.
 *)
Definition update_q:
  (update_q old_qs (fetch_queue      new_q) = old_qs with bds_to_fetch      := new_q) ∧
  (update_q old_qs (update_queue     new_q) = old_qs with bds_to_update     := new_q) ∧
  (update_q old_qs (process_queue    new_q) = old_qs with bds_to_process    := new_q) ∧
  (update_q old_qs (write_back_queue new_q) = old_qs with bds_to_write_back := new_q)
End

(* Updates all queues in old_qs with the queues in new_qs.
 *)
Definition update_qs:
  update_qs old_qs new_qs = FOLDL update_q old_qs new_qs
End

(* Given a DMA channel state and a list of new queues, updates the queues with
 * respect to the given DMA channel state as specified by new_qs.
 *)
Definition update_channel_qs:
  update_channel_qs channel new_qs = channel with queue := update_qs channel.queue new_qs
End

(*End of types and functions for updating DMA channel queues.*******************)


(*Start of predicates describing relationships between input and output states of all channels.*)

Definition PRESERVED_CHANNELS:
PRESERVED_CHANNELS channels1 channels2 max_index =
  !index.
    index >+ max_index
    ==>
    channels2 index = channels1 index
End

Definition DEFINED_PRESERVED_CHANNELS:
DEFINED_PRESERVED_CHANNELS channels1 channels2 max_index = (
  (!index. index <=+ max_index ==> IS_SOME (channels2 index)                            ) /\
  (!index. index >+  max_index ==> IS_SOME (channels1 index) = IS_SOME (channels2 index))
)
End

(*End of predicates describing relationships between input and output states of all channels.*)






(* Start of theorems for termination proofs. *)

Definition MEASURE_CHANNEL_ID:
MEASURE_CHANNEL_ID i j = (i <+ j)
End

Definition measure_channel_id:
measure_channel_id i = w2n i
End

Theorem MEASURE_CHANNEL_ID_EQ_MEASURE_CHANNEL_ID_LEMMA:
MEASURE_CHANNEL_ID = measure measure_channel_id
Proof
REPEAT (fn (A, t) => (* Add arguments so MEASURE_CHANNEL_ID and measure can be expanded. *)
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
ETAC prim_recTheory.measure_thm THEN
Cases_on ‘x’ THEN Cases_on ‘x'’ THEN
REWRITE_TAC [MEASURE_CHANNEL_ID, measure_channel_id] THEN
REWRITE_TAC [wordsTheory.WORD_LO]
QED

Theorem INDEX_NEQ_ZERO_IMPLIES_MEASURE_CHANNEL_ID_LEMMA:
!i.
  i <> 0w
  ==>
  MEASURE_CHANNEL_ID (i - 1w) i
Proof
REPEAT CONJ_TAC THEN
 INTRO_TAC THEN
 IRTAC word_lemmasTheory.NEQ_ZERO_IMPLIES_PRE_LT_LEMMA THEN
 REWRITE_TAC [MEASURE_CHANNEL_ID] THEN
 STAC
QED

(* End of theorems for termination proofs.*)





(*Fetching BDs******************************************************************)

Definition fetching_bd_set_request:
  (fetching_bd_set_request channel addresses tag =
     channel with pending_accesses :=
       channel.pending_accesses with requests :=
         channel.pending_accesses.requests with fetching_bd := SOME (request_read addresses tag))
End

Definition fetching_bd_clear_reply:
  fetching_bd_clear_reply channel =
    channel with pending_accesses :=
      channel.pending_accesses with <|
        replies := channel.pending_accesses.replies with fetching_bd := NONE;
        requests := channel.pending_accesses.requests with fetching_bd := NONE
      |>
End

Definition append_bds_to_update:
  append_bds_to_update channel bd_ras_was = channel with queue := channel.queue with bds_to_update := channel.queue.bds_to_update ++ [bd_ras_was]
End

Definition append_bds_to_process:
  append_bds_to_process channel bd_ras_was = channel with queue := channel.queue with bds_to_process := channel.queue.bds_to_process ++ [bd_ras_was]
End

(*End of fetching BDs***********************************************************)






(*Updating BDs******************************************************************)

(* Updates the bds_to_update and bds_to_process queues after a update of a BD is
 * complete.
 *)
Definition updating_bd_update_qs:
  (updating_bd_update_qs update_incomplete channel bd_ras_was bd_ras_wass = channel) ∧
  (updating_bd_update_qs update_complete   channel bd_ras_was bd_ras_wass =
     update_channel_qs
       channel
       [update_queue bd_ras_wass;
        process_queue (channel.queue.bds_to_process ++ [bd_ras_was])])
End

(* Appends a request to the interconnect queue of the updating BD pending_accesses.
 *)
Definition updating_bd_append_request:
  (updating_bd_append_request channel [] tag = channel) ∧
  (updating_bd_append_request channel (address_byte::address_bytes) tag =
     channel with pending_accesses :=
       channel.pending_accesses with requests :=
         channel.pending_accesses.requests with updating_bd :=
           channel.pending_accesses.requests.updating_bd ++ [request_write (address_byte::address_bytes) tag])
End

(*End of updating BDs***********************************************************)







(*Transferring data*************************************************************)

(* Removes all pending replies of the transferring data pending_accesses. *)
Definition transferring_data_clear_replies:
  transferring_data_clear_replies channel =
    channel with pending_accesses :=
      channel.pending_accesses with replies := 
        channel.pending_accesses.replies with transferring_data := []
End

(* Gives all pending replies of the transferring data pending_accesses to the
 * instantiation and removes all pending replies.
 *)
Definition transferring_data_replies_requests:
  transferring_data_replies_requests replies process_replies_generate_requests internal_state channel bd =
  let (internal_state, new_requests, complete) = process_replies_generate_requests internal_state bd replies in
  let channel = transferring_data_clear_replies channel in
    (internal_state, channel, new_requests, complete)
End

(* Moves bd_ras_was to write back queue and sets the remaining BDs to update to
 * bd_ras_wass.
 *)
Definition transferring_data_update_qs:
  transferring_data_update_qs channel bd_ras_was bd_ras_wass =
    update_channel_qs
      channel
      [process_queue bd_ras_wass;
       write_back_queue (channel.queue.bds_to_write_back ++ [bd_ras_was])]
End

(* Appends request to the pending request queue of the transferring data
 * pending_accesses.
 *)
Definition transferring_data_append_requests:
  transferring_data_append_requests channel requests =
    channel with pending_accesses :=
      channel.pending_accesses with requests :=
        channel.pending_accesses.requests with transferring_data :=
          channel.pending_accesses.requests.transferring_data ++ requests
End

(*End of transferring data******************************************************)





(*Writing back BD***************************************************************)

(* Removes all released BDs (released_bd_ras_wass) from bds_to_write_back.
 *)
Definition writing_back_bd_remove_released_bds:
  writing_back_bd_remove_released_bds channel released_bd_ras_wass =
    update_channel_qs
      channel
      [write_back_queue (FILTER (\bd_ras_was. ~MEM bd_ras_was released_bd_ras_wass) channel.queue.bds_to_write_back)]
End

(* Appends a request to the interconnect queue of the writing back BD pending_accesses.
 *)
Definition writing_back_bd_append_request:
  (writing_back_bd_append_request channel [] tag = channel) ∧
  (writing_back_bd_append_request channel (address_byte::address_bytes) tag =
     channel with pending_accesses :=
       channel.pending_accesses with requests :=
         channel.pending_accesses.requests with writing_back_bd :=
           channel.pending_accesses.requests.writing_back_bd ++ [request_write (address_byte::address_bytes) tag])
End

(*End of writing back BD********************************************************)




























(*Pending requests**************************************************************)

Definition request_to_write_addresses:
  (request_to_write_addresses (request_read addresses tag) = []) /\
  (request_to_write_addresses (request_write address_bytes tag) = MAP FST address_bytes)
End

Definition collect_pending_fetch_bd_request:
(collect_pending_fetch_bd_request NONE = []) /\
(collect_pending_fetch_bd_request (SOME request) = [request])
End

(* Collects all pending requests of one DMA channel.
 *)
Definition collect_pending_requests:
collect_pending_requests channel_pending_accesses_requests =
  (collect_pending_fetch_bd_request channel_pending_accesses_requests.fetching_bd,
   channel_pending_accesses_requests.updating_bd,
   channel_pending_accesses_requests.transferring_data,
   channel_pending_accesses_requests.writing_back_bd)
End

Definition channel_pending_requests:
channel_pending_requests channel_pending_accesses_requests =
  (collect_pending_fetch_bd_request channel_pending_accesses_requests.fetching_bd) ++
  channel_pending_accesses_requests.updating_bd ++
  channel_pending_accesses_requests.transferring_data ++
  channel_pending_accesses_requests.writing_back_bd
End

val collect_pending_requests_channels_index_tgoal = Hol_defn "collect_pending_requests_channels_index" ‘
collect_pending_requests_channels_index channels i =
  let channel = THE (channels i) in
  let (frs, urs, trs, wrs) = collect_pending_requests channel.pending_accesses.requests in
    if i = 0w then
      (frs, urs, trs, wrs)
    else
      let (fetch_requests, update_requests, transfer_requests, write_back_requests) = collect_pending_requests_channels_index channels (i - 1w) in
        (fetch_requests ++ frs, update_requests ++ urs, transfer_requests ++ trs, write_back_requests ++ wrs)’

Definition MEASURE_CHANNEL_ID_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX:
(MEASURE_CHANNEL_ID_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX (channels1, channel_id1) (channels2, channel_id2) =
 MEASURE_CHANNEL_ID channel_id1 channel_id2)
End

Definition measure_channel_id_collect_pending_requests_channels_index:
(measure_channel_id_collect_pending_requests_channels_index (channels, channel_id) = measure_channel_id channel_id)
End

Theorem WF_MEASURE_CHANNEL_ID_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX_LEMMA:
WF (measure measure_channel_id_collect_pending_requests_channels_index)
Proof
REWRITE_TAC [prim_recTheory.WF_measure]
QED

Theorem MEASURE_CHANNEL_ID_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX_EQ_LEMMA:
MEASURE_CHANNEL_ID_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX = measure measure_channel_id_collect_pending_requests_channels_index
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
Cases_on ‘x’ THEN Cases_on ‘x'’ THEN
ETAC prim_recTheory.measure_thm THEN
REWRITE_TAC [MEASURE_CHANNEL_ID_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX, measure_channel_id_collect_pending_requests_channels_index] THEN
ETAC prim_recTheory.measure_thm THEN
AP_THM_TAC THEN
AP_THM_TAC THEN
REWRITE_TAC [MEASURE_CHANNEL_ID_EQ_MEASURE_CHANNEL_ID_LEMMA]
QED

val (collect_pending_requests_channels_index, collect_pending_requests_channels_index_ind) = Defn.tprove (
(*Defn.tgoal*) collect_pending_requests_channels_index_tgoal,
(fn (A, t) =>
  let val goal_type = (type_of o #1 o dest_exists) t in
  let val measure_type = type_of “MEASURE_CHANNEL_ID_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX” in
  let val type_matching = match_type measure_type goal_type in
  let val type_r_measure_channel_id = inst type_matching “MEASURE_CHANNEL_ID_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX”  in
    EXISTS_TAC type_r_measure_channel_id (A, t)
  end end end end) THEN
CONJ_TAC THENL
[
 REWRITE_TAC [MEASURE_CHANNEL_ID_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX_EQ_LEMMA] THEN
 REWRITE_TAC [WF_MEASURE_CHANNEL_ID_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX_LEMMA]
 ,
 REPEAT CONJ_TAC THEN
  INTRO_TAC THEN
  REWRITE_TAC [MEASURE_CHANNEL_ID_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX] THEN
  (fn (A, t) => let val asm_to_disch = valOf (List.find is_neg A) in UNDISCH_TAC asm_to_disch (A, t) end) THEN
  REWRITE_TAC [INDEX_NEQ_ZERO_IMPLIES_MEASURE_CHANNEL_ID_LEMMA]
]
)

val collect_pending_requests_channels_index = save_thm ("collect_pending_requests_channels_index", collect_pending_requests_channels_index)
val collect_pending_requests_channels_index_ind = save_thm ("collect_pending_requests_channels_index_ind", collect_pending_requests_channels_index_ind)

Definition channel_requests:
channel_requests device_characteristics device =
  let (fetch_requests, update_requests, transfer_requests, write_back_requests) = collect_pending_requests_channels_index device.dma_state.channels device_characteristics.dma_characteristics.max_index in
    fetch_requests ++ update_requests ++ transfer_requests ++ write_back_requests
End

(* Collects all pending requests of all DMA channels of the same kind, or the
 * empty list if the kind does is not implemented.
 *)
Definition dma_pending_requests:
dma_pending_requests device_characteristics device =
  (channel_requests device_characteristics device) ++ device.dma_state.pending_register_related_memory_requests
End

Definition dma_requests:
dma_requests device_characteristics device =
  let (fetch_requests, update_requests, transfer_requests, write_back_requests) = collect_pending_requests_channels_index device.dma_state.channels device_characteristics.dma_characteristics.max_index in
    transfer_requests
End
















(******************************************************************************)






(* True if and only if the given two requests match each other (same type, both
 * read or both write, and tag).
 *)
Definition request_serviced:
(request_serviced (_ , request_read  _ tag_reply) (request_read  _ tag_request) = (tag_reply = tag_request)) /\
(request_serviced (_ , request_read  _ _        ) (request_write _ _          ) = F) /\
(request_serviced (_ , request_write _ _        ) (request_read  _ _          ) = F) /\
(request_serviced (_ , request_write _ tag_reply) (request_write _ tag_request) = (tag_reply = tag_request))
End

(* Removes each pending request that matches the serviced request (normally each
 * request is unique, identified by its tag, and at most one request is removed.
 *)
Definition remove_pending_request:
remove_pending_request serviced_request pending_requests =
  FILTER (\pending_request. ~request_serviced serviced_request pending_request) pending_requests
End

Definition serviced_request_to_reply:
(serviced_request_to_reply (bytes, request_read addresses tag) = (bytes, tag)) /\
(serviced_request_to_reply (_    , _                         ) = ([]   , 0w ))
End

Definition fetching_bd_request_served:
(fetching_bd_request_served _                              NONE                                 = F) /\
(fetching_bd_request_served _                              (SOME (request_write _ _          )) = F) /\
(fetching_bd_request_served (_, request_read addresses_reply tag_reply) (SOME (request_read addresses_pending tag_pending)) = (addresses_reply = addresses_pending /\ tag_reply = tag_pending)) /\
(fetching_bd_request_served (_, request_write _ _        ) _                                    = F)
End

Definition append_reply_remove_request_fetching_bd:
append_reply_remove_request_fetching_bd serviced_request pending_accesses =
  if fetching_bd_request_served serviced_request pending_accesses.requests.fetching_bd then
    pending_accesses with <|
      requests := pending_accesses.requests with fetching_bd := NONE;
      replies := pending_accesses.replies with fetching_bd := SOME (serviced_request_to_reply serviced_request)
    |>
  else
    pending_accesses
End

Definition append_reply_remove_request_updating_bd:
append_reply_remove_request_updating_bd serviced_request pending_accesses =
  if EXISTS (request_serviced serviced_request) pending_accesses.requests.updating_bd then
    pending_accesses with requests :=
      pending_accesses.requests with updating_bd :=
        remove_pending_request serviced_request pending_accesses.requests.updating_bd
  else
    pending_accesses
End

Definition append_reply_remove_request_transferring_data:
append_reply_remove_request_transferring_data serviced_request pending_accesses =
  if EXISTS (request_serviced serviced_request) pending_accesses.requests.transferring_data then
    pending_accesses with <|
      requests := pending_accesses.requests with transferring_data := remove_pending_request serviced_request pending_accesses.requests.transferring_data;
      replies := pending_accesses.replies with transferring_data := pending_accesses.replies.transferring_data ++ [serviced_request_to_reply serviced_request]
    |>
  else
    pending_accesses
End

Definition append_reply_remove_request_writing_back_bd:
append_reply_remove_request_writing_back_bd serviced_request pending_accesses =
  if EXISTS (request_serviced serviced_request) pending_accesses.requests.writing_back_bd then
    pending_accesses with requests :=
      pending_accesses.requests with writing_back_bd :=
        remove_pending_request serviced_request pending_accesses.requests.writing_back_bd
  else
    pending_accesses
End

Definition append_reply_remove_request_operation:
(append_reply_remove_request_operation serviced_request pending_accesses fetch_bd =
 append_reply_remove_request_fetching_bd serviced_request pending_accesses) /\
(append_reply_remove_request_operation serviced_request pending_accesses update_bd =
 append_reply_remove_request_updating_bd serviced_request pending_accesses) /\
(append_reply_remove_request_operation serviced_request pending_accesses transfer_data =
 append_reply_remove_request_transferring_data serviced_request pending_accesses) /\
(append_reply_remove_request_operation serviced_request pending_accesses write_back_bd =
 append_reply_remove_request_writing_back_bd serviced_request pending_accesses)
End

(* Appends the serviced request if it matches a pending request.
 *)
Definition append_reply_remove_request_channel:
append_reply_remove_request_channel serviced_request channel =
  channel with pending_accesses :=
    FOLDL (append_reply_remove_request_operation serviced_request) channel.pending_accesses [fetch_bd; update_bd; transfer_data; write_back_bd]
End

(* Appends reply and removes the serviced request from the pending requests of
 * all DMA channels of a specific sort (read, write or copy).
 *)
val append_reply_remove_request_channels_index_tgoal = Hol_defn "append_reply_remove_request_channels_index" ‘
append_reply_remove_request_channels_index serviced_request channels i =
  let channel = THE (channels i) in
  let channel = append_reply_remove_request_channel serviced_request channel in
  let channels = (i =+ SOME channel) channels in
    if i = 0w then
      channels
    else
      append_reply_remove_request_channels_index serviced_request channels (i - 1w)’

Definition MEASURE_CHANNEL_ID_APPEND_REPLY_REMOVE_REQUEST_CHANNELS_INDEX:
MEASURE_CHANNEL_ID_APPEND_REPLY_REMOVE_REQUEST_CHANNELS_INDEX
(serviced_request1, channels1, channel_id1) (serviced_request2, channels2, channel_id2) = MEASURE_CHANNEL_ID channel_id1 channel_id2
End

Definition measure_channel_id_append_reply_remove_request_channels_index:
measure_channel_id_append_reply_remove_request_channels_index (serviced_request, channels, channel_id) = measure_channel_id channel_id
End

Theorem WF_MEASURE_CHANNEL_ID_APPEND_REPLY_REMOVE_REQUEST_CHANNELS_INDEX_LEMMA:
WF (measure measure_channel_id_append_reply_remove_request_channels_index)
Proof
REWRITE_TAC [prim_recTheory.WF_measure]
QED

Theorem MEASURE_CHANNEL_ID_APPEND_REPLY_REMOVE_REQUEST_CHANNELS_INDEX_EQ_LEMMA:
MEASURE_CHANNEL_ID_APPEND_REPLY_REMOVE_REQUEST_CHANNELS_INDEX = measure measure_channel_id_append_reply_remove_request_channels_index
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
ETAC prim_recTheory.measure_thm THEN
Cases_on ‘x’ THEN Cases_on ‘x'’ THEN Cases_on ‘r’ THEN Cases_on ‘r'’ THEN
REWRITE_TAC [MEASURE_CHANNEL_ID_APPEND_REPLY_REMOVE_REQUEST_CHANNELS_INDEX, measure_channel_id_append_reply_remove_request_channels_index] THEN
ETAC prim_recTheory.measure_thm THEN
REPEAT AP_THM_TAC THEN
REWRITE_TAC [MEASURE_CHANNEL_ID_EQ_MEASURE_CHANNEL_ID_LEMMA]
QED

val (append_reply_remove_request_channels_index, append_reply_remove_request_channels_index_ind) = Defn.tprove (
(*Defn.tgoal*) append_reply_remove_request_channels_index_tgoal,
(fn (A, t) =>
  let val goal_type = (type_of o #1 o dest_exists) t in
  let val measure_type = type_of “MEASURE_CHANNEL_ID_APPEND_REPLY_REMOVE_REQUEST_CHANNELS_INDEX” in
  let val type_matching = match_type measure_type goal_type in
  let val type_r_measure_channel_id = inst type_matching “MEASURE_CHANNEL_ID_APPEND_REPLY_REMOVE_REQUEST_CHANNELS_INDEX” in
    EXISTS_TAC type_r_measure_channel_id (A, t)
  end end end end) THEN
CONJ_TAC THENL
[
 REWRITE_TAC [MEASURE_CHANNEL_ID_APPEND_REPLY_REMOVE_REQUEST_CHANNELS_INDEX_EQ_LEMMA] THEN
 REWRITE_TAC [WF_MEASURE_CHANNEL_ID_APPEND_REPLY_REMOVE_REQUEST_CHANNELS_INDEX_LEMMA]
 ,
 REPEAT CONJ_TAC THEN
  INTRO_TAC THEN
  REWRITE_TAC [MEASURE_CHANNEL_ID_APPEND_REPLY_REMOVE_REQUEST_CHANNELS_INDEX] THEN
  (fn (A, t) => let val asm_to_disch = valOf (List.find is_neg A) in UNDISCH_TAC asm_to_disch (A, t) end) THEN
  REWRITE_TAC [INDEX_NEQ_ZERO_IMPLIES_MEASURE_CHANNEL_ID_LEMMA]
]
)

val append_reply_remove_request_channels_index = save_thm ("append_reply_remove_request_channels_index", append_reply_remove_request_channels_index)
val append_reply_remove_request_channels_index_ind = save_thm ("append_reply_remove_request_channels_index_ind", append_reply_remove_request_channels_index_ind)



(* Removes the serviced request from the pending requests of all DMA channels.
 *)
Definition append_reply_remove_request_channels:
append_reply_remove_request_channels channels max_index serviced_request =
  append_reply_remove_request_channels_index serviced_request channels max_index
End

(* Process memory replies to requests originating from dma register accesses
   made by the CPU. *)
Definition append_reply_remove_register_related_reply:
append_reply_remove_register_related_reply serviced_request pending_register_related_memory_requests pending_register_related_memory_replies =
  if EXISTS (request_serviced serviced_request) pending_register_related_memory_requests then
    (remove_pending_request serviced_request pending_register_related_memory_requests,
     pending_register_related_memory_replies ++ [serviced_request_to_reply serviced_request])
  else
    (pending_register_related_memory_requests,
     pending_register_related_memory_replies)
End

(* This function is used by the interconnect to notify the DMA controller of
 * which requests have now been satisfied, causing the DMA controller to remove
 * the corresponding pending request if the tags of the request and the reply
 * are equal, and add the read reply to the queue of the matching operation and
 * DMA channel. serviced_request has the forms:
 * -bytes # request_write address_bytes tag: Acknowledge a write. Bytes are ignored.
 * -bytes # request_read addresses tag: Reply to previous read.
 *)
Definition dma_request_served:
dma_request_served device_characteristics device serviced_request =
  let channels_updated = append_reply_remove_request_channels device.dma_state.channels device_characteristics.dma_characteristics.max_index serviced_request in
  let (pending_register_related_memory_requests, pending_register_related_memory_replies) =
      append_reply_remove_register_related_reply serviced_request device.dma_state.pending_register_related_memory_requests device.dma_state.pending_register_related_memory_replies in
    device with dma_state := device.dma_state with <| channels := channels_updated;
                                                      pending_register_related_memory_requests := pending_register_related_memory_requests;
                                                      pending_register_related_memory_replies := pending_register_related_memory_replies |>
End

Definition APPENDED_REPLY_REMOVED_REQUEST_CHANNEL:
APPENDED_REPLY_REMOVED_REQUEST_CHANNEL channel1 channel2 serviced_request = (
  channel2 = append_reply_remove_request_channel serviced_request channel1
)
End

Definition APPENDED_REPLY_REMOVED_REQUEST_INDEXED_CHANNEL:
APPENDED_REPLY_REMOVED_REQUEST_INDEXED_CHANNEL channel1 channel2 serviced_request channel_index max_index = (
  (channel_index <=+ max_index ==> APPENDED_REPLY_REMOVED_REQUEST_CHANNEL channel1 channel2 serviced_request) /\
  (channel_index >+ max_index ==> channel1 = channel2)
)
End

Definition APPENDED_REPLY_REMOVED_REQUEST_CHANNELS:
APPENDED_REPLY_REMOVED_REQUEST_CHANNELS channels1 channels2 serviced_request max_index =
!index channel1 channel2.
  channel1 = THE (channels1 index) /\
  channel2 = THE (channels2 index)
  ==>
  APPENDED_REPLY_REMOVED_REQUEST_INDEXED_CHANNEL channel1 channel2 serviced_request index max_index
End

Definition APPENDED_REPLY_REMOVED_REQUEST_INDEXED_OR_PRESERVED_CHANNELS:
APPENDED_REPLY_REMOVED_REQUEST_INDEXED_OR_PRESERVED_CHANNELS channels1 channels2 serviced_request max_channel_id = (
  channels2 = append_reply_remove_request_channels_index serviced_request channels1 max_channel_id
  ==>
  APPENDED_REPLY_REMOVED_REQUEST_CHANNELS channels1 channels2 serviced_request max_channel_id /\
  PRESERVED_CHANNELS channels1 channels2 max_channel_id /\
  DEFINED_PRESERVED_CHANNELS channels1 channels2 max_channel_id
)
End

(*End of pending requests*******************************************************)












(*Internal DMA channel operations**********************************************)

Definition channel_state_components:
channel_state_components channel =
  let pending_accesses = channel.pending_accesses in
  let bds_to_update = channel.queue.bds_to_update in
  let bds_to_process = channel.queue.bds_to_process in
  let bds_to_write_back = channel.queue.bds_to_write_back in
  let queues = (bds_to_update, bds_to_process, bds_to_write_back) in
    (pending_accesses, queues)
End

val collect_channel_state_components_index_tgoal = Hol_defn "collect_channel_state_components_index" ‘
collect_channel_state_components_index channels channels_state_components i =
  let channel = THE (channels i) in
  let state_components = channel_state_components channel in
  let channels_state_components = (i =+ SOME state_components) channels_state_components in
    if i = 0w then
      channels_state_components
    else
      collect_channel_state_components_index channels channels_state_components (i - 1w)’

Definition MEASURE_CHANNEL_ID_COLLECT_CHANNEL_STATE_COMPONENTS_INDEX:
MEASURE_CHANNEL_ID_COLLECT_CHANNEL_STATE_COMPONENTS_INDEX
  (channels1, channel_state_components1, channel_id1)
  (channels2, channel_state_components2, channel_id2) =
  MEASURE_CHANNEL_ID channel_id1 channel_id2
End

Definition measure_channel_id_collect_channel_state_components_index:
measure_channel_id_collect_channel_state_components_index (channels, channel_state_components, channel_id) = measure_channel_id channel_id
End

Theorem WF_MEASURE_CHANNEL_ID_COLLECT_CHANNEL_STATE_COMPONENTS_INDEX_LEMMA:
WF (measure measure_channel_id_collect_channel_state_components_index)
Proof
REWRITE_TAC [prim_recTheory.WF_measure]
QED

Theorem MEASURE_CHANNEL_ID_COLLECT_CHANNEL_STATE_COMPONENTS_INDEX_EQ_LEMMA:
MEASURE_CHANNEL_ID_COLLECT_CHANNEL_STATE_COMPONENTS_INDEX = measure measure_channel_id_collect_channel_state_components_index
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
REWRITE_TAC [MEASURE_CHANNEL_ID_COLLECT_CHANNEL_STATE_COMPONENTS_INDEX, measure_channel_id_collect_channel_state_components_index] THEN
ETAC prim_recTheory.measure_thm THEN
AP_THM_TAC THEN
AP_THM_TAC THEN
REWRITE_TAC [MEASURE_CHANNEL_ID_EQ_MEASURE_CHANNEL_ID_LEMMA]
QED

val (collect_channel_state_components_index, collect_channel_state_components_index_ind) = Defn.tprove (
(*Defn.tgoal*) collect_channel_state_components_index_tgoal,
(fn (A, t) =>
  let val goal_type = (type_of o #1 o dest_exists) t in
  let val measure_type = type_of “MEASURE_CHANNEL_ID_COLLECT_CHANNEL_STATE_COMPONENTS_INDEX” in
  let val type_matching = match_type measure_type goal_type in
  let val type_r_measure_channel_id = inst type_matching “MEASURE_CHANNEL_ID_COLLECT_CHANNEL_STATE_COMPONENTS_INDEX”  in
    EXISTS_TAC type_r_measure_channel_id (A, t)
  end end end end) THEN
CONJ_TAC THENL
[
 REWRITE_TAC [MEASURE_CHANNEL_ID_COLLECT_CHANNEL_STATE_COMPONENTS_INDEX_EQ_LEMMA] THEN
 REWRITE_TAC [WF_MEASURE_CHANNEL_ID_COLLECT_CHANNEL_STATE_COMPONENTS_INDEX_LEMMA]
 ,
 REPEAT CONJ_TAC THEN
  INTRO_TAC THEN
  REWRITE_TAC [MEASURE_CHANNEL_ID_COLLECT_CHANNEL_STATE_COMPONENTS_INDEX] THEN
  (fn (A, t) => let val asm_to_disch = valOf (List.find is_neg A) in UNDISCH_TAC asm_to_disch (A, t) end) THEN
  REWRITE_TAC [INDEX_NEQ_ZERO_IMPLIES_MEASURE_CHANNEL_ID_LEMMA]
]
)

val collect_channel_state_components_index = save_thm ("collect_channel_state_components_index", collect_channel_state_components_index)
val collect_channel_state_components_index_ind = save_thm ("collect_channel_state_components_index_ind", collect_channel_state_components_index_ind)

Definition collect_channels_state:
collect_channels_state dma_characteristics channels =
  let channels_none = \channel_id. NONE in
  let channels = collect_channel_state_components_index channels channels_none dma_characteristics.max_index in
    channels
End

Definition collect_dma_state:
collect_dma_state dma_characteristics dma_state =
  let channels = collect_channels_state dma_characteristics dma_state.channels in
  let pending_register_related_memory_requests = dma_state.pending_register_related_memory_requests in
  let pending_register_related_memory_replies = dma_state.pending_register_related_memory_replies in
  let pending_register_memory_accesses = (pending_register_related_memory_requests, pending_register_related_memory_replies) in
    (channels, pending_register_memory_accesses)
End

(* Updates the state of the DMA controller with the new internal state and the
 * channel identified by the last argument.
 *)
Definition update_device_state:
update_device_state device channel_id internal_state channel_state =
  device with dma_state := device.dma_state with <|
    internal_state := internal_state;
    channels := (channel_id =+ SOME channel_state) device.dma_state.channels
  |>
End

(* Input:
 * -device: The device (which consists of a non-DMA part and a DMA part).
 * -environment: Used by writing back BDs and the scheduler. Can be thought of as
 *  the back-end of the DMA controller interfacing an part of the device not
 *  being modeled (like the network of a NIC, or the storage of a disk), or
 *  aspects of the device not being specified (e.g. order of operations).
 * -channel_operation: Describes an operation of a specific layer. May have a
 *  last argument of memory.
 *)
Definition internal_dma_operation:
internal_dma_operation device_characteristics channel_operation memory environment device1 =
  let scheduler                                            = device_characteristics.dma_characteristics.scheduler in
  let function_state                                       = device1.function_state in
  let internal_state_pre_scheduling                        = device1.dma_state.internal_state in
  let (pipelines, pending_register_memory_accesses)        = collect_dma_state device_characteristics.dma_characteristics device1.dma_state in
                                                             (* collected_dma_state ensures scheduler does not access abstract bds; for bisimulation. *)
  let (internal_state1, channel_id, dma_channel_operation) = scheduler environment function_state internal_state_pre_scheduling (pipelines, pending_register_memory_accesses) in
  let channel1                                             = schannel device1 channel_id in
  let (internal_state2, channel2)                          = channel_operation device_characteristics channel_id dma_channel_operation memory environment internal_state1 channel1 in
  let device2                                              = update_device_state device1 channel_id internal_state2 channel2 in
    device2
End

Definition scheduler_operation:
scheduler_operation device_characteristics device1 environment =
  let scheduler                                            = device_characteristics.dma_characteristics.scheduler in
  let function_state                                       = device1.function_state in
  let internal_state1                                      = device1.dma_state.internal_state in
  let (pipelines, pending_register_memory_accesses)        = collect_dma_state device_characteristics.dma_characteristics device1.dma_state in
  let (internal_state2, channel_id, dma_channel_operation) = scheduler environment function_state internal_state1 (pipelines, pending_register_memory_accesses) in
  let device2 = device1 with dma_state := device1.dma_state with internal_state := internal_state2 in
    (device2, channel_id, dma_channel_operation)
End

Definition dma_operation:
dma_operation device_characteristics channel_operation memory environment (device1, channel_id, dma_channel_operation) =
  let internal_state1             = device1.dma_state.internal_state in
  let channel1                    = schannel device1 channel_id in
  let (internal_state2, channel2) = channel_operation device_characteristics channel_id dma_channel_operation memory environment internal_state1 channel1 in
  let device2                     = update_device_state device1 channel_id internal_state2 channel2 in
    device2
End

(* Equivalent to internal_dma_operation.
 *)
Definition scheduler_dma_operation:
scheduler_dma_operation device_characteristics channel_operation memory environment device1 =
  let device_channel_id_operation = scheduler_operation device_characteristics device1 environment in
  let device2 = dma_operation device_characteristics channel_operation memory environment device_channel_id_operation in
    device2
End

(* Predicate used to abstract away all equalities resulting from unfolding
 * internal_dma_operation and which occur in all proofs of many functions
 * applied as a result of applying internal_dma_operation.
 *)
Definition INTERNAL_DMA_OPERATION:
INTERNAL_DMA_OPERATION
  device_characteristics environment device1 internal_state_pre_scheduling
  internal_state1 channel1 function_state scheduler pipelines
  pending_register_memory_accesses channel_id dma_channel_operation =
(
    scheduler = device_characteristics.dma_characteristics.scheduler /\
    function_state = device1.function_state /\
    internal_state_pre_scheduling = device1.dma_state.internal_state /\
    (pipelines, pending_register_memory_accesses) = collect_dma_state device_characteristics.dma_characteristics device1.dma_state /\
    (internal_state1, channel_id, dma_channel_operation) = scheduler environment function_state internal_state_pre_scheduling (pipelines, pending_register_memory_accesses) /\
    channel1 = schannel device1 channel_id
)
End

Definition internal_function_operation:
internal_function_operation function_characteristics environment device =
  let function_state1 = THE device.function_state in
  let function_state2 = function_characteristics.function_operation environment function_state1 in
    device with function_state := SOME function_state2
End

(* Applies the parameterized DMA function processing memory request replies to
 * requests from DMA register accesses made by the CPU.
 *)
Definition process_register_related_memory_access:
process_register_related_memory_access dma_characteristics device =
  let internal_state = device.dma_state.internal_state in
  let pending_memory_requests = device.dma_state.pending_register_related_memory_requests in (* Giving pending memory requests to the parameterized processing function allows it to see which writes have taken effect. *)
  let pending_memory_replies = device.dma_state.pending_register_related_memory_replies in
  let (internal_state, completed_pending_memory_replies) = dma_characteristics.process_register_related_memory_replies internal_state pending_memory_requests pending_memory_replies in
    device with dma_state := device.dma_state with <| internal_state := internal_state;
                                                      pending_register_related_memory_replies := FILTER (\reply. ~MEM reply completed_pending_memory_replies) pending_memory_replies |>
End

(* Describes an internal operation of the device, including both the functional
 * and DMA parts. Note that the functional part of the device cannot affect the
 * DMA part of the device, including both the internal DMA state and the DMA
 * channels.
 *
 * @channel_operation: Function describing how a DMA channel operates (one for
 *  each layer).
 * @environment: E.g. data input to network interface controller.
 *)
Definition internal_device_operation:
internal_device_operation device_characteristics channel_operation memory environment device =
  let function_state = device.function_state in
  let internal_state = device.dma_state.internal_state in
  let collected_dma_state = collect_dma_state device_characteristics.dma_characteristics device.dma_state in
  (* collected_dma_state ensures scheduler does not access abstract bds; for bisimulation. *)
  case device_characteristics.device_scheduler environment function_state internal_state collected_dma_state of
    function => internal_function_operation (THE device_characteristics.function_characteristics) environment device
  | dma_register_memory_access => process_register_related_memory_access device_characteristics.dma_characteristics device
  | dma_operation => internal_dma_operation device_characteristics channel_operation memory environment device
  | idle => device
End

(*End of Internal DMA channel operations***************************************)

























(*Register reads****************************************************************)

(* @is_valid: True if and only if a given memory request satisfies a certain
 *  condition. Used by layer 1 to restrict memory accesses which may be created
 *  due to the CPU accesseing registers (e.g. for the USB DMA controller on
 *  BeagleBone Black, register accesses causes memory accesses to linking RAM in
 *  memory where information about BDs are stored).
 *)
Definition dma_register_read:
dma_register_read device_characteristics is_valid device addresses =
  let pending_requests                           = device.dma_state.pending_register_related_memory_requests in
  let (internal_state, read_bytes, new_requests) = device_characteristics.dma_characteristics.register_read device.dma_state.internal_state addresses in
  let requests                                   = FILTER is_valid new_requests in
  let read_requests                              = FILTER READ_REQUEST requests in
  let write_requests                             = FILTER WRITE_REQUEST requests in
  let dma_address_bytes                          = FLAT (MAP request_to_address_bytes write_requests) in
  let device                                     = device with dma_state := device.dma_state with <| internal_state := internal_state;
                                                                                                     pending_register_related_memory_requests := pending_requests ++ read_requests |> in
      (device, dma_address_bytes, read_bytes)
End

Definition function_register_read:
function_register_read device_characteristics device addresses =
  let (function_state, read_bytes) = (THE device_characteristics.function_characteristics).function_register_read (THE device.function_state) addresses in
    (device with function_state := SOME function_state, [], read_bytes)
End

Definition device_register_read:
device_register_read (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type) is_valid device addresses =
  if EVERY device_characteristics.dma_characteristics.DMA_REGISTER_ADDRESSES addresses then
    dma_register_read device_characteristics is_valid device addresses
  else if IS_SOME device_characteristics.function_characteristics then
    if EVERY (THE device_characteristics.function_characteristics).FUNCTION_REGISTER_ADDRESSES addresses then
      function_register_read device_characteristics device addresses
    else
      (device, [], [] : 8 word list)
  else
    (device, [], [])
End

(*End of register reads*********************************************************)




(*******************************************************************************)
(*Register writes***************************************************************)
(*******************************************************************************)

(*BD appends********************************************************************)

(* Appends BDs to the queue of BDs to fetch of channel1 if and only if the
 * concrete queue in the post-state (memory2, internal_state2) is an extension
 * of the abstract queue in the pre-state channel1, where the post-state
 * results from the pre-state by either writing to external memory or to a DMA
 * register.
 *)
Definition append_bds_channel:
  append_bds_channel channel bds_to_fetch =
  let q1 = channel.queue.bds_to_fetch in
  let q2 = bds_to_fetch in
  if ∃bds_to_append. q1 ++ bds_to_append = q2 then
    channel with queue := channel.queue with bds_to_fetch := q2
  else
    channel
End

(* Appends BDs to the channels in channels.
 *)
val append_bds_channels_index_tgoal = Hol_defn "append_bds_channels_index" ‘
(append_bds_channels_index dma_characteristics memory channels internal_state i =
  let bds_to_fetch = (THE (dma_characteristics.verification i)).bds_to_fetch memory internal_state in
  let channel      = THE (channels i) in
  let channel      = append_bds_channel channel bds_to_fetch in
  let channels     = (i =+ SOME channel) channels in
  if i = 0w then
    channels
  else
    append_bds_channels_index dma_characteristics memory channels internal_state (i - 1w))’

Definition MEASURE_CHANNEL_ID_APPEND_BDS_CHANNELS_INDEX:
MEASURE_CHANNEL_ID_APPEND_BDS_CHANNELS_INDEX
  (dma_characteristics1, memory1, channels1, internal_state1, channel_id1)
  (dma_characteristics2, memory2, channels2, internal_state2, channel_id2) =
   MEASURE_CHANNEL_ID channel_id1 channel_id2
End

Definition measure_channel_id_append_bds_channels_index:
measure_channel_id_append_bds_channels_index (dma_characteristics, memory, channels, internal_state, channel_id) =
  measure_channel_id channel_id
End

Theorem WF_MEASURE_CHANNEL_ID_APPEND_BDS_CHANNELS_INDEX_LEMMA:
WF (measure measure_channel_id_append_bds_channels_index)
Proof
REWRITE_TAC [prim_recTheory.WF_measure]
QED

Theorem MEASURE_CHANNEL_ID_APPEND_BDS_CHANNELS_INDEX_EQ_LEMMA:
MEASURE_CHANNEL_ID_APPEND_BDS_CHANNELS_INDEX = measure measure_channel_id_append_bds_channels_index
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
Cases_on ‘x’ THEN Cases_on ‘x'’ THEN Cases_on ‘r’ THEN Cases_on ‘r'’ THEN Cases_on ‘r’ THEN Cases_on ‘r''’ THEN Cases_on ‘r’ THEN Cases_on ‘r'’ THEN
ETAC prim_recTheory.measure_thm THEN
REWRITE_TAC [MEASURE_CHANNEL_ID_APPEND_BDS_CHANNELS_INDEX, measure_channel_id_append_bds_channels_index] THEN
ETAC prim_recTheory.measure_thm THEN
AP_THM_TAC THEN
AP_THM_TAC THEN
REWRITE_TAC [MEASURE_CHANNEL_ID_EQ_MEASURE_CHANNEL_ID_LEMMA]
QED

val (append_bds_channels_index, append_bds_channels_index_ind) = Defn.tprove (
(*Defn.tgoal*) append_bds_channels_index_tgoal,
(fn (A, t) =>
  let val goal_type = (type_of o #1 o dest_exists) t in
  let val measure_type = type_of “MEASURE_CHANNEL_ID_APPEND_BDS_CHANNELS_INDEX” in
  let val type_matching = match_type measure_type goal_type in
  let val type_r_measure_channel_id = inst type_matching “MEASURE_CHANNEL_ID_APPEND_BDS_CHANNELS_INDEX”  in
    EXISTS_TAC type_r_measure_channel_id (A, t)
  end end end end) THEN
CONJ_TAC THENL
[
 REWRITE_TAC [MEASURE_CHANNEL_ID_APPEND_BDS_CHANNELS_INDEX_EQ_LEMMA] THEN
 REWRITE_TAC [WF_MEASURE_CHANNEL_ID_APPEND_BDS_CHANNELS_INDEX_LEMMA]
 ,
 REPEAT CONJ_TAC THEN
  INTRO_TAC THEN
  REWRITE_TAC [MEASURE_CHANNEL_ID_APPEND_BDS_CHANNELS_INDEX] THEN
  (fn (A, t) => let val asm_to_disch = valOf (List.find is_neg A) in UNDISCH_TAC asm_to_disch (A, t) end) THEN
  REWRITE_TAC [INDEX_NEQ_ZERO_IMPLIES_MEASURE_CHANNEL_ID_LEMMA]
]
)

val append_bds_channels_index = save_thm ("append_bds_channels_index", append_bds_channels_index)
val append_bds_channels_index_ind = save_thm ("append_bds_channels_index_ind", append_bds_channels_index_ind)

(* Appends BDs to channels if not NONE, given the internal state and the memory.
 *)
Definition append_bds_channels:
  append_bds_channels dma_characteristics memory channels internal_state =
  append_bds_channels_index dma_characteristics memory channels internal_state dma_characteristics.max_index
End

(* Append BDs:
 * -BBB NIC: Write next descriptor pointer of last BD. Not fixed address since
 *  the address depends on the address of the currently last BD. Does not depend
 *  on the channel.
 * -INTEL NIC: Write tail pointer. Fixed address since tha tail pointer register
 *  has a fixed address. Depends on channel.
 *
 * Hence, there are a number of cases to consider when BDs are appended:
 * -internal vs external: internal register vs internal memory vs external memory.
 * -channel vs general: written location is hardwired to a specific channel (e.g.
 *  HDP[x] for DMA channel x on INTEL NIC), or not (CPPI_RAM on BBB NIC).
 *
 * The desired behavior is that BDs can only be appended to the abstract queue of
 * BDs to fetch, not modified or removed. The queue of BDs to fetch is updated
 * only if the write causes the bds_to_fetch queue to expand/be unchanged. The
 * DMA channel queues to update are identified by traversing all channels and
 * identifying those who are expanded.
 *
 * This function is intended to be applied on the pre- and post-states
 * (controller1; and (memory2, internal_state2), respectively, where
 * internal_state2 is NONE if the append of BDs is via a write to external
 * memory as opposed to a DMA register or internal memory write) resulting from
 * a register or memory write that causes BDs to be appended to a queue of BDs
 * to fetch. The pre- and post-states are needed to determine whether the queues
 * to fetch are expanded or not.
 *
 * Writes appending BDs with a concrete queue correspond to the same write with
 * a abstract queue immediately followed by an application of this function.
 *
 * A write that causes an append of BDs, can only affect the internal state or
 * the external memory.
 *)

(* Append BDs via write to external memory, where memory is the written memory.
 *)
Definition dma_append_external_abstract_bds:
dma_append_external_abstract_bds device_characteristics memory device =
  device with dma_state :=
    device.dma_state with channels :=
      append_bds_channels device_characteristics.dma_characteristics memory device.dma_state.channels device.dma_state.internal_state
End

(* Append BDs via write to an internal register or to internal memory, where
 * device.internal reflects the register write that caused the append of
 * BDs. If the memory argument is NONE, then the register write is considered to
 * not cause an append of BDs, since memory is a required argument to
 * bds_to_fetch.
 *)
Definition dma_append_internal_abstract_bds:
(dma_append_internal_abstract_bds device_characteristics NONE          device = device) /\
(dma_append_internal_abstract_bds device_characteristics (SOME memory) device =
 dma_append_external_abstract_bds device_characteristics memory device)
End

Definition EXTENDED_BDS:
EXTENDED_BDS channel1 abstract_bds = (
  ?appended_bds. abstract_bds = channel1.queue.bds_to_fetch ++ appended_bds
)
End

Definition APPENDED_BDS:
APPENDED_BDS channel1 channel2 abstract_bds = (
  channel2 = channel1 with queue := channel1.queue with bds_to_fetch := abstract_bds
)
End

Definition EXTENDED_ABSTRACT_BDS_TO_FETCH:
EXTENDED_ABSTRACT_BDS_TO_FETCH channel1 channel2 abstract_bds = (
  EXTENDED_BDS channel1 abstract_bds /\
  APPENDED_BDS channel1 channel2 abstract_bds
)
End

Definition NOT_EXTENDED_ABSTRACT_BDS_TO_FETCH_AND_UNCHANGED_CHANNEL:
NOT_EXTENDED_ABSTRACT_BDS_TO_FETCH_AND_UNCHANGED_CHANNEL channel1 channel2 abstract_bds = (
  ~EXTENDED_BDS channel1 abstract_bds /\
  channel2 = channel1
)
End

Definition EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL:
EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL channel1 channel2 abstract_bds = (
  EXTENDED_ABSTRACT_BDS_TO_FETCH channel1 channel2 abstract_bds \/
  NOT_EXTENDED_ABSTRACT_BDS_TO_FETCH_AND_UNCHANGED_CHANNEL channel1 channel2 abstract_bds
)
End

Definition EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS:
EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS device_characteristics memory internal_state channels1 channels2 max_index =
!index channel1 channel2 bds_to_fetch.
  index <=+ max_index /\
  channel1 = THE (channels1 index) /\
  channel2 = THE (channels2 index) /\
  bds_to_fetch = (cverification device_characteristics index).bds_to_fetch memory internal_state
  ==>
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL channel1 channel2 bds_to_fetch
End

Definition APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS:
APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width,
                           'internal_state_type, 'tag_width) device_characteristics_type )
memory
(channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
(channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
internal_state max_channel_id = (
  channels2 = append_bds_channels_index device_characteristics.dma_characteristics memory channels1 internal_state max_channel_id
  ==>
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS device_characteristics memory internal_state channels1 channels2 max_channel_id /\
  PRESERVED_CHANNELS channels1 channels2 max_channel_id /\
  DEFINED_PRESERVED_CHANNELS channels1 channels2 max_channel_id
)
End

(*End of BD appends*************************************************************)




Definition update_memory_option:
(update_memory_option NONE _ = NONE) /\
(update_memory_option (SOME memory1) address_bytes = SOME (update_memory memory1 address_bytes))
End

(* Only writes affecting the queues as allowed need to be intercepted:
 * -Adding BDs: start and append, where append is managed separately since it may
 *  depend on writes to external memory. Hence, starts of channels must be
 *  intercepted.
 * -removing BDs: initialization and stop. Hence, initialization of the DMA
 *  controller, and channels, and stops of channels must be intercepted.
 *
 * Remaining register writes can be performed without interception.
 *
 * This leads to the following interceptions of register writes that may affect
 * the BD queues of the DMA channels:
 * -Start of DMA channel: Appends BDs to the BD queue to fetch.
 * -Initialization of DMA controller: Clears all queues of all channels.
 * -Initialization of DMA channel: Clears all queues.
 * -Stop of DMA channel: Removes BDs of the BD queue to fetch.
 *
 * To indicate that a channel is started and its abstract queue of BDs to be
 * fetched is to be assigned the BDs identified by the verification function
 * bds_to_fetch, memory1 is SOME memory1'.
 *
 * To indicate that BDs are appended, memory1 is SOME memory1 and memory2 is
 * SOME memory2', with the intention that memory2' is equal memory1 modified by
 * the write causing BDs to be appended.
 *
 * If both memory1 and memory2 are NONE, then this function acts as a concrete
 * register write, since:
 * -dma_append_bds_abstract does not change the state.
 * -channel_id_start_abstract does not change the state.
 * -channel_id_stop_abstract only clears bds_to_fetch which has no effect on a
 *  concrete model which does not use the abstract queue of BDs to fetch.
 *
 * The arguments have the following meaning:
 * -memory: State of memory before a DMA channel is started or BDs are appended.
 *  If NONE, then the register write does not cause BDs to be assigned or
 *  appended to bds_to_fetch.
 * -controller: State of the DMA controller before a register is written.
 *
 * @is_valid: Used to filter new memory requests that are appended to the queue
 *  of memory requests originating from DMA register writes made by the CPU.
 *)
Definition dma_register_write:
dma_register_write device_characteristics is_valid memory1 device address_bytes =
  let dma_characteristics            = device_characteristics.dma_characteristics in
  let addresses                      = MAP FST address_bytes in
  let pending_requests               = device.dma_state.pending_register_related_memory_requests in
  let (internal_state, new_requests) = dma_characteristics.register_write device.dma_state.internal_state address_bytes in
  let requests                       = FILTER is_valid new_requests in
  let read_requests                  = FILTER READ_REQUEST requests in
  let write_requests                 = FILTER WRITE_REQUEST requests in
  let dma_address_bytes              = FLAT (MAP request_to_address_bytes write_requests) in
  let device                         = device with dma_state := device.dma_state with <|internal_state := internal_state;
                                                                                        pending_register_related_memory_requests := pending_requests ++ read_requests|> in
  let memory2                        = update_memory_option memory1 dma_address_bytes in

  (* The new internal state SOME internal_state2 informs whether BDs are
   * appended or not via the bds_to_fetch function. Since dma_register_write
   * writes a register, the internal post-state is given to
   * dma_append_bds_abstract.
   *)
  let device                         = dma_append_internal_abstract_bds device_characteristics memory2 device in
    (device, dma_address_bytes)
End

Definition function_register_write:
function_register_write device_characteristics device address_bytes =
  let function_state = (THE device_characteristics.function_characteristics).function_register_write (THE device.function_state) address_bytes in
    device with function_state := SOME function_state
End

Definition device_register_write:
device_register_write device_characteristics is_valid memory device address_bytes =
  if EVERY device_characteristics.dma_characteristics.DMA_REGISTER_ADDRESSES (MAP FST address_bytes) then
    dma_register_write device_characteristics is_valid memory device address_bytes
  else if IS_SOME device_characteristics.function_characteristics then
    if EVERY (THE device_characteristics.function_characteristics).FUNCTION_REGISTER_ADDRESSES (MAP FST address_bytes) then
      (function_register_write device_characteristics device address_bytes, [])
    else
      (device, [])
  else
    (device, [])
End

(*******************************************************************************)
(*End of register writes********************************************************)
(*******************************************************************************)



(*******************************************************************************)
(*Start of transition system****************************************************)
(*******************************************************************************)

(* Labels for system transition system.
 *)
Datatype: system_transition_labels_type =
   cpu_internal_operation
 | cpu_memory_read                 (('interconnect_address_width interconnect_address_type # word8) list)
 | cpu_memory_write                (('interconnect_address_width interconnect_address_type # word8) list)
 | cpu_register_read_memory_write  ((('interconnect_address_width interconnect_address_type # word8) list) # (('interconnect_address_width interconnect_address_type # word8) list))
 | cpu_register_write_memory_write ((('interconnect_address_width interconnect_address_type # word8) list) # (('interconnect_address_width interconnect_address_type # word8) list))
 | device_internal_operation
 | device_memory_read              (('interconnect_address_width interconnect_address_type # word8) list)
 | device_memory_write             (('interconnect_address_width interconnect_address_type # word8) list)
End

(* System transition system.
 *)
Inductive system_transitions:
(* CPU performs internal transition:
 *
 * cpu1 -->cpu_internal cpu2
 * -------------------------------------------------------------
 * (cpu1, memory, device) -->cpu_internal (cpu2, memory, device)
 *)
(!cpu1 cpu2 cpu_transition memory (device (*: 
  ('bd_address_width,
   'bd_type,
   'channel_index_width_copy,
   'channel_index_width_read,
   'channel_index_width_write,
   'function_state_type,
   'interconnect_address_width,
   'internal_state_type,
   'tag_width) device_state_type*)).
  cpu_transition cpu1 (cpu_internal_operation : 'interconnect_address_width system_transition_labels_type) cpu2
  ==>
  (* device_transition does not need to have the argument memory since this
   * transition of the system holds for all device transition systems.
   *)
  system_transition cpu_transition device_transition (cpu1, memory, device) (cpu_internal_operation : 'interconnect_address_width system_transition_labels_type) (cpu2, memory, device)) /\



(* CPU reads memory:
 *
 * cpu1 -->memory_read address_bytes cpu2
 * MAP FST address_bytes ⊆ MEMORY_ADDRESSES
 * MAP (memory o FST) address_bytes = MAP SND address_bytes
 * ------------------------------------------------------------------------------
 * (cpu1, memory, device) -->cpu_memory_read address_bytes (cpu2, memory, device)
 *)
(!cpu1 cpu2 cpu_transition device_transition memory device MEMORY_ADDRESSES address_bytes.
  cpu_transition cpu1 (cpu_memory_read address_bytes) cpu2 /\
  EVERY MEMORY_ADDRESSES (MAP FST address_bytes) /\
  MAP (memory o FST) address_bytes = MAP SND address_bytes
  ==>
  (* device_transition does not need to have the argument memory since this
   * transition of the system holds for all device transition systems.
   *)
  system_transition cpu_transition device_transition (cpu1, memory, device) (cpu_memory_read address_bytes) (cpu2, memory, device)) /\



(* CPU writes memory, which may cause append of BDs:
 *
 * cpu1 -->memory_write address_bytes cpu2
 * MAP FST address_bytes ⊆ MEMORY_ADDRESSES	<---Depends on the computer: Physical addresses are assigned to RAM/main memory. Can be embedded in the CPU transition system, s.t. cpu_memory_write only occurs when addresses are in in MEMRY_ADDRESSES.
 * update_memory memory1 address_bytes = memory2
 * device_transition device_characteristics device1 (external_bds_appended memory2) device2)
 * -----------------------------------------------------------------------------------------
 * (cpu1, memory1, device) -->cpu_memory_write address_bytes (cpu2, memory2, device)
 *)
(!cpu1 cpu2 cpu_transition device_transition memory1 memory2 device1 device2 MEMORY_ADDRESSES address_bytes.
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  EVERY MEMORY_ADDRESSES (MAP FST address_bytes) /\
  memory2 = update_memory memory1 address_bytes /\
  device_transition device1 (memory2, external_bds_appended) device2 (* Device performs transition from written memory. *)
  ==>
  system_transition cpu_transition device_transition (cpu1, memory1, device1) (cpu_memory_write address_bytes) (cpu2, memory2, device2)) /\



(* CPU reads device register:
 *
 * cpu1 -->memory_read address_bytes cpu2
 * device1 -->register_read address_bytes device2
 * ------------------------------------------------------------------------------
 * (cpu1, memory, device1) -->cpu_register_read address_bytes (cpu2, memory, device2)
 *)
(!cpu1 cpu2 cpu_transition device_transition memory1 memory2 device1 device device2 cpu_address_bytes dma_address_bytes.
  cpu_transition cpu1 (cpu_memory_read cpu_address_bytes) cpu2 /\
  device_transition device1 (memory1, device_register_read (cpu_address_bytes, dma_address_bytes)) device /\
  memory2 = update_memory memory1 dma_address_bytes /\
  device_transition device (memory2, external_bds_appended) device2 (* Device performs transition from written memory. *)
  ==>
  system_transition cpu_transition device_transition (cpu1, memory1, device1) (cpu_register_read_memory_write (cpu_address_bytes, dma_address_bytes)) (cpu2, memory2, device2)) /\



(* CPU writes device register:
 *
 * cpu1 -->memory_write address_bytes cpu2
 * device1 -->register_write address_bytes device2
 * ------------------------------------------------------------------------------
 * (cpu1, memory, device1) -->cpu_register_write address_bytes (cpu2, memory, device2)
 *)
(!cpu1 cpu2 cpu_transition device_transition memory1 memory2 device1 device2 cpu_address_bytes.
  cpu_transition cpu1 (cpu_memory_write cpu_address_bytes) cpu2 /\
  device_transition device1 (memory1, device_register_write (cpu_address_bytes, dma_address_bytes)) device2 /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  system_transition cpu_transition device_transition (cpu1, memory1, device1) (cpu_register_write_memory_write (cpu_address_bytes, dma_address_bytes)) (cpu2, memory2, device2)) /\



(* Device performs internal operation:
 *
 * device1 --> internal_operation device2
 * --------------------------------------------------------------------------
 * (cpu, memory, device1) -->device_internal_operation (cpu, memory, device2)
 *)
(!cpu memory device1 device2 cpu_transition device_transition.
  device_transition device1 (memory, state$device_internal_operation environment) device2
  ==>
  system_transition cpu_transition device_transition (cpu, memory, device1) (device_internal_operation (*: 'interconnect_address_width system_transition_labels_type*)) (cpu, memory, device2)) /\



(* Device reads memory:
 *
 * device1 -->device_memory_read address_bytes device2
 * memory (MAP FST address_bytes) = MAP SND address_bytes
 * ---------------------------------------------------------------------------------
 * (cpu, memory, device1) -->device_memory_read address_bytes (cpu, memory, device2)
 *)
(!cpu device1 device2 cpu_transition device_transition address_bytes memory.
  device_transition device1 (memory, state$device_memory_read address_bytes) device2 /\
  (MAP memory (MAP FST address_bytes) = MAP SND address_bytes)
  ==>
  system_transition cpu_transition device_transition (cpu, memory, device1) (device_memory_read address_bytes) (cpu, memory, device2)) /\



(* Device writes memory:
 *
 * device1 -->device_memory_write address_bytes device2
 * memory2 = update_memory memory1 address_bytes
 * device2 -->append_external_bds address_bytes device3
 * ------------------------------------------------------------------------------------
 * (cpu, memory1, device1) -->device_memory_write address_bytes (cpu, memory2, device3)
 *)
(!cpu memory1 memory2 device1 device2 cpu_transition device_transition address_bytes.
  device_transition device1 (memory1, state$device_memory_write address_bytes) device2 /\
  (memory2 = update_memory memory1 address_bytes)
  ==>
  system_transition cpu_transition device_transition (cpu, memory1, device1) (device_memory_write address_bytes) (cpu, memory2, device2))
End

(*******************************************************************************)
(*End of system transition system***********************************************)
(*******************************************************************************)

val _ = export_theory();

