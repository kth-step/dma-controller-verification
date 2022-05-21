open HolKernel Parse boolLib bossLib helper_tactics;
open l3Theory invariant_l3Theory;

val _ = new_theory "transferring_data_l3_preserves_invariant_concrete_l3_lemmas";

Theorem TRANSFERRING_DATA_UPDATE_QS_PRESERVES_PENDING_ACCESSES_REPLIES_REQUESTS_LEMMA:
!channel1 channel2 bd bds.
  channel2 = transferring_data_update_qs channel1 bd bds
  ==>
  channel2.pending_accesses.replies = channel1.pending_accesses.replies /\
  channel2.pending_accesses.requests = channel1.pending_accesses.requests
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_update_qs THEN
ETAC operationsTheory.update_channel_qs THEN
ETAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem TRANSFERRING_DATA_UPDATE_QS_SHIFTS_BDS_TO_UPDATE_PROCESS_WRITE_BACK_LEMMA:
!channel1 channel2 bd bds.
  channel1.queue.bds_to_process = bd::bds /\
  channel2 = transferring_data_update_qs channel1 bd bds
  ==>
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = bds /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back ++ [bd]
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_update_qs THEN
ETAC operationsTheory.update_channel_qs THEN
ETAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_PENDING_ACCESSES_REQUESTS_FETCHING_UPDATING_WRITING_BACK_BDS_APPEND_TRANSFERRING_DATA_LEMMA:
!channel1 channel2 new_requests.
  channel2 = transferring_data_append_requests channel1 new_requests
  ==>
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data ++ new_requests /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_append_requests THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_BDS_LEMMA:
!channel1 channel2 new_requests.
  channel2 = transferring_data_append_requests channel1 new_requests
  ==>
  channel2.queue = channel1.queue
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_append_requests THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem TRANSFERRING_DATA_CLEAR_REPLIES_PRESERVES_PENDING_ACCESSES_REQUESTS_LEMMA:
!channel1 channel2.
  channel2 = transferring_data_clear_replies channel1
  ==>
  channel2.pending_accesses.requests = channel1.pending_accesses.requests
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_clear_replies THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem TRANSFERRING_DATA_CLEAR_REPLIES_PRESERVES_BDS_LEMMA:
!channel1 channel2.
  channel2 = transferring_data_clear_replies channel1
  ==>
  channel2.queue = channel1.queue
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_clear_replies THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED


Theorem TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_PENDING_ACCESSES_REQUESTS_LEMMA:
!replies process_replies_generate_requests internal_state1 internal_state2 channel1 channel2 bd new_requests complete.
  (internal_state2, channel2, new_requests, complete) = transferring_data_replies_requests replies process_replies_generate_requests internal_state1 channel1 bd
  ==>
  channel2.pending_accesses.requests = channel1.pending_accesses.requests
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_replies_requests THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 4 THEN
IRTAC TRANSFERRING_DATA_CLEAR_REPLIES_PRESERVES_PENDING_ACCESSES_REQUESTS_LEMMA THEN
STAC
QED

Theorem TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_BDS_LEMMA:
!replies process_replies_generate_requests internal_state1 internal_state2 channel1 channel2 bd new_requests complete.
  (internal_state2, channel2, new_requests, complete) = transferring_data_replies_requests replies process_replies_generate_requests internal_state1 channel1 bd
  ==>
  channel2.queue = channel1.queue
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_replies_requests THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 4 THEN
IRTAC TRANSFERRING_DATA_CLEAR_REPLIES_PRESERVES_BDS_LEMMA THEN
STAC
QED


Theorem TRANSFERRING_DATA_L3_PRESERVES_REQUESTS_FETCHING_UPDATING_WRITING_BACK_BD_TRANSFERRING_DATA_EXPANSION_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  (channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data \/
   ?new_requests complete bd bd_ras bd_was bds replies process channel.
     channel1.queue.bds_to_process = (bd, bd_ras, bd_was)::bds /\
     replies = channel1.pending_accesses.replies.transferring_data /\
     CONSISTENT_DMA_WRITE device_characteristics memory internal_state2 (FLAT (MAP request_to_write_addresses new_requests)) /\
     process = (coperation device_characteristics channel_id).process_replies_generate_requests /\
     (internal_state2, channel, new_requests, complete) = transferring_data_replies_requests replies process internal_state1 channel1 bd /\
     channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data ++ new_requests) /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC transferring_data_l3 THENL
[
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 ITAC TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_PENDING_ACCESSES_REQUESTS_LEMMA THEN
 IF_SPLIT_TAC THEN
  IRTAC TRANSFERRING_DATA_UPDATE_QS_PRESERVES_PENDING_ACCESSES_REPLIES_REQUESTS_LEMMA THEN
  RLTAC THEN
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_PENDING_ACCESSES_REQUESTS_FETCHING_UPDATING_WRITING_BACK_BDS_APPEND_TRANSFERRING_DATA_LEMMA THEN
  NLRTAC 4 THEN
  RLTAC THEN
  REWRITE_TAC [] THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  PAXTAC THEN
  STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 2 THEN
 ITAC TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_PENDING_ACCESSES_REQUESTS_LEMMA THEN
 IF_SPLIT_TAC THEN
  IRTAC TRANSFERRING_DATA_UPDATE_QS_PRESERVES_PENDING_ACCESSES_REPLIES_REQUESTS_LEMMA THEN
  STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem TRANSFERRING_DATA_L3_PRESERVES_OR_ADDS_WRITE_REQUEST_LEMMA:
!device_characteristics memory internal_state1 internal_state2 channel1 channel2 channel_id request.
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  MEM request (channel_pending_requests channel2.pending_accesses.requests)
  ==>
  MEM request (channel_pending_requests channel1.pending_accesses.requests) \/
  ?bd bd_ras bd_was bds new_requests complete replies.
    channel1.queue.bds_to_process = (bd, bd_ras, bd_was)::bds /\
    (internal_state2, new_requests, complete) = (coperation device_characteristics channel_id).process_replies_generate_requests internal_state1 bd replies /\
    CONSISTENT_DMA_WRITE device_characteristics memory internal_state2 (FLAT (MAP request_to_write_addresses new_requests)) /\
    MEM request new_requests
Proof
INTRO_TAC THEN
ETAC operationsTheory.channel_pending_requests THEN
IRTAC TRANSFERRING_DATA_L3_PRESERVES_REQUESTS_FETCHING_UPDATING_WRITING_BACK_BD_TRANSFERRING_DATA_EXPANSION_LEMMA THEN
RLTAC THEN
RLTAC THEN
RLTAC THEN
SPLIT_ASM_DISJS_TAC THEN TRY (RLTAC THEN STAC) THEN
AXTAC THEN
RLTAC THEN
LRTAC THEN
LRTAC THEN
ETAC listTheory.MEM_APPEND THEN
SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
LRTAC THEN
ETAC listTheory.MEM_APPEND THEN
SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
PTAC operationsTheory.transferring_data_replies_requests THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 4 THEN
PAXTAC THEN
EXISTS_EQ_TAC THEN
STAC
QED

Theorem TRANSFERRING_DATA_L3_UPDATE_DEVICE_STATE_IMPLIES_ADDED_UPDATE_WRITE_REQUEST_LEMMA:
!device_characteristics memory channel_id device1 device2 internal_state1 internal_state2 channel1 channel2 request.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channel1 = schannel device1 channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  MEM request (channel_requests device_characteristics device2)
  ==>
  MEM request (channel_requests device_characteristics device1) \/
  ?bd bd_ras bd_was bds new_requests complete replies.
    channel1.queue.bds_to_process = (bd, bd_ras, bd_was)::bds /\
    (internal_state2, new_requests, complete) = (coperation device_characteristics channel_id).process_replies_generate_requests internal_state1 bd replies /\
    CONSISTENT_DMA_WRITE device_characteristics memory internal_state2 (FLAT (MAP request_to_write_addresses new_requests)) /\
    MEM request new_requests
Proof
INTRO_TAC THEN
IRTAC dma_pending_requests_lemmasTheory.MEM_CHANNEL_REQUESTS_IMPLIES_SOME_VALID_CHANNEL_PENDING_REQUESTS_LEMMA THEN
AXTAC THEN
Cases_on ‘channel_id = channel_id'’ THENL
[
 RLTAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN
 LRTAC THEN
 LRTAC THEN
 IRTAC TRANSFERRING_DATA_L3_PRESERVES_OR_ADDS_WRITE_REQUEST_LEMMA THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  IRTAC dma_pending_requests_lemmasTheory.CHANNEL_PENDING_REQUESTS_IN_CHANNEL_REQUESTS_LEMMA THEN STAC
  ,
  STAC
 ]
 ,
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN
 PAT_X_ASSUM “~P” (fn thm => ASSUME_TAC (GSYM thm)) THEN
 AIRTAC THEN
 LRTAC THEN
 LRTAC THEN
 IRTAC dma_pending_requests_lemmasTheory.CHANNEL_PENDING_REQUESTS_IN_CHANNEL_REQUESTS_LEMMA THEN
 STAC
]
QED

Theorem TRANSFERRING_DATA_L3_PRESERVES_OR_UPDATES_INTERNAL_STATE_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  internal_state2 = internal_state1 \/
  ?new_requests complete bd replies.
    (internal_state2, new_requests, complete) = (coperation device_characteristics channel_id).process_replies_generate_requests internal_state1 bd replies
Proof
INTRO_TAC THEN
PTAC transferring_data_l3 THENL
[
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 PTAC operationsTheory.transferring_data_replies_requests THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 4 THEN
 PAXTAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 PTAC operationsTheory.transferring_data_replies_requests THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 4 THEN
 PAXTAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem TRANSFERRING_DATA_L3_IMPLIES_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  BDS_TO_FETCH_EQ device_characteristics memory internal_state1 internal_state2
Proof
INTRO_TAC THEN
IRTAC TRANSFERRING_DATA_L3_PRESERVES_OR_UPDATES_INTERNAL_STATE_LEMMA THEN
SPLIT_ASM_DISJS_TAC THEN TRY (ASM_REWRITE_TAC [stateTheory.BDS_TO_FETCH_EQ]) THEN
AXTAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH THEN
AIRTAC THEN
STAC
QED

Theorem WRITE_REQUEST_IN_FLAT_REQUEST_TO_WRITE_ADDRESSES_LEMMA:
!requests address_bytes tag requests_was request_was.
  MAP FST address_bytes = request_was /\
  MEM (request_write address_bytes tag) requests /\
  requests_was = FLAT (MAP request_to_write_addresses requests)
  ==>
  LIST1_IN_LIST2 request_was requests_was
Proof
Induct THEN REWRITE_TAC [listTheory.MEM] THEN
INTRO_TAC THEN
SPLIT_ASM_DISJS_TAC THENL
[
 RLTAC THEN
 ETAC listTheory.MAP THEN
 ETAC listTheory.FLAT THEN
 LRTAC THEN
 ETAC listsTheory.LIST1_IN_LIST2 THEN
 REWRITE_TAC [listTheory.MEM_APPEND] THEN
 RLTAC THEN
 ETAC operationsTheory.request_to_write_addresses THEN
 ETAC listTheory.EVERY_MEM THEN
 INTRO_TAC THEN
 APP_SCALAR_TAC THEN
 STAC
 ,
 AIRTAC THEN
 LRTAC THEN
 ETAC listTheory.MAP THEN
 ETAC listTheory.FLAT THEN
 ETAC listsTheory.LIST1_IN_LIST2 THEN
 ETAC listTheory.EVERY_MEM THEN
 INTRO_TAC THEN
 AIRTAC THEN
 APP_SCALAR_TAC THEN
 ETAC listTheory.MEM_APPEND THEN
 STAC
]
QED

Theorem LIST1_IN_LIST2_PRESERVES_WRITE_ADDRESS_NOT_BD_TO_FETCH_LEMMA:
!device_characteristics memory internal_state l1 l2.
  LIST1_IN_LIST2 l1 l2 /\
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory internal_state l2
  ==>
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory internal_state l1
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
INTRO_TAC THEN
AIRTAC THEN
IRTAC lists_lemmasTheory.LIST1_IN_LIST2_PRESERVES_DISJOINTNESS_LEMMA THEN
STAC
QED

Theorem REQUEST_TO_WRITE_ADDRESSES_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA:
!device_characteristics memory internal_state new_requests address_bytes request_was tag.
  MAP FST address_bytes = request_was /\
  MEM (request_write address_bytes tag) new_requests /\
  CONSISTENT_DMA_WRITE device_characteristics memory internal_state (FLAT (MAP request_to_write_addresses new_requests))
  ==>
  CONSISTENT_DMA_WRITE device_characteristics memory internal_state request_was
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.CONSISTENT_DMA_WRITE THEN
INTRO_TAC THEN
AIRTAC THEN
IRTAC WRITE_REQUEST_IN_FLAT_REQUEST_TO_WRITE_ADDRESSES_LEMMA THEN
IRTAC LIST1_IN_LIST2_PRESERVES_WRITE_ADDRESS_NOT_BD_TO_FETCH_LEMMA THEN
STAC
QED

Theorem TRANSFERRING_DATA_L3_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device1
  ==>
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC NO_MEMORY_WRITES_TO_BDS THEN
INTRO_TAC THEN
ITAC internal_operation_lemmasTheory.REQUEST_WAS_EMPTY_OR_WRITE_REQUEST_LEMMA THEN
SPLIT_ASM_DISJS_TAC THEN TRY (ASM_REWRITE_TAC [bd_queues_lemmasTheory.CONSISTENT_DMA_WRITE_EMPTY_WRITE_ADDRESSES_LEMMA] THEN NO_TAC) THEN
AXTAC THEN
ITAC TRANSFERRING_DATA_L3_UPDATE_DEVICE_STATE_IMPLIES_ADDED_UPDATE_WRITE_REQUEST_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 IRTAC internal_operation_lemmasTheory.WRITE_REQUEST_IN_REQUEST_WRITE_ADDRESSES_LEMMA THEN
 AXTAC THEN
 AIRTAC THEN
 IRTAC TRANSFERRING_DATA_L3_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
 IRTAC bd_queues_lemmasTheory.BDS_TO_FETCH_EQ_PRESERVE_CONSISTENT_DMA_WRITE_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 STAC
 ,
 AXTAC THEN
 IRTAC REQUEST_TO_WRITE_ADDRESSES_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 STAC
]
QED



Theorem TRANSFERRING_DATA_L3_SHIFTS_BDS_TO_PROCESS_WRITE_BACK_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  (channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
   channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back) \/
  ?bd bds.
    channel1.queue.bds_to_process = bd::bds /\
    channel2.queue.bds_to_process = bds /\
    channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back ++ [bd]
Proof
INTRO_TAC THEN
PTAC transferring_data_l3 THENL
[
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 IRTAC TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_BDS_LEMMA THEN
 IF_SPLIT_TAC THENL
 [
  RLTAC THEN
  ITAC TRANSFERRING_DATA_UPDATE_QS_SHIFTS_BDS_TO_UPDATE_PROCESS_WRITE_BACK_LEMMA THEN
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_BDS_LEMMA THEN
  RLTAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  LRTAC THEN
  RLTAC THEN
  RLTAC THEN
  EXISTS_EQ_TAC
  ,
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_BDS_LEMMA THEN
  STAC
 ]
 ,
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 2 THEN
 IRTAC TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_BDS_LEMMA THEN
 RLTAC THEN
 IF_SPLIT_TAC THENL
 [
  ITAC TRANSFERRING_DATA_UPDATE_QS_SHIFTS_BDS_TO_UPDATE_PROCESS_WRITE_BACK_LEMMA THEN
  LRTAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  LRTAC THEN
  RLTAC THEN
  EXISTS_EQ_TAC
  ,
  STAC
 ]
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem TRANSFERRING_DATA_L3_PRESERVES_BDS_TO_UPDATE_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  channel2.queue.bds_to_update = channel1.queue.bds_to_update
Proof
INTRO_TAC THEN
PTAC transferring_data_l3 THENL
[
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 IRTAC TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_BDS_LEMMA THEN
 IF_SPLIT_TAC THENL
 [
  RLTAC THEN
  ITAC TRANSFERRING_DATA_UPDATE_QS_SHIFTS_BDS_TO_UPDATE_PROCESS_WRITE_BACK_LEMMA THEN
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_BDS_LEMMA THEN
  STAC
  ,
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_BDS_LEMMA THEN STAC
 ]
 ,
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 2 THEN
 IRTAC TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_BDS_LEMMA THEN
 RLTAC THEN
 IF_SPLIT_TAC THENL
 [
  ITAC TRANSFERRING_DATA_UPDATE_QS_SHIFTS_BDS_TO_UPDATE_PROCESS_WRITE_BACK_LEMMA THEN STAC
  ,
  STAC
 ]
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem TRANSFERRING_DATA_L3_NOT_ADDING_BDS_LEMMA:
!device_characteristics memory internal_state1 internal_state2 channel1 channel2 channel_id channel_bd_queues1 channel_bd_queues2.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  channel_bd_queues1 = channel_bd_queues device_characteristics channel_id memory internal_state1 channel1 /\
  channel_bd_queues2 = channel_bd_queues device_characteristics channel_id memory internal_state2 channel2
  ==>
  CHANNEL_SET channel_bd_queues2 SUBSET CHANNEL_SET channel_bd_queues1
Proof
INTRO_TAC THEN
ETAC CHANNEL_SET THEN
ETAC pred_setTheory.SUBSET_DEF THEN
REWRITE_TAC [invariant_l3_lemmasTheory.SET_ETA_LEMMA, pred_setTheory.GSPEC_ETA, invariant_l3_lemmasTheory.IN_MEM_ABS_EQ_MEM_LEMMA] THEN
INTRO_TAC THEN
ETAC channel_bd_queues THEN
LETS_TAC THEN
ITAC TRANSFERRING_DATA_L3_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
ITAC TRANSFERRING_DATA_L3_SHIFTS_BDS_TO_PROCESS_WRITE_BACK_LEMMA THEN
ITAC TRANSFERRING_DATA_L3_PRESERVES_BDS_TO_UPDATE_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 ALL_LRTAC THEN
 ETAC stateTheory.BDS_TO_FETCH_EQ THEN
 AIRTAC THEN
 RLTAC THEN
 STAC
 ,
 AXTAC THEN
 ALL_LRTAC THEN
 ETAC listTheory.MEM_APPEND THEN
 SPLIT_ASM_DISJS_TAC THEN TRY STAC THENL
 [
  ETAC stateTheory.BDS_TO_FETCH_EQ THEN AIRTAC THEN STAC
  ,
  ETAC listTheory.MEM THEN STAC
  ,
  ETAC listTheory.MEM THEN REMOVE_F_DISJUNCTS_TAC THEN STAC
 ]
]
QED

Theorem TRANSFERRING_DATA_L3_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA:
!device_characteristics channel_id memory device1 device2 internal_state1 internal_state2 channel1 channel2.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
IRTAC TRANSFERRING_DATA_L3_PRESERVES_OR_UPDATES_INTERNAL_STATE_LEMMA THEN
ETAC stateTheory.BD_TRANSFER_RAS_WAS_EQ THEN
SPLIT_ASM_DISJS_TAC THENL
[
 RLTAC THEN LRTAC THEN IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN STAC
 ,
 AXTAC THEN
 ETAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION THEN
 AIRTAC THEN
 RLTAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 LRTAC THEN
 INTRO_TAC THEN
 AIRTAC THEN
 STAC
]
QED

Theorem TRANSFERRING_DATA_L3_PRESERVES_NOT_DMA_BDS_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  NOT_DMA_BDS device_characteristics memory device1
  ==>
  NOT_DMA_BDS device_characteristics memory device2
Proof
REWRITE_TAC [NOT_DMA_BDS, GSYM invariant_l3_lemmasTheory.CHANNEL_BD_QUEUES_EQ_CHANNEL_BDS_LEMMA] THEN
INTRO_TAC THEN
INTRO_TAC THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC_ALL thm)) THEN
INST_IMP_ASM_GOAL_TAC THEN
CONJS_TAC THEN TRY STAC THENL
[
 FITAC TRANSFERRING_DATA_L3_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
 FITAC TRANSFERRING_DATA_L3_NOT_ADDING_BDS_LEMMA THEN
 ITAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 RLTAC THEN
 ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_CHANNEL_EQ_LEMMA THEN
 FIRTAC invariant_l3_lemmasTheory.UPDATE_DEVICE_STATE_BDS_TO_FETCH_EQ_NOT_ADDING_BDS_LEMMA THEN
 ITAC invariant_l3_lemmasTheory.CHANNEL_BD_QUEUES_SUBSET_TRANSFERS_MEM_LEMMA THEN
 STAC
 ,
 FIRTAC TRANSFERRING_DATA_L3_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA THEN
 IRTAC invariant_l3_lemmasTheory.BD_TRANSFER_RAS_WAS_PRESERVES_BD_DMA_WRITE_ADDRESSES_LEMMA THEN
 STAC
 ,
 WEAKEN_TAC (fn term => Term.compare (term, “VALID_CHANNEL_ID device_characteristics channel_id_dma_bd”) = EQUAL) THEN
 FITAC TRANSFERRING_DATA_L3_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
 FITAC TRANSFERRING_DATA_L3_NOT_ADDING_BDS_LEMMA THEN
 ITAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 RLTAC THEN
 ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_CHANNEL_EQ_LEMMA THEN
 FIRTAC invariant_l3_lemmasTheory.UPDATE_DEVICE_STATE_BDS_TO_FETCH_EQ_NOT_ADDING_BDS_LEMMA THEN
 ITAC invariant_l3_lemmasTheory.CHANNEL_BD_QUEUES_SUBSET_TRANSFERS_MEM_LEMMA THEN
 STAC
]
QED



Theorem TRANSFERRING_DATA_L3_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device1
  ==>
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device2
Proof
INTRO_TAC THEN
ETAC MEMORY_WRITES_PRESERVES_BDS_TO_FETCH THEN
IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA THEN
STAC
QED



Theorem TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_REPLIES_REQUESTS_FETCHING_BD_LEMMA:
!replies process internal_state1 internal_state2 channel1 channel2 bd new_requests complete.
  (internal_state2, channel2, new_requests, complete) = transferring_data_replies_requests replies process internal_state1 channel1 bd
  ==>
  channel2.pending_accesses.replies.fetching_bd = channel1.pending_accesses.replies.fetching_bd /\
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_replies_requests THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 4 THEN
PTAC operationsTheory.transferring_data_clear_replies THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_REPLIES_REQUESTS_FETCHING_BD_LEMMA:
!channel1 channel2 new_requests.
  channel2 = transferring_data_append_requests channel1 new_requests
  ==>
  channel2.pending_accesses.replies.fetching_bd = channel1.pending_accesses.replies.fetching_bd /\
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_append_requests THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem TRANSFERRING_DATA_L3_PRESERVES_REPLIES_REQUESTS_FETCHING_BD_LEMMA:
!device_characteristics channel_id memory channel1 channel2 internal_state1 internal_state2.
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  channel2.pending_accesses.replies.fetching_bd = channel1.pending_accesses.replies.fetching_bd /\
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd
Proof
INTRO_TAC THEN
PTAC transferring_data_l3 THEN EQ_PAIR_ASM_TAC THEN RLTAC THENL
[
 IRTAC TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_REPLIES_REQUESTS_FETCHING_BD_LEMMA THEN
 IF_SPLIT_TAC THENL
 [
  IRTAC TRANSFERRING_DATA_UPDATE_QS_PRESERVES_PENDING_ACCESSES_REPLIES_REQUESTS_LEMMA THEN
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_REPLIES_REQUESTS_FETCHING_BD_LEMMA THEN
  STAC
  ,
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_REPLIES_REQUESTS_FETCHING_BD_LEMMA THEN STAC
 ]
 ,
 IRTAC TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_REPLIES_REQUESTS_FETCHING_BD_LEMMA THEN
 IF_SPLIT_TAC THENL
 [
  IRTAC TRANSFERRING_DATA_UPDATE_QS_PRESERVES_PENDING_ACCESSES_REPLIES_REQUESTS_LEMMA THEN
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_REPLIES_REQUESTS_FETCHING_BD_LEMMA THEN
  STAC
  ,
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_REPLIES_REQUESTS_FETCHING_BD_LEMMA THEN STAC
 ]
 ,
 STAC
]
QED

Theorem UPDATE_STATE_TRANSFERRING_DATA_L3_PRESERVES_PENDING_ACCESSES_REPLIES_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 device1 device2.
  channel1 = schannel device1 channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  !channel_id.
    (schannel device2 channel_id).pending_accesses.replies.fetching_bd = (schannel device1 channel_id).pending_accesses.replies.fetching_bd
Proof
INTRO_TAC THEN
GEN_TAC THEN
Cases_on ‘channel_id = channel_id'’ THENL
[
 RLTAC THEN
 RLTAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_CHANNEL_EQ_LEMMA THEN
 RLTAC THEN
 IRTAC TRANSFERRING_DATA_L3_PRESERVES_REPLIES_REQUESTS_FETCHING_BD_LEMMA THEN
 STAC
 ,
 ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_PENDING_ACCESSES_REPLIES_FETCHING_BD_LEMMA THEN
 STAC
]
QED

Theorem TRANSFERRING_DATA_L3_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device1
  ==>
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_EXTERNAL_FETCH_BD_REPLY THEN
INTRO_TAC THEN
ITAC UPDATE_STATE_TRANSFERRING_DATA_L3_PRESERVES_PENDING_ACCESSES_REPLIES_LEMMA THEN
QLRTAC THEN
ITAC TRANSFERRING_DATA_L3_PRESERVES_OR_UPDATES_INTERNAL_STATE_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN RLTAC THEN RLTAC THEN RLTAC THEN AIRTAC THEN STAC
 ,
 AXTAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_FETCH_BD_ADDRESSES THEN
 FAIRTAC THEN
 AITAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 RLTAC THEN
 AITAC THEN
 STAC
]
QED



Theorem UPDATE_STATE_TRANSFERRING_DATA_L3_PRESERVES_PENDING_ACCESSES_REQUESTS_FETCHING_BD_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 device1 device2.
  channel1 = schannel device1 channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  !channel_id.
    (schannel device2 channel_id).pending_accesses.requests.fetching_bd = (schannel device1 channel_id).pending_accesses.requests.fetching_bd
Proof
INTRO_TAC THEN
GEN_TAC THEN
Cases_on ‘channel_id = channel_id'’ THENL
[
 RLTAC THEN
 RLTAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_CHANNEL_EQ_LEMMA THEN
 RLTAC THEN
 IRTAC TRANSFERRING_DATA_L3_PRESERVES_REPLIES_REQUESTS_FETCHING_BD_LEMMA THEN
 STAC
 ,
 ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_PENDING_ACCESSES_REQUESTS_FETCHING_BD_LEMMA THEN
 STAC
]
QED

Theorem TRANSFERRING_DATA_L3_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device1
  ==>
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES THEN
INTRO_TAC THEN
ITAC UPDATE_STATE_TRANSFERRING_DATA_L3_PRESERVES_PENDING_ACCESSES_REQUESTS_FETCHING_BD_LEMMA THEN
QLRTAC THEN
IRTAC TRANSFERRING_DATA_L3_PRESERVES_OR_UPDATES_INTERNAL_STATE_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN RLTAC THEN RLTAC THEN RLTAC THEN AIRTAC THEN STAC
 ,
 AXTAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_FETCH_BD_ADDRESSES THEN
 FAITAC THEN
 AITAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 RLTAC THEN
 AIRTAC THEN
 STAC
]
QED

Theorem TRANSFERRING_DATA_L3_PRESERVES_INVARIANT_BDS_TO_FETCH_DISJOINT_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device1
  ==>
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device2
Proof
INTRO_TAC THEN
ITAC TRANSFERRING_DATA_L3_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
ETAC invariant_l3Theory.INVARIANT_BDS_TO_FETCH_DISJOINT THEN
INTRO_TAC THEN
AITAC THEN
ETAC stateTheory.BDS_TO_FETCH_EQ THEN
AIRTAC THEN
IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
LRTAC THEN
LRTAC THEN
RLTAC THEN
STAC
QED

Theorem TRANSFERRING_DATA_L3_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  INVARIANT_CONCRETE_L3 device_characteristics memory device1
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_CONCRETE_L3 THEN
ITAC TRANSFERRING_DATA_L3_PRESERVES_INVARIANT_BDS_TO_FETCH_DISJOINT_LEMMA THEN
ITAC TRANSFERRING_DATA_L3_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA THEN
ITAC TRANSFERRING_DATA_L3_PRESERVES_NOT_DMA_BDS_LEMMA THEN
ITAC TRANSFERRING_DATA_L3_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA THEN
ITAC TRANSFERRING_DATA_L3_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA THEN
ITAC TRANSFERRING_DATA_L3_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA THEN
STAC
QED

val _ = export_theory();

