open HolKernel Parse boolLib bossLib helper_tactics;
open l3Theory invariant_l3Theory;

val _ = new_theory "writing_back_bd_l3_preserves_invariant_concrete_l3_lemmas";

Theorem WRITING_BACK_BD_REMOVE_RELEASED_BDS_NOT_ADDING_BDS_TO_PIPELINE_LEMMA:
!channel1 channel2 released_bds.
  channel2 = writing_back_bd_remove_released_bds channel1 released_bds
  ==>
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  LIST1_IN_LIST2 channel2.queue.bds_to_write_back channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC operationsTheory.writing_back_bd_remove_released_bds THEN
PTAC operationsTheory.update_channel_qs THEN
PTAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [] THEN
REPEAT (WEAKEN_TAC (fn _ => true)) THEN
ETAC listsTheory.LIST1_IN_LIST2 THEN
ETAC listTheory.EVERY_MEM THEN
INTRO_TAC THEN
ETAC listTheory.MEM_FILTER THEN
APP_SCALAR_TAC THEN
STAC
QED

Theorem WRITING_BACK_BD_REMOVE_RELEASED_BDS_PRESERVES_PENDING_ACCESSES_LEMMA:
!channel1 channel2 released_bds.
  channel2 = writing_back_bd_remove_released_bds channel1 released_bds
  ==>
  channel2.pending_accesses = channel1.pending_accesses
Proof
INTRO_TAC THEN
PTAC operationsTheory.writing_back_bd_remove_released_bds THEN
LRTAC THEN
PTAC operationsTheory.update_channel_qs THEN
RECORD_TAC THEN
STAC
QED

Theorem WRITING_BACK_BD_APPEND_REQUEST_PRESERVES_BDS_LEMMA:
!channel1 channel2 write_address_bytes tag.
  channel2 = writing_back_bd_append_request channel1 write_address_bytes tag
  ==>
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC operationsTheory.writing_back_bd_append_request THEN TRY STAC THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem WRITING_BACK_BD_APPEND_REQUEST_PRESERVES_OR_ADDS_WRITE_REQUEST_LEMMA:
!channel1 channel2 write_address_bytes tag.
  channel2 = writing_back_bd_append_request channel1 write_address_bytes tag
  ==>
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data /\
  (channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd \/
   channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd ++ [request_write write_address_bytes tag])
Proof
INTRO_TAC THEN
PTAC operationsTheory.writing_back_bd_append_request THEN TRY STAC THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem WRITING_BACK_BD_L3_PRESERVES_OR_ADDS_CONSISTENT_WRITE_REQUEST_LEMMA:
!device_characteristics channel_id memory environment internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1
  ==>
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data /\
  (channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd \/
   ?write_addresses write_address_bytes tag released_bds.
     write_addresses = (cverification device_characteristics channel_id).write_back_bd_addresses environment internal_state1 channel1.queue.bds_to_write_back /\
     CONSISTENT_BD_WRITE device_characteristics memory internal_state1 write_addresses /\
     (internal_state2, write_address_bytes, tag, released_bds) = (coperation device_characteristics channel_id).write_back_bd environment internal_state1 channel1.queue.bds_to_write_back /\
     channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd ++ [request_write write_address_bytes tag])
Proof
INTRO_TAC THEN
PTAC writing_back_bd_l3 THEN EQ_PAIR_ASM_TAC THEN RLTAC THENL
[
 RLTAC THEN IRTAC WRITING_BACK_BD_REMOVE_RELEASED_BDS_PRESERVES_PENDING_ACCESSES_LEMMA THEN STAC
 ,
 IRTAC WRITING_BACK_BD_REMOVE_RELEASED_BDS_PRESERVES_PENDING_ACCESSES_LEMMA THEN
 IRTAC WRITING_BACK_BD_APPEND_REQUEST_PRESERVES_OR_ADDS_WRITE_REQUEST_LEMMA THEN
 NLRTAC 3 THEN
 LRTAC THEN
 REWRITE_TAC [] THEN
 SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 PAXTAC THEN
 STAC
 ,
 STAC
]
QED

Theorem WRITING_BACK_BD_L3_NOT_ADDING_BDS_TO_PIPELINE_LEMMA:
!device_characteristics channel_id memory channel1 channel2 internal_state1 internal_state2 environment.
  (internal_state2, channel2) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1
  ==>
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  LIST1_IN_LIST2 channel2.queue.bds_to_write_back channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC writing_back_bd_l3 THEN EQ_PAIR_ASM_TAC THEN RLTAC THENL
[
 IRTAC WRITING_BACK_BD_REMOVE_RELEASED_BDS_NOT_ADDING_BDS_TO_PIPELINE_LEMMA THEN STAC
 ,
 IRTAC WRITING_BACK_BD_REMOVE_RELEASED_BDS_NOT_ADDING_BDS_TO_PIPELINE_LEMMA THEN
 IRTAC WRITING_BACK_BD_APPEND_REQUEST_PRESERVES_BDS_LEMMA THEN
 NRLTAC 2 THEN
 STAC
 ,
 RLTAC THEN REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
]
QED

Theorem WRITING_BACK_BD_L3_NOT_ADDING_BDS_TO_PIPELINE_LEMMA:
!device_characteristics channel_id memory channel1 channel2 internal_state1 internal_state2 environment.
  (internal_state2, channel2) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1
  ==>
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  LIST1_IN_LIST2 channel2.queue.bds_to_write_back channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC writing_back_bd_l3 THEN EQ_PAIR_ASM_TAC THEN RLTAC THENL
[
 IRTAC WRITING_BACK_BD_REMOVE_RELEASED_BDS_NOT_ADDING_BDS_TO_PIPELINE_LEMMA THEN STAC
 ,
 IRTAC WRITING_BACK_BD_REMOVE_RELEASED_BDS_NOT_ADDING_BDS_TO_PIPELINE_LEMMA THEN
 IRTAC WRITING_BACK_BD_APPEND_REQUEST_PRESERVES_BDS_LEMMA THEN
 NRLTAC 2 THEN
 STAC
 ,
 RLTAC THEN REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
]
QED

Theorem WRITING_BACK_BD_L3_PRESERVES_OR_ADDS_WRITE_REQUEST_LEMMA:
!device_characteristics memory internal_state1 internal_state2 channel1 channel2 channel_id request environment.
  (internal_state2, channel2) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1 /\
  MEM request (channel_pending_requests channel2.pending_accesses.requests)
  ==>
  MEM request (channel_pending_requests channel1.pending_accesses.requests) \/
  ?write_addresses write_address_bytes tag released_bds.
    write_addresses = (cverification device_characteristics channel_id).write_back_bd_addresses environment internal_state1 channel1.queue.bds_to_write_back /\
    CONSISTENT_BD_WRITE device_characteristics memory internal_state1 write_addresses /\
    (internal_state2, write_address_bytes, tag, released_bds) = (coperation device_characteristics channel_id).write_back_bd environment internal_state1 channel1.queue.bds_to_write_back /\
    request = request_write write_address_bytes tag
Proof
INTRO_TAC THEN
ETAC operationsTheory.channel_pending_requests THEN
IRTAC WRITING_BACK_BD_L3_PRESERVES_OR_ADDS_CONSISTENT_WRITE_REQUEST_LEMMA THEN
ALL_LRTAC THEN
ETAC listTheory.MEM_APPEND THEN
SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
AXTAC THEN
LRTAC THEN
LRTAC THEN
ETAC listTheory.MEM_APPEND THEN
SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
ETAC listTheory.MEM THEN
REMOVE_F_DISJUNCTS_TAC THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
PAXTAC THEN
STAC
QED

Theorem WRITING_BACK_BD_L3_UPDATE_DEVICE_STATE_IMPLIES_ADDED_UPDATE_WRITE_REQUEST_LEMMA:
!device_characteristics memory channel_id device1 device2 internal_state1 internal_state2 channel1 channel2 request environment.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channel1 = schannel device1 channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  MEM request (channel_requests device_characteristics device2)
  ==>
  MEM request (channel_requests device_characteristics device1) \/
  ?write_addresses write_address_bytes tag released_bds.
    write_addresses = (cverification device_characteristics channel_id).write_back_bd_addresses environment internal_state1 channel1.queue.bds_to_write_back /\
    CONSISTENT_BD_WRITE device_characteristics memory internal_state1 write_addresses /\
    (internal_state2, write_address_bytes, tag, released_bds) = (coperation device_characteristics channel_id).write_back_bd environment internal_state1 channel1.queue.bds_to_write_back /\
    request = request_write write_address_bytes tag
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
 IRTAC WRITING_BACK_BD_L3_PRESERVES_OR_ADDS_WRITE_REQUEST_LEMMA THEN
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

Theorem WRITING_BACK_L3_UPDATING_INTERNAL_STATE_LEMMA:
!device_characteristics channel_id memory environment internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1
  ==>
  internal_state2 = internal_state1 \/
  ?write_addresses write_address_bytes tag released_bds.
    write_addresses = (cverification device_characteristics channel_id).write_back_bd_addresses environment internal_state1 channel1.queue.bds_to_write_back /\
    CONSISTENT_BD_WRITE device_characteristics memory internal_state1 write_addresses /\
    (internal_state2, write_address_bytes, tag, released_bds) = (coperation device_characteristics channel_id).write_back_bd environment internal_state1 channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC writing_back_bd_l3 THEN EQ_PAIR_ASM_TAC THEN RLTAC THENL
[
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN PAXTAC THEN STAC
 ,
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN PAXTAC THEN STAC
 ,
 STAC
]
QED

Theorem WRITING_BACK_BD_L3_IMPLIES_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 environment.
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1
  ==>
  BDS_TO_FETCH_EQ device_characteristics memory internal_state1 internal_state2
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
Cases_on ‘channel_id = channel_id'’ THENL
[
 IRTAC writing_back_bd_lemmasTheory.WRITING_BACK_BD_L3_PRESERVES_BDS_TO_FETCH_LEMMA THEN
 RLTAC THEN
 ETAC stateTheory.BDS_TO_FETCH_EQ THEN
 AIRTAC THEN
 STAC
 ,
 PTAC writing_back_bd_l3 THENL
 [
  EQ_PAIR_ASM_TAC THEN
  NRLTAC 2 THEN
  ETAC bd_queuesTheory.CONSISTENT_BD_WRITE THEN
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL THEN
  FAIRTAC THEN
  AIRTAC THEN
  STAC
  ,
  EQ_PAIR_ASM_TAC THEN
  NRLTAC 2 THEN
  ETAC bd_queuesTheory.CONSISTENT_BD_WRITE THEN
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST THEN
  IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
  FAIRTAC THEN
  AIRTAC THEN
  STAC
  ,
  EQ_PAIR_ASM_TAC THEN STAC
 ]
]
QED

Theorem UPDATE_DEVICE_STATE_ID_LEMMA:
!device_characteristics device1 device2 channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  DEFINED_CHANNELS device_characteristics device1 /\
  device2 = update_device_state device1 channel_id device1.dma_state.internal_state (schannel device1 channel_id)
  ==>
  device2 = device1
Proof
INTRO_TAC THEN
PTAC operationsTheory.update_device_state THEN
LRTAC THEN
ETAC stateTheory.device_state_type_component_equality THEN
RECORD_TAC THEN
ETAC stateTheory.dma_state_type_component_equality THEN
RECORD_TAC THEN
REWRITE_TAC [combinTheory.UPDATE_def, boolTheory.FUN_EQ_THM] THEN
GEN_TAC THEN
APP_SCALAR_TAC THEN
ETAC stateTheory.schannel THEN
IF_SPLIT_TAC THENL
[
 LRTAC THEN
 ETAC stateTheory.DEFINED_CHANNELS THEN
 ETAC stateTheory.VALID_CHANNELS THEN
 AIRTAC THEN
 PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
 RECORD_TAC THEN
 LRTAC THEN
 REWRITE_TAC [optionTheory.THE_DEF]
 ,
 STAC
]
QED

Theorem CONSISTENT_BD_WRITE_IMPLIES_CONSISTENT_DMA_WRITE_LEMMA:
!device_characteristics memory channel_id internal_state1 internal_state2 write_addresses
 address_bytes tag request_was bds_to_write_back released_bds environment.
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_WRITES_DECLARED device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  write_addresses = (cverification device_characteristics channel_id).write_back_bd_addresses environment internal_state1 bds_to_write_back /\
  (internal_state2, address_bytes, tag, released_bds) = (coperation device_characteristics channel_id).write_back_bd environment internal_state1 bds_to_write_back /\
  MAP FST address_bytes = request_was /\
  CONSISTENT_BD_WRITE device_characteristics memory internal_state1 write_addresses
  ==>
  CONSISTENT_DMA_WRITE device_characteristics memory internal_state2 request_was
Proof
INTRO_TAC THEN
PTAC bd_queuesTheory.CONSISTENT_DMA_WRITE THEN
INTRO_TAC THEN
PTAC bd_queuesTheory.CONSISTENT_BD_WRITE THEN
PTAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
INTRO_TAC THEN
Cases_on ‘channel_id = channel_id'’ THENL
[
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST THEN
 AITAC THEN
 AITAC THEN
 QLRTAC THEN
 ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
 AITAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_WRITE_BACK_WRITES_DECLARED THEN
 AIRTAC THEN
 LRTAC THEN
 LRTAC THEN
 IRTAC lists_lemmasTheory.LIST1_IN_LIST2_PRESERVES_DISJOINTNESS_LEMMA THEN
 STAC
 ,
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST THEN
 FAITAC THEN
 AITAC THEN
 ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
 AIRTAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_WRITE_BACK_WRITES_DECLARED THEN
 AIRTAC THEN
 LRTAC THEN
 IRTAC lists_lemmasTheory.LIST1_IN_LIST2_PRESERVES_DISJOINTNESS_LEMMA THEN
 STAC
]
QED

Theorem WRITING_BACK_BD_L3_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id environment.
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_WRITES_DECLARED device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  DEFINED_CHANNELS device_characteristics device1 /\
  channel1 = schannel device1 channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1 /\
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
ITAC WRITING_BACK_BD_L3_UPDATE_DEVICE_STATE_IMPLIES_ADDED_UPDATE_WRITE_REQUEST_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 IRTAC internal_operation_lemmasTheory.WRITE_REQUEST_IN_REQUEST_WRITE_ADDRESSES_LEMMA THEN
 AXTAC THEN
 AIRTAC THEN
 IRTAC WRITING_BACK_BD_L3_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
 IRTAC bd_queues_lemmasTheory.BDS_TO_FETCH_EQ_PRESERVE_CONSISTENT_DMA_WRITE_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 STAC
 ,
 AXTAC THEN
 ETAC stateTheory.interconnect_request_type_11 THEN
 RLTAC THEN
 RLTAC THEN
 IRTAC CONSISTENT_BD_WRITE_IMPLIES_CONSISTENT_DMA_WRITE_LEMMA THEN
 ITAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 RLTAC THEN
 STAC
]
QED



Theorem WRITING_BACK_BD_L3_NOT_ADDING_BDS_LEMMA:
!device_characteristics memory internal_state1 internal_state2 channel1 channel2
 channel_id channel_bd_queues1 channel_bd_queues2 environment.
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1 /\
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
ITAC WRITING_BACK_BD_L3_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
ITAC WRITING_BACK_BD_L3_NOT_ADDING_BDS_TO_PIPELINE_LEMMA THEN
ALL_LRTAC THEN
ETAC listTheory.MEM_APPEND THEN
SPLIT_ASM_DISJS_TAC THEN TRY STAC THENL
[
 ETAC stateTheory.BDS_TO_FETCH_EQ THEN AIRTAC THEN STAC
 ,
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN IRTAC lists_lemmasTheory.LIST1_IN_LIST2_MEM_LIST1_IMPLIES_MEM_LIST2_LEMMA THEN STAC
]
QED

Theorem WRITING_BACK_BD_L3_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA:
!device_characteristics channel_id memory device1 device2 internal_state1 internal_state2 channel1 channel2 environment.
  PROOF_OBLIGATION_WRITE_BACK_PRESERVES_BD_INTERPRETATION device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
IRTAC WRITING_BACK_L3_UPDATING_INTERNAL_STATE_LEMMA THEN
ETAC stateTheory.BD_TRANSFER_RAS_WAS_EQ THEN
SPLIT_ASM_DISJS_TAC THENL
[
 RLTAC THEN LRTAC THEN IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN STAC
 ,
 AXTAC THEN
 ETAC proof_obligationsTheory.PROOF_OBLIGATION_WRITE_BACK_PRESERVES_BD_INTERPRETATION THEN
 AIRTAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 LRTAC THEN
 RLTAC THEN
 INTRO_TAC THEN
 AIRTAC THEN
 STAC
]
QED

Theorem WRITING_BACK_BD_L3_PRESERVES_NOT_DMA_BDS_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id environment.
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_PRESERVES_BD_INTERPRETATION device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channel1 = schannel device1 channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1 /\
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
 FITAC WRITING_BACK_BD_L3_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
 FITAC WRITING_BACK_BD_L3_NOT_ADDING_BDS_LEMMA THEN
 ITAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 RLTAC THEN
 ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_CHANNEL_EQ_LEMMA THEN
 FIRTAC invariant_l3_lemmasTheory.UPDATE_DEVICE_STATE_BDS_TO_FETCH_EQ_NOT_ADDING_BDS_LEMMA THEN
 ITAC invariant_l3_lemmasTheory.CHANNEL_BD_QUEUES_SUBSET_TRANSFERS_MEM_LEMMA THEN
 STAC
 ,
 FIRTAC WRITING_BACK_BD_L3_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA THEN 
 IRTAC invariant_l3_lemmasTheory.BD_TRANSFER_RAS_WAS_PRESERVES_BD_DMA_WRITE_ADDRESSES_LEMMA THEN
 STAC
 ,
 WEAKEN_TAC (fn term => Term.compare (term, “VALID_CHANNEL_ID device_characteristics channel_id_dma_bd”) = EQUAL) THEN
 FITAC WRITING_BACK_BD_L3_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
 FITAC WRITING_BACK_BD_L3_NOT_ADDING_BDS_LEMMA THEN
 ITAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 RLTAC THEN
 ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_CHANNEL_EQ_LEMMA THEN
 FIRTAC invariant_l3_lemmasTheory.UPDATE_DEVICE_STATE_BDS_TO_FETCH_EQ_NOT_ADDING_BDS_LEMMA THEN
 ITAC invariant_l3_lemmasTheory.CHANNEL_BD_QUEUES_SUBSET_TRANSFERS_MEM_LEMMA THEN
 STAC
]
QED




Theorem WRITING_BACK_BD_L3_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id environment.
  channel1 = schannel device1 channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1 /\
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

Theorem WRITING_BACK_BD_L3_PRESERVES_PENDING_ACCESSES_REPLIES_FETCHING_BD_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 device1 device2 environment.
  channel1 = schannel device1 channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1 /\
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
 IRTAC writing_back_bd_lemmasTheory.WRITING_BACK_BD_L3_PRESERVES_BDS_TO_WRITE_BACK_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
 STAC
 ,
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_PENDING_ACCESSES_REPLIES_FETCHING_BD_LEMMA THEN STAC
]
QED

Theorem WRITING_BACK_BD_L3_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id environment.
  PROOF_OBLIGATION_WRITE_BACK_BD_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channel1 = schannel device1 channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device1
  ==>
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_EXTERNAL_FETCH_BD_REPLY THEN
INTRO_TAC THEN
ITAC WRITING_BACK_BD_L3_PRESERVES_PENDING_ACCESSES_REPLIES_FETCHING_BD_LEMMA THEN
QLRTAC THEN
ITAC WRITING_BACK_L3_UPDATING_INTERNAL_STATE_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN RLTAC THEN RLTAC THEN RLTAC THEN AIRTAC THEN STAC
 ,
 AXTAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_WRITE_BACK_BD_PRESERVES_FETCH_BD_ADDRESSES THEN
 FAIRTAC THEN
 AITAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 RLTAC THEN
 AIRTAC THEN
 STAC
]
QED

Theorem WRITING_BACK_BD_L3_PRESERVES_PENDING_ACCESSES_REQUESTS_FETCHING_BD_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 device1 device2 environment.
  channel1 = schannel device1 channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1 /\
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
 IRTAC writing_back_bd_lemmasTheory.WRITING_BACK_BD_L3_PRESERVES_BDS_TO_WRITE_BACK_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
 STAC
 ,
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_PENDING_ACCESSES_REQUESTS_FETCHING_BD_LEMMA THEN STAC
]
QED

Theorem WRITING_BACK_BD_L3_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id environment.
  PROOF_OBLIGATION_WRITE_BACK_BD_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channel1 = schannel device1 channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device1
  ==>
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES THEN
INTRO_TAC THEN
ITAC WRITING_BACK_BD_L3_PRESERVES_PENDING_ACCESSES_REQUESTS_FETCHING_BD_LEMMA THEN
QLRTAC THEN
IRTAC WRITING_BACK_L3_UPDATING_INTERNAL_STATE_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 RLTAC THEN
 RLTAC THEN
 RLTAC THEN
 AIRTAC THEN
 STAC
 ,
 AXTAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_WRITE_BACK_BD_PRESERVES_FETCH_BD_ADDRESSES THEN
 FAIRTAC THEN
 AITAC THEN 
 IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 RLTAC THEN
 AIRTAC THEN
 STAC
]
QED

Theorem WRITING_BACK_BD_L3_PRESERVES_INVARIANT_BDS_TO_FETCH_DISJOINT_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id environment.
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  (internal_state2, channel2) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1 /\
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device1
  ==>
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device2
Proof
INTRO_TAC THEN
ITAC WRITING_BACK_BD_L3_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
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

Theorem WRITING_BACK_BD_L3_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id environment.
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_WRITES_DECLARED device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_BD_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  DEFINED_CHANNELS device_characteristics device1 /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  INVARIANT_CONCRETE_L3 device_characteristics memory device1
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_CONCRETE_L3 THEN
ITAC WRITING_BACK_BD_L3_PRESERVES_INVARIANT_BDS_TO_FETCH_DISJOINT_LEMMA THEN
ITAC WRITING_BACK_BD_L3_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA THEN
ITAC WRITING_BACK_BD_L3_PRESERVES_NOT_DMA_BDS_LEMMA THEN
ITAC WRITING_BACK_BD_L3_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA THEN
ITAC WRITING_BACK_BD_L3_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA THEN
ITAC WRITING_BACK_BD_L3_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA THEN
STAC
QED

val _ = export_theory();

