open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory;

val _ = new_theory "writing_back_bd_lemmas";

Theorem WRITING_BACK_BD_REMOVE_RELEASED_BDS_PRESERVES_BDS_TO_FETCH_WRITE_BACK_REPLIES_REQUESTS_FETCH_UPDATE_PROCESS_LEMMA:
!channel1 channel2 released_bd_ras_wass.
  channel2 = writing_back_bd_remove_released_bds channel1 released_bd_ras_wass
  ==>
  channel2.queue.bds_to_fetch = channel1.queue.bds_to_fetch /\
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  channel2.pending_accesses.replies = channel1.pending_accesses.replies /\
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data
Proof
INTRO_TAC THEN
ETAC operationsTheory.writing_back_bd_remove_released_bds THEN
PTAC operationsTheory.update_channel_qs THEN
PTAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem WRITING_BACK_BD_APPEND_REQUEST_PRESERVES_BDS_TO_FETCH_UPDATE_PROCESS_REPLIES_REQUESTS_FETCH_UPDATE_PROCESS_LEMMA:
!channel1 channel2 write_address_bytes tag.
  channel2 = writing_back_bd_append_request channel1 write_address_bytes tag
  ==>
  channel2.queue.bds_to_fetch = channel1.queue.bds_to_fetch /\
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  channel2.pending_accesses.replies = channel1.pending_accesses.replies /\
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data
Proof
INTRO_TAC THEN
PTAC operationsTheory.writing_back_bd_append_request THEN TRY STAC THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem WRITING_BACK_BD_L2_PRESERVES_BDS_TO_FETCH_UPDATE_PROCESS_REPLIES_REQUESTS_FETCH_UPDATE_PROCESS_LEMMA:
!device_characteristics channel_id memory channel1 channel2 internal_state1 internal_state2 environment.
  (internal_state2, channel2) = writing_back_bd_l2 device_characteristics channel_id memory environment internal_state1 channel1
  ==>
  channel2.queue.bds_to_fetch = channel1.queue.bds_to_fetch /\
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  channel2.pending_accesses.replies = channel1.pending_accesses.replies /\
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data
Proof
INTRO_TAC THEN
PTAC l2Theory.writing_back_bd_l2 THEN EQ_PAIR_ASM_TAC THEN RLTAC THENL
[
 RLTAC THEN
 IRTAC WRITING_BACK_BD_REMOVE_RELEASED_BDS_PRESERVES_BDS_TO_FETCH_WRITE_BACK_REPLIES_REQUESTS_FETCH_UPDATE_PROCESS_LEMMA THEN
 STAC
 ,
 IRTAC WRITING_BACK_BD_REMOVE_RELEASED_BDS_PRESERVES_BDS_TO_FETCH_WRITE_BACK_REPLIES_REQUESTS_FETCH_UPDATE_PROCESS_LEMMA THEN
 IRTAC WRITING_BACK_BD_APPEND_REQUEST_PRESERVES_BDS_TO_FETCH_UPDATE_PROCESS_REPLIES_REQUESTS_FETCH_UPDATE_PROCESS_LEMMA THEN
 STAC
 ,
 STAC
]
QED

Theorem WRITING_BACK_BD_L3_PRESERVES_BDS_TO_WRITE_BACK_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA:
!device_characteristics channel_id memory channel1 channel2 internal_state1 internal_state2 environment.
  (internal_state2, channel2) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1
  ==>
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  channel2.pending_accesses.replies = channel1.pending_accesses.replies /\
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data
Proof
INTRO_TAC THEN
PTAC l3Theory.writing_back_bd_l3 THEN EQ_PAIR_ASM_TAC THEN ALL_RLTAC THENL
[
 IRTAC WRITING_BACK_BD_REMOVE_RELEASED_BDS_PRESERVES_BDS_TO_FETCH_WRITE_BACK_REPLIES_REQUESTS_FETCH_UPDATE_PROCESS_LEMMA THEN STAC
 ,
 IRTAC WRITING_BACK_BD_REMOVE_RELEASED_BDS_PRESERVES_BDS_TO_FETCH_WRITE_BACK_REPLIES_REQUESTS_FETCH_UPDATE_PROCESS_LEMMA THEN
 IRTAC WRITING_BACK_BD_APPEND_REQUEST_PRESERVES_BDS_TO_FETCH_UPDATE_PROCESS_REPLIES_REQUESTS_FETCH_UPDATE_PROCESS_LEMMA THEN
 STAC
 ,
 STAC
]
QED

Theorem WRITING_BACK_BD_REMOVE_RELEASED_BDS_BSIM_BDS_TO_WRITE_BACK_WRITING_BACK_BD_LEMMA:
!channel1a channel1b channel2a channel2b released_bd_ras_wass.
  channel1a.queue.bds_to_write_back = channel1b.queue.bds_to_write_back /\
  channel1a.pending_accesses.requests.writing_back_bd = channel1b.pending_accesses.requests.writing_back_bd /\
  channel2a = writing_back_bd_remove_released_bds channel1a released_bd_ras_wass /\
  channel2b = writing_back_bd_remove_released_bds channel1b released_bd_ras_wass
  ==>
  channel2a.queue.bds_to_write_back = channel2b.queue.bds_to_write_back /\
  channel2a.pending_accesses.requests.writing_back_bd = channel2b.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
ETAC operationsTheory.writing_back_bd_remove_released_bds THEN
ETAC operationsTheory.update_channel_qs THEN
ETAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem WRITING_BACK_BD_APPEND_REQUEST_BSIM_BDS_TO_WRITE_BACK_WRITING_BACK_BD_LEMMA:
!channel1a channel1b channel2a channel2b write_address_bytes tag.
  channel1a.queue.bds_to_write_back = channel1b.queue.bds_to_write_back /\
  channel1a.pending_accesses.requests.writing_back_bd = channel1b.pending_accesses.requests.writing_back_bd /\
  channel2a = writing_back_bd_append_request channel1a write_address_bytes tag /\
  channel2b = writing_back_bd_append_request channel1b write_address_bytes tag
  ==>
  channel2a.queue.bds_to_write_back = channel2b.queue.bds_to_write_back /\
  channel2a.pending_accesses.requests.writing_back_bd = channel2b.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC operationsTheory.writing_back_bd_append_request THEN PTAC operationsTheory.writing_back_bd_append_request THENL
[
 STAC
 ,
 ALL_LRTAC THEN
 RECORD_TAC THEN
 STAC
]
QED

Theorem WRITING_BACK_BD_L2_L3_PRESERVES_REQUESTS_WRITING_BACK_BD_BDS_TO_WRITE_BACK_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2a internal_state2b
 channel1a channel1b channel2a channel2b environment.
  (internal_state2a, channel2a) = writing_back_bd_l2 device_characteristics channel_id memory environment internal_state1 channel1a /\
  (internal_state2b, channel2b) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1b /\
  channel1a.queue.bds_to_write_back = channel1b.queue.bds_to_write_back /\
  channel1a.pending_accesses.requests.writing_back_bd = channel1b.pending_accesses.requests.writing_back_bd
  ==>
  internal_state2a = internal_state2b /\
  channel2a.queue.bds_to_write_back = channel2b.queue.bds_to_write_back /\
  channel2a.pending_accesses.requests.writing_back_bd = channel2b.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
ETAC l2Theory.writing_back_bd_l2 THEN ETAC l3Theory.writing_back_bd_l3 THEN
ASM_LR_RW_OTHERS_KEEP_TAC THEN
LETS_TAC THEN
ITAC WRITING_BACK_BD_REMOVE_RELEASED_BDS_BSIM_BDS_TO_WRITE_BACK_WRITING_BACK_BD_LEMMA THEN
IF_SPLIT_TAC THENL
[
 IF_SPLIT_TAC THENL
 [
  EQ_PAIR_ASM_TAC THEN
  ALL_RLTAC THEN
  STAC
  ,
  EQ_PAIR_ASM_TAC THEN
  ALL_RLTAC THEN
  IRTAC WRITING_BACK_BD_APPEND_REQUEST_BSIM_BDS_TO_WRITE_BACK_WRITING_BACK_BD_LEMMA THEN
  STAC
 ]
 ,
 EQ_PAIR_ASM_TAC THEN
 ALL_RLTAC THEN
 STAC
]
QED

Theorem WRITING_BACK_BD_L3_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 environment.
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel1
  ==>
  (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2 =
  (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1
Proof
INTRO_TAC THEN
PTAC l3Theory.writing_back_bd_l3 THENL
[
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL THEN
 PTAC bd_queuesTheory.CONSISTENT_BD_WRITE THEN
 AITAC THEN
 AITAC THEN
 EQ_PAIR_ASM_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST THEN
 AITAC THEN
 AIRTAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem PENDING_ACCESSES_EQ_IMPLIES_WRITING_BACK_BD_EQ_LEMMA:
!channel2 channel3.
  channel2.pending_accesses = channel3.pending_accesses
  ==>
  channel2.pending_accesses.requests.writing_back_bd = channel3.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
STAC
QED

Theorem WRITING_BACK_BD_L2_L3_PRESERVES_INTERNAL_STATE_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA:
!device_characteristics channel_id memory environment concrete_bds1 concrete_bds2
 internal_state1 internal_state32 internal_state22 channel21 channel22 channel31 channel32.
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel21 channel31 /\
  concrete_bds1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  concrete_bds2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state32 /\
  (internal_state22, channel22) = writing_back_bd_l2 device_characteristics channel_id memory environment internal_state1 channel21 /\
  (internal_state32, channel32) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel31
  ==>
  internal_state32 = internal_state22 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel22 channel32
Proof
INTRO_TAC THEN
ITAC WRITING_BACK_BD_L2_PRESERVES_BDS_TO_FETCH_UPDATE_PROCESS_REPLIES_REQUESTS_FETCH_UPDATE_PROCESS_LEMMA THEN
ITAC WRITING_BACK_BD_L3_PRESERVES_BDS_TO_FETCH_LEMMA THEN
ITAC WRITING_BACK_BD_L3_PRESERVES_BDS_TO_WRITE_BACK_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
ITAC PENDING_ACCESSES_EQ_IMPLIES_WRITING_BACK_BD_EQ_LEMMA THEN
ITAC WRITING_BACK_BD_L2_L3_PRESERVES_REQUESTS_WRITING_BACK_BD_BDS_TO_WRITE_BACK_LEMMA THEN
ALL_LRTAC THEN
REWRITE_TAC [] THEN
ETAC stateTheory.pending_accesses_type_component_equality THEN
ETAC stateTheory.pending_requests_type_component_equality THEN
STAC
QED

Theorem WRITING_BACK_BD_L3_PRESERVES_BDS_TO_FETCH_LEMMA:
!internal_state32 channel32 device_characteristics channel_id memory internal_state1 channel31 environment.
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state32, channel32) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel31
  ==>
  BDS_TO_FETCH_EQ device_characteristics memory internal_state1 internal_state32
Proof
INTRO_TAC THEN
PTAC stateTheory.BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
PTAC l3Theory.writing_back_bd_l3 THENL
[
 EQ_PAIR_ASM_TAC THEN
 ALL_RLTAC THEN
 PTAC bd_queuesTheory.CONSISTENT_BD_WRITE THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL THEN
 FAIRTAC THEN
 FAIRTAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST THEN
 FAIRTAC THEN
 FAIRTAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC 
]
QED

Theorem WRITING_BACK_BD_L2_L3_BSIMS_INTERNAL_STATE_CHANNEL_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id memory environment concrete_bds1 concrete_bds2
 channel21 channel31 channel22 channel32 internal_state1 internal_state22 internal_state32.
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel21 channel31 /\
  concrete_bds1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  (internal_state22, channel22) = writing_back_bd_l2 device_characteristics channel_id memory environment internal_state1 channel21 /\
  (internal_state32, channel32) = writing_back_bd_l3 device_characteristics channel_id memory environment internal_state1 channel31 /\
  concrete_bds2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state32
  ==>
  internal_state32 = internal_state22 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel22 channel32 /\
  BDS_TO_FETCH_EQ device_characteristics memory internal_state1 internal_state32
Proof
INTRO_TAC THEN
FITAC WRITING_BACK_BD_L2_L3_PRESERVES_INTERNAL_STATE_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA THEN
FIRTAC WRITING_BACK_BD_L3_PRESERVES_BDS_TO_FETCH_LEMMA THEN
STAC
QED

val _ = export_theory();

