open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory;

val _ = new_theory "updating_bd_lemmas";

Theorem UPDATING_BD_UPDATE_QS_PRESERVES_BDS_TO_FETCH_WRITE_BACK_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA:
!channel1 channel2 bd bds update_status.
  channel2 = updating_bd_update_qs update_status channel1 bd bds
  ==>
  channel2.queue.bds_to_fetch = channel1.queue.bds_to_fetch /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back /\
  channel2.pending_accesses.replies = channel1.pending_accesses.replies /\
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC operationsTheory.updating_bd_update_qs THEN TRY STAC THEN
PTAC operationsTheory.update_channel_qs THEN
PTAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem UPDATING_BD_APPEND_REQUEST_PRESERVES_BDS_TO_FETCH_WRITE_BACK_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA:
!channel1 channel2 write_address_bytes tag.
  channel2 = updating_bd_append_request channel1 write_address_bytes tag
  ==>
  channel2.queue.bds_to_fetch = channel1.queue.bds_to_fetch /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back /\
  channel2.pending_accesses.replies = channel1.pending_accesses.replies /\
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC operationsTheory.updating_bd_append_request THEN TRY STAC THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem UPDATING_BD_L2_PRESERVES_BDS_TO_FETCH_WRITE_BACK_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA:
!device_characteristics channel_id memory channel1 channel2 internal_state1 internal_state2.
  (internal_state2, channel2) = updating_bd_l2 device_characteristics channel_id memory internal_state1 channel1
  ==>
  channel2.queue.bds_to_fetch = channel1.queue.bds_to_fetch /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back /\
  channel2.pending_accesses.replies = channel1.pending_accesses.replies /\
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC l2Theory.updating_bd_l2 THEN EQ_PAIR_ASM_TAC THEN RLTAC THENL
[
 RLTAC THEN
 IRTAC UPDATING_BD_UPDATE_QS_PRESERVES_BDS_TO_FETCH_WRITE_BACK_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
 STAC
 ,
 IRTAC UPDATING_BD_UPDATE_QS_PRESERVES_BDS_TO_FETCH_WRITE_BACK_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
 IRTAC UPDATING_BD_APPEND_REQUEST_PRESERVES_BDS_TO_FETCH_WRITE_BACK_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
 STAC
 ,
 STAC
 ,
 STAC
]
QED

Theorem UPDATING_BD_L3_PRESERVES_BDS_TO_WRITE_BACK_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA:
!device_characteristics channel_id memory channel1 channel2 internal_state1 internal_state2.
  (internal_state2, channel2) = updating_bd_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back /\
  channel2.pending_accesses.replies = channel1.pending_accesses.replies /\
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC l3Theory.updating_bd_l3 THEN EQ_PAIR_ASM_TAC THEN RLTAC THENL
[
 RLTAC THEN
 IRTAC UPDATING_BD_UPDATE_QS_PRESERVES_BDS_TO_FETCH_WRITE_BACK_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
 STAC
 ,
 IRTAC UPDATING_BD_UPDATE_QS_PRESERVES_BDS_TO_FETCH_WRITE_BACK_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
 IRTAC UPDATING_BD_APPEND_REQUEST_PRESERVES_BDS_TO_FETCH_WRITE_BACK_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
 STAC
 ,
 STAC
 ,
 STAC
]
QED

Theorem UPDATING_BD_UPDATE_QS_PRESERVES_REQUESTS_UPDATING_BD_BDS_TO_UPDATE_PROCESS_LEMMA:
!channel1a channel2a channel1b channel2b bda bdsa bdb bdsb update_status.
  channel1a.pending_accesses.requests.updating_bd = channel1b.pending_accesses.requests.updating_bd /\
  channel1a.queue.bds_to_update = channel1b.queue.bds_to_update /\
  channel1a.queue.bds_to_process = channel1b.queue.bds_to_process /\
  bda::bdsa = channel1a.queue.bds_to_update /\
  bdb::bdsb = channel1b.queue.bds_to_update /\
  channel2a = updating_bd_update_qs update_status channel1a bda bdsa /\
  channel2b = updating_bd_update_qs update_status channel1b bdb bdsb
  ==>
  channel2a.pending_accesses.requests.updating_bd = channel2b.pending_accesses.requests.updating_bd /\
  channel2a.queue.bds_to_update = channel2b.queue.bds_to_update /\
  channel2a.queue.bds_to_process = channel2b.queue.bds_to_process
Proof
INTRO_TAC THEN
PTAC operationsTheory.updating_bd_update_qs THEN PTAC operationsTheory.updating_bd_update_qs THEN TRY STAC THEN
ETAC operationsTheory.update_channel_qs THEN
ETAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
ALL_LRTAC THEN
RECORD_TAC THEN
RLTAC THEN
ETAC listTheory.CONS_11 THEN
STAC
QED

Theorem UPDATING_BD_APPEND_REQUESTS_PRESERVES_REQUESTS_UPDATING_BD_BDS_TO_UPDATE_PROCESS_LEMMA:
!channel1a channel2a channel1b channel2b write_address_bytes tag.
  channel1a.pending_accesses.requests.updating_bd = channel1b.pending_accesses.requests.updating_bd /\
  channel1a.queue.bds_to_update = channel1b.queue.bds_to_update /\
  channel1a.queue.bds_to_process = channel1b.queue.bds_to_process /\
  channel2a = updating_bd_append_request channel1a write_address_bytes tag /\
  channel2b = updating_bd_append_request channel1b write_address_bytes tag
  ==>
  channel2a.pending_accesses.requests.updating_bd = channel2b.pending_accesses.requests.updating_bd /\
  channel2a.queue.bds_to_update = channel2b.queue.bds_to_update /\
  channel2a.queue.bds_to_process = channel2b.queue.bds_to_process
Proof
INTRO_TAC THEN
PTAC operationsTheory.updating_bd_append_request THEN PTAC operationsTheory.updating_bd_append_request THEN TRY STAC THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem UPDATE_BD_EQ_BDS_TO_UPDATE_EQ_LEMMA:
!device_characteristics channel_id internal_state1 channel1a channel1b bda bdsa bdb bdsb
internal_statea write_address_bytesa taga update_statusa
internal_stateb write_address_bytesb tagb update_statusb.
  bda::bdsa = channel1a.queue.bds_to_update /\
  bdb::bdsb = channel1b.queue.bds_to_update /\
  channel1a.queue.bds_to_update = channel1b.queue.bds_to_update /\
  (internal_statea, write_address_bytesa, taga, update_statusa) = (coperation device_characteristics channel_id).update_bd internal_state1 bda /\
  (internal_stateb, write_address_bytesb, tagb, update_statusb) = (coperation device_characteristics channel_id).update_bd internal_state1 bdb
  ==>
  (internal_statea, write_address_bytesa, taga, update_statusa) = (internal_stateb, write_address_bytesb, tagb, update_statusb)
Proof
INTRO_TAC THEN
RLTAC THEN
RLTAC THEN
ETAC listTheory.CONS_11 THEN
LRTAC THEN
RLTAC THEN
STAC
QED

Theorem UPDATING_BD_L2_L3_PRESERVES_REQUESTS_UPDATING_BD_BDS_TO_UPDATE_PROCESS_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2a internal_state2b
 channel1a channel1b channel2a channel2b.
  (internal_state2a, channel2a) = updating_bd_l2 device_characteristics channel_id memory internal_state1 channel1a /\
  (internal_state2b, channel2b) = updating_bd_l3 device_characteristics channel_id memory internal_state1 channel1b /\
  channel1a.queue.bds_to_update = channel1b.queue.bds_to_update /\
  channel1a.queue.bds_to_process = channel1b.queue.bds_to_process /\
  channel1a.pending_accesses.requests.updating_bd = channel1b.pending_accesses.requests.updating_bd
  ==>
  internal_state2a = internal_state2b /\
  channel2a.queue.bds_to_update = channel2b.queue.bds_to_update /\
  channel2a.queue.bds_to_process = channel2b.queue.bds_to_process /\
  channel2a.pending_accesses.requests.updating_bd = channel2b.pending_accesses.requests.updating_bd
Proof
INTRO_TAC THEN
ETAC l2Theory.updating_bd_l2 THEN ETAC l3Theory.updating_bd_l3 THEN
Cases_on ‘channel1a.queue.bds_to_update’ THEN Cases_on ‘channel1b.queue.bds_to_update’ THENL
[
 CASE_PATTERN_TAC THEN EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN STAC
 ,
 HYP_CONTR_NEQ_LEMMA_TAC listTheory.NOT_CONS_NIL
 ,
 HYP_CONTR_NEQ_LEMMA_TAC listTheory.NOT_CONS_NIL
 ,
 ALL_TAC
] THEN
CASE_PATTERN_TAC THEN
Cases_on ‘h’ THEN Cases_on ‘h'’ THEN
Cases_on ‘r’ THEN Cases_on ‘r'’ THEN
CASE_PATTERN_TAC THEN
ETAC listTheory.CONS_11 THEN EQ_PAIR_ASM_TAC THEN
RLTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN
LETS_TAC THEN
IF_SPLIT_TAC THENL
[
 IF_SPLIT_TAC THENL
 [
  EQ_PAIR_ASM_TAC THEN
  ITAC UPDATING_BD_UPDATE_QS_PRESERVES_REQUESTS_UPDATING_BD_BDS_TO_UPDATE_PROCESS_LEMMA THEN
  ALL_LRTAC THEN
  STAC
  ,
  EQ_PAIR_ASM_TAC THEN
  IRTAC UPDATING_BD_UPDATE_QS_PRESERVES_REQUESTS_UPDATING_BD_BDS_TO_UPDATE_PROCESS_LEMMA THEN
  IRTAC UPDATING_BD_APPEND_REQUESTS_PRESERVES_REQUESTS_UPDATING_BD_BDS_TO_UPDATE_PROCESS_LEMMA THEN
  STAC
 ]
 ,
 EQ_PAIR_ASM_TAC THEN
 ITAC UPDATING_BD_UPDATE_QS_PRESERVES_REQUESTS_UPDATING_BD_BDS_TO_UPDATE_PROCESS_LEMMA THEN
 STAC
]
QED

Theorem UPDATING_BD_L3_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = updating_bd_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2 =
  (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1
Proof
INTRO_TAC THEN
PTAC l3Theory.updating_bd_l3 THENL
[
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL THEN
 PTAC bd_queuesTheory.CONSISTENT_BD_WRITE THEN
 AITAC THEN
 AIRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST THEN
 AITAC THEN
 AIRTAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem PENDING_ACCESSES_EQ_IMPLIES_UPDATING_BD_EQ_LEMMA:
!channel2 channel3.
  channel2.pending_accesses = channel3.pending_accesses
  ==>
  channel2.pending_accesses.requests.updating_bd = channel3.pending_accesses.requests.updating_bd
Proof
INTRO_TAC THEN
STAC
QED

Theorem UPDATING_BD_L2_L3_PRESERVES_INTERNAL_STATE_REQUESTS_UPDATING_BD_BDS_TO_UPDATE_PROCESS_LEMMA:
!device_characteristics channel_id memory concrete_bds1 concrete_bds2
 internal_state1 internal_state32 internal_state22 channel21 channel22 channel31 channel32.
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel21 channel31 /\
  concrete_bds1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  concrete_bds2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state32 /\
  (internal_state22, channel22) = updating_bd_l2 device_characteristics channel_id memory internal_state1 channel21 /\
  (internal_state32, channel32) = updating_bd_l3 device_characteristics channel_id memory internal_state1 channel31
  ==>
  internal_state32 = internal_state22 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel22 channel32
Proof
INTRO_TAC THEN
ITAC UPDATING_BD_L2_PRESERVES_BDS_TO_FETCH_WRITE_BACK_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
ITAC UPDATING_BD_L3_PRESERVES_BDS_TO_FETCH_LEMMA THEN
ITAC UPDATING_BD_L3_PRESERVES_BDS_TO_WRITE_BACK_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
ITAC PENDING_ACCESSES_EQ_IMPLIES_UPDATING_BD_EQ_LEMMA THEN
ITAC UPDATING_BD_L2_L3_PRESERVES_REQUESTS_UPDATING_BD_BDS_TO_UPDATE_PROCESS_LEMMA THEN
ALL_LRTAC THEN
REWRITE_TAC [] THEN
ETAC stateTheory.pending_accesses_type_component_equality THEN
ALL_LRTAC THEN
REWRITE_TAC [] THEN
ETAC stateTheory.pending_requests_type_component_equality THEN
STAC
QED

Theorem UPDATING_BD_L3_PRESERVES_OTHER_BDS_TO_FETCH_LEMMA:
!internal_state32 channel32 device_characteristics channel_id memory internal_state1 channel31.
(*  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_OTHER_BD_QUEUES_INTERNAL device_characteristics /\*)
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state32, channel32) = updating_bd_l3 device_characteristics channel_id memory internal_state1 channel31
  ==>
  OTHER_BDS_TO_FETCH_EQ device_characteristics channel_id memory internal_state1 internal_state32
Proof
INTRO_TAC THEN
PTAC stateTheory.OTHER_BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
PTAC l3Theory.updating_bd_l3 THENL
[
 EQ_PAIR_ASM_TAC THEN
 PTAC bd_queuesTheory.CONSISTENT_BD_WRITE THEN
(* PTAC proof_obligationsTheory.PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_OTHER_BD_QUEUES_INTERNAL THEN*)
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL THEN
 FAIRTAC THEN
 AIRTAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST THEN
 FAIRTAC THEN
 FAIRTAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC 
]
QED

Theorem UPDATING_BD_L2_L3_BSIMS_INTERNAL_STATE_CHANNEL_OTHER_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id memory concrete_bds1 concrete_bds2
 channel21 channel31 channel22 channel32 internal_state1 internal_state22 internal_state32.
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
(*  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_OTHER_BD_QUEUES_INTERNAL device_characteristics /\*)
  VALID_CHANNEL_ID device_characteristics channel_id /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel21 channel31 /\
  concrete_bds1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  concrete_bds2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state32 /\
  (internal_state22, channel22) = updating_bd_l2 device_characteristics channel_id memory internal_state1 channel21 /\
  (internal_state32, channel32) = updating_bd_l3 device_characteristics channel_id memory internal_state1 channel31
  ==>
  internal_state32 = internal_state22 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel22 channel32 /\
  OTHER_BDS_TO_FETCH_EQ device_characteristics channel_id memory internal_state1 internal_state32
Proof
INTRO_TAC THEN
FITAC UPDATING_BD_L2_L3_PRESERVES_INTERNAL_STATE_REQUESTS_UPDATING_BD_BDS_TO_UPDATE_PROCESS_LEMMA THEN
IRTAC UPDATING_BD_L3_PRESERVES_OTHER_BDS_TO_FETCH_LEMMA THEN
STAC
QED

Theorem UPDATING_BD_UPDATE_QS_PRESERVES_PENDING_ACCESSES_LEMMA:
!channel1 channel2 bd bds update_status.
  channel2 = updating_bd_update_qs update_status channel1 bd bds
  ==>
  channel2.pending_accesses = channel1.pending_accesses
Proof
INTRO_TAC THEN
PTAC operationsTheory.updating_bd_update_qs THEN TRY STAC THEN
PTAC operationsTheory.update_channel_qs THEN
PTAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED





Theorem UPDATING_BD_UPDATE_QS_SHIFTS_BDS_TO_UPDATE_PROCESS_LEMMA:
!channel1 channel2 bd bds update_status.
  channel1.queue.bds_to_update = bd::bds /\
  channel2 = updating_bd_update_qs update_status channel1 bd bds
  ==>
  (channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
   channel2.queue.bds_to_process = channel1.queue.bds_to_process) \/
  (channel1.queue.bds_to_update = bd::bds /\
   channel2.queue.bds_to_update = bds /\
   channel2.queue.bds_to_process = channel1.queue.bds_to_process ++ [bd])
Proof
INTRO_TAC THEN
PTAC operationsTheory.updating_bd_update_qs THEN TRY STAC THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
ALL_LRTAC THEN
REWRITE_TAC [listTheory.TL, listTheory.HD] THEN
ETAC operationsTheory.update_channel_qs THEN
ETAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
RECORD_TAC THEN
STAC
QED

Theorem UPDATING_BD_UPDATE_QS_PRESERVES_BDS_TO_WRITE_BACK_LEMMA:
!channel1 channel2 update_status bd bds.
  channel2 = updating_bd_update_qs update_status channel1 bd bds
  ==>
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC operationsTheory.updating_bd_update_qs THEN TRY STAC THEN
LRTAC THEN
ETAC operationsTheory.update_channel_qs THEN
ETAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
RECORD_TAC THEN
STAC
QED

Theorem UPDATING_BD_APPEND_REQUEST_PRESERVES_BDS_TO_UPDATE_PROCESS_WRITE_BACK_LEMMA:
!channel1 channel2 write_address_bytes tag.
  channel2 = updating_bd_append_request channel1 write_address_bytes tag
  ==>
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC operationsTheory.updating_bd_append_request THEN TRY STAC THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

val _ = export_theory();

