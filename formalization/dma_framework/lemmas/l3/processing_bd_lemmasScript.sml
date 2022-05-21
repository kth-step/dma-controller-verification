open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory;

val _ = new_theory "processing_bd_lemmas";

Theorem TRANSFERRING_DATA_UPDATE_QS_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA:
!channel1 channel2 bd bds.
  channel2 = transferring_data_update_qs channel1 bd bds
  ==>
  channel2.queue.bds_to_fetch = channel1.queue.bds_to_fetch /\
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.pending_accesses.replies.fetching_bd = channel1.pending_accesses.replies.fetching_bd /\
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_update_qs THEN
PTAC operationsTheory.update_channel_qs THEN
PTAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA:
!device_characteristics channel_id channel1 channel2 bd internal_state1 internal_state2 new_requests complete.
  (internal_state2, channel2, new_requests, complete) = transferring_data_replies_requests
          channel1.pending_accesses.replies.transferring_data
          (coperation device_characteristics channel_id).process_replies_generate_requests internal_state1 channel1 bd        
  ==>
  channel2.queue.bds_to_fetch = channel1.queue.bds_to_fetch /\
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.pending_accesses.replies.fetching_bd = channel1.pending_accesses.replies.fetching_bd /\
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_replies_requests THEN
EQ_PAIR_ASM_TAC THEN
PTAC operationsTheory.transferring_data_clear_replies THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA:
!channel1 channel2 new_requests.
  channel2 = transferring_data_append_requests channel1 new_requests
  ==>
  channel2.queue.bds_to_fetch = channel1.queue.bds_to_fetch /\
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.pending_accesses.replies.fetching_bd = channel1.pending_accesses.replies.fetching_bd /\
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_append_requests THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem PROCESSING_BD_L2_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA:
!device_characteristics channel_id memory channel1 channel2 internal_state1 internal_state2.
  (internal_state2, channel2) = transferring_data_l2 device_characteristics channel_id memory internal_state1 channel1
  ==>
  channel2.queue.bds_to_fetch = channel1.queue.bds_to_fetch /\
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.pending_accesses.replies.fetching_bd = channel1.pending_accesses.replies.fetching_bd /\
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC l2Theory.transferring_data_l2 THEN EQ_PAIR_ASM_TAC THEN RLTAC THENL
[
 IRTAC TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
 IF_SPLIT_TAC THENL
 [
  IRTAC TRANSFERRING_DATA_UPDATE_QS_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
  ALL_LRTAC THEN
  STAC
  ,
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
  ALL_LRTAC THEN
 STAC
 ]
 ,
 IRTAC TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
 IF_SPLIT_TAC THENL
 [
  IRTAC TRANSFERRING_DATA_UPDATE_QS_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
  ALL_LRTAC THEN
  STAC
  ,
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
  ALL_LRTAC THEN
 STAC
 ]
 ,
 STAC
]
QED

Theorem PROCESSING_BD_L3_PRESERVES_BDS_TO_UPDATE_REPLIES_REQUESTS_FETCH_UPDATE_WRITE_BACK_LEMMA:
!device_characteristics channel_id memory channel1 channel2 internal_state1 internal_state2.
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.pending_accesses.replies.fetching_bd = channel1.pending_accesses.replies.fetching_bd /\
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC l3Theory.transferring_data_l3 THEN EQ_PAIR_ASM_TAC THEN RLTAC THENL
[
 IRTAC TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
 IF_SPLIT_TAC THENL
 [
  IRTAC TRANSFERRING_DATA_UPDATE_QS_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
  ALL_LRTAC THEN
  STAC
  ,
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
  ALL_LRTAC THEN
 STAC
 ]
 ,
 IRTAC TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
 IF_SPLIT_TAC THENL
 [
  IRTAC TRANSFERRING_DATA_UPDATE_QS_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
  ALL_LRTAC THEN
  STAC
  ,
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
  ALL_LRTAC THEN
 STAC
 ]
 ,
 STAC
]
QED

Theorem TRANSFERRING_DATA_CLEAR_REPLIES_BSIM_BDS_TO_PROCESS_WRITE_BACK_PENDING_ACCESSES_TRANSFERRING_DATA_LEMMA:
!channel1a channel1b channel2a channel2b.
  channel1a.queue.bds_to_process = channel1b.queue.bds_to_process /\
  channel1a.queue.bds_to_write_back = channel1b.queue.bds_to_write_back /\
  channel1a.pending_accesses.requests.transferring_data = channel1b.pending_accesses.requests.transferring_data /\
  channel2a = transferring_data_clear_replies channel1a /\
  channel2b = transferring_data_clear_replies channel1b
  ==>
  channel2a.queue.bds_to_process = channel2b.queue.bds_to_process /\
  channel2a.queue.bds_to_write_back = channel2b.queue.bds_to_write_back /\
  channel2a.pending_accesses.replies.transferring_data = channel2b.pending_accesses.replies.transferring_data /\
  channel2a.pending_accesses.requests.transferring_data = channel2b.pending_accesses.requests.transferring_data
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_clear_replies THEN PTAC operationsTheory.transferring_data_clear_replies THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem TRANSFERRING_DATA_REPLIES_REQUESTS_BSIM_BDS_TO_PROCESS_WRITE_BACK_PENDING_ACCESSES_TRANSFERRING_DATA_LEMMA:
!device_characteristics channel_id p bd channel1a channel1b channel2a channel2b
 internal_state1 internal_statea internal_stateb new_requestsa new_requestsb completea completeb.
  p = (coperation device_characteristics channel_id).process_replies_generate_requests /\
  channel1a.queue.bds_to_process = channel1b.queue.bds_to_process /\
  channel1a.queue.bds_to_write_back = channel1b.queue.bds_to_write_back /\
  channel1a.pending_accesses.replies.transferring_data = channel1b.pending_accesses.replies.transferring_data /\
  channel1a.pending_accesses.requests.transferring_data = channel1b.pending_accesses.requests.transferring_data /\
  transferring_data_replies_requests channel1a.pending_accesses.replies.transferring_data p internal_state1 channel1a bd =
  (internal_statea, channel2a, new_requestsa, completea) /\
  transferring_data_replies_requests channel1b.pending_accesses.replies.transferring_data p internal_state1 channel1b bd =
  (internal_stateb, channel2b, new_requestsb, completeb)
  ==>
  (internal_statea, new_requestsa, completea) = (internal_stateb, new_requestsb, completeb) /\
  channel2a.queue.bds_to_process = channel2b.queue.bds_to_process /\
  channel2a.queue.bds_to_write_back = channel2b.queue.bds_to_write_back /\
  channel2a.pending_accesses.replies.transferring_data = channel2b.pending_accesses.replies.transferring_data /\
  channel2a.pending_accesses.requests.transferring_data = channel2b.pending_accesses.requests.transferring_data
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_replies_requests THEN PTAC operationsTheory.transferring_data_replies_requests THEN
EQ_PAIR_ASM_TAC THEN
ALL_RLTAC THEN
REWRITE_TAC [] THEN
MATCH_MP_TAC TRANSFERRING_DATA_CLEAR_REPLIES_BSIM_BDS_TO_PROCESS_WRITE_BACK_PENDING_ACCESSES_TRANSFERRING_DATA_LEMMA THEN
PAXTAC THEN
STAC
QED

Theorem TRANSFERRING_DATA_UPDATE_QS_BSIM_BDS_TO_PROCESS_WRITE_BACK_PENDING_ACCESSES_TRANSFERRING_DATA_LEMMA:
!bd bds channel1a channel1b channel2a channel2b.
  channel1a.queue.bds_to_process = channel1b.queue.bds_to_process /\
  channel1a.queue.bds_to_write_back = channel1b.queue.bds_to_write_back /\
  channel1a.pending_accesses.requests.transferring_data = channel1b.pending_accesses.requests.transferring_data /\
  channel1a.pending_accesses.replies.transferring_data = channel1b.pending_accesses.replies.transferring_data /\
  channel2a = transferring_data_update_qs channel1a bd bds /\
  channel2b = transferring_data_update_qs channel1b bd bds
  ==>
  channel2a.queue.bds_to_process = channel2b.queue.bds_to_process /\
  channel2a.queue.bds_to_write_back = channel2b.queue.bds_to_write_back /\
  channel2a.pending_accesses.requests.transferring_data = channel2b.pending_accesses.requests.transferring_data /\
  channel2a.pending_accesses.replies.transferring_data = channel2b.pending_accesses.replies.transferring_data
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_update_qs THEN PTAC operationsTheory.transferring_data_update_qs THEN
ETAC operationsTheory.update_channel_qs THEN
ETAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem TRANSFERRING_DATA_APPEND_REQUESTS_BSIM_BDS_TO_PROCESS_WRITE_BACK_PENDING_ACCESSES_TRANSFERRING_DATA_LEMMA:
!new_requests channel1a channel1b channel2a channel2b.
  channel1a.queue.bds_to_process = channel1b.queue.bds_to_process /\
  channel1a.queue.bds_to_write_back = channel1b.queue.bds_to_write_back /\
  channel1a.pending_accesses.requests.transferring_data = channel1b.pending_accesses.requests.transferring_data /\
  channel1a.pending_accesses.replies.transferring_data = channel1b.pending_accesses.replies.transferring_data /\
  channel2a = transferring_data_append_requests channel1a new_requests /\
  channel2b = transferring_data_append_requests channel1b new_requests
  ==>
  channel2a.queue.bds_to_process = channel2b.queue.bds_to_process /\
  channel2a.queue.bds_to_write_back = channel2b.queue.bds_to_write_back /\
  channel2a.pending_accesses.requests.transferring_data = channel2b.pending_accesses.requests.transferring_data /\
  channel2a.pending_accesses.replies.transferring_data = channel2b.pending_accesses.replies.transferring_data
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_append_requests THEN PTAC operationsTheory.transferring_data_append_requests THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem PROCESSING_BD_L2_L3_PRESERVES_REQUESTS_PROCESSING_BD_BDS_TO_PROCESS_WRITE_BACK_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2a internal_state2b channel1a channel1b channel2a channel2b.
  (internal_state2a, channel2a) = transferring_data_l2 device_characteristics channel_id memory internal_state1 channel1a /\
  (internal_state2b, channel2b) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1b /\
  channel1a.queue.bds_to_process = channel1b.queue.bds_to_process /\
  channel1a.queue.bds_to_write_back = channel1b.queue.bds_to_write_back /\
  channel1a.pending_accesses.requests.transferring_data = channel1b.pending_accesses.requests.transferring_data /\
  channel1a.pending_accesses.replies.transferring_data = channel1b.pending_accesses.replies.transferring_data
  ==>
  internal_state2a = internal_state2b /\
  channel2a.queue.bds_to_process = channel2b.queue.bds_to_process /\
  channel2a.queue.bds_to_write_back = channel2b.queue.bds_to_write_back /\
  channel2a.pending_accesses.requests.transferring_data = channel2b.pending_accesses.requests.transferring_data /\
  channel2a.pending_accesses.replies.transferring_data = channel2b.pending_accesses.replies.transferring_data
Proof
INTRO_TAC THEN
ETAC l2Theory.transferring_data_l2 THEN ETAC l3Theory.transferring_data_l3 THEN
SPLIT_SCALAR_CASE_KEEP_EQ_TAC THEN SPLIT_SCALAR_CASE_KEEP_EQ_TAC THENL
[
 EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN STAC
 ,
 HYP_CONTR_NEQ_LEMMA_TAC listTheory.NOT_CONS_NIL
 ,
 HYP_CONTR_NEQ_LEMMA_TAC listTheory.NOT_CONS_NIL
 ,
 ALL_TAC
] THEN
CASE_VECTOR_TAC THEN
ETAC listTheory.CONS_11 THEN EQ_PAIR_ASM_TAC THEN
RLTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN
LETS_TAC THEN
RLTAC THEN
IRTAC TRANSFERRING_DATA_REPLIES_REQUESTS_BSIM_BDS_TO_PROCESS_WRITE_BACK_PENDING_ACCESSES_TRANSFERRING_DATA_LEMMA THEN
EQ_PAIR_ASM_TAC THEN
LRTAC THEN
LRTAC THEN
LRTAC THEN
IF_SPLIT_TAC THENL
[
 IRTAC TRANSFERRING_DATA_UPDATE_QS_BSIM_BDS_TO_PROCESS_WRITE_BACK_PENDING_ACCESSES_TRANSFERRING_DATA_LEMMA THEN
 IF_SPLIT_TAC THEN EQ_PAIR_ASM_TAC THENL
 [
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_BSIM_BDS_TO_PROCESS_WRITE_BACK_PENDING_ACCESSES_TRANSFERRING_DATA_LEMMA THEN STAC
  ,
  STAC
 ]
 ,
 IF_SPLIT_TAC THEN EQ_PAIR_ASM_TAC THENL
 [
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_BSIM_BDS_TO_PROCESS_WRITE_BACK_PENDING_ACCESSES_TRANSFERRING_DATA_LEMMA THEN STAC
  ,
  STAC
 ]
]
QED

Theorem TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id internal_state1 internal_state2 channel1 channel2 new_requests complete bd replies memory.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2, new_requests, complete) =
  transferring_data_replies_requests replies
          (coperation device_characteristics channel_id).process_replies_generate_requests internal_state1 channel1 bd
  ==>
  (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2 =
  (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_replies_requests THEN
EQ_PAIR_ASM_TAC THEN
ALL_RLTAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH THEN
FAITAC THEN
FAIRTAC THEN
STAC
QED

Theorem PROCESSING_BD_L3_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2 =
  (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1
Proof
INTRO_TAC THEN
PTAC l3Theory.transferring_data_l3 THENL
[
 EQ_PAIR_ASM_TAC THEN
 LRTAC THEN
 IRTAC TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_BDS_TO_FETCH_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 LRTAC THEN
 IRTAC TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_BDS_TO_FETCH_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem PENDING_ACCESSES_EQ_IMPLIES_TRANSFERRING_DATA_EQ_LEMMA:
!channel2 channel3.
  channel2.pending_accesses = channel3.pending_accesses
  ==>
  channel2.pending_accesses.requests.transferring_data = channel3.pending_accesses.requests.transferring_data /\
  channel2.pending_accesses.replies.transferring_data = channel3.pending_accesses.replies.transferring_data
Proof
INTRO_TAC THEN
STAC
QED

Theorem PROCESSING_BD_L2_L3_PRESERVES_INTERNAL_STATE_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA:
!device_characteristics channel_id memory concrete_bds1 concrete_bds2
 internal_state1 internal_state32 internal_state22 channel21 channel22 channel31 channel32.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel21 channel31 /\
  concrete_bds1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  concrete_bds2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state32 /\
  (internal_state22, channel22) = transferring_data_l2 device_characteristics channel_id memory internal_state1 channel21 /\
  (internal_state32, channel32) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel31
  ==>
  internal_state32 = internal_state22 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel22 channel32
Proof
INTRO_TAC THEN
ITAC PROCESSING_BD_L2_PRESERVES_BDS_TO_FETCH_UPDATE_REPLIES_REQUESTS_FETCH_PROCESS_WRITE_BACK_LEMMA THEN
ITAC PROCESSING_BD_L3_PRESERVES_BDS_TO_FETCH_LEMMA THEN
ITAC PROCESSING_BD_L3_PRESERVES_BDS_TO_UPDATE_REPLIES_REQUESTS_FETCH_UPDATE_WRITE_BACK_LEMMA THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
ITAC PENDING_ACCESSES_EQ_IMPLIES_TRANSFERRING_DATA_EQ_LEMMA THEN
ITAC PROCESSING_BD_L2_L3_PRESERVES_REQUESTS_PROCESSING_BD_BDS_TO_PROCESS_WRITE_BACK_LEMMA THEN
ALL_LRTAC THEN
REWRITE_TAC [] THEN
ETAC stateTheory.pending_accesses_type_component_equality THEN
ETAC stateTheory.pending_requests_type_component_equality THEN
ETAC stateTheory.pending_replies_type_component_equality THEN
STAC
QED

Theorem PROCESSING_BD_L3_PRESERVES_OTHER_BDS_TO_FETCH_LEMMA:
!internal_state32 channel32 device_characteristics channel_id memory internal_state1 channel31.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  (internal_state32, channel32) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel31
  ==>
  OTHER_BDS_TO_FETCH_EQ device_characteristics channel_id memory internal_state1 internal_state32
Proof
INTRO_TAC THEN
PTAC stateTheory.OTHER_BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
PTAC l3Theory.transferring_data_l3 THENL
[
 EQ_PAIR_ASM_TAC THEN
 PTAC operationsTheory.transferring_data_replies_requests THEN
 EQ_PAIR_ASM_TAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH THEN
 FAIRTAC THEN
 FAIRTAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 PTAC operationsTheory.transferring_data_replies_requests THEN
 EQ_PAIR_ASM_TAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH THEN
 FAIRTAC THEN
 FAIRTAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem PROCESSING_BD_L2_L3_BSIMS_INTERNAL_STATE_CHANNEL_OTHER_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id memory concrete_bds1 concrete_bds2 channel21 channel31 channel22 channel32
 internal_state1 internal_state22 internal_state32.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel21 channel31 /\
  concrete_bds1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  (internal_state22, channel22) = transferring_data_l2 device_characteristics channel_id memory internal_state1 channel21 /\
  (internal_state32, channel32) = transferring_data_l3 device_characteristics channel_id memory internal_state1 channel31 /\
  concrete_bds2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state32
  ==>
  internal_state32 = internal_state22 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel22 channel32 /\
  OTHER_BDS_TO_FETCH_EQ device_characteristics channel_id memory internal_state1 internal_state32
Proof
INTRO_TAC THEN
FITAC PROCESSING_BD_L2_L3_PRESERVES_INTERNAL_STATE_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA THEN
FIRTAC PROCESSING_BD_L3_PRESERVES_OTHER_BDS_TO_FETCH_LEMMA THEN
STAC
QED

val _ = export_theory();

