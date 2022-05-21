open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory;
open operationsTheory;
open proof_obligationsTheory;

val _ = new_theory "transferring_data_suboperations_lemmas";

Theorem TRANSFERRING_DATA_REPLIES_REQUESTS_NEXT_INTERNAL_STATE_LEMMA:
!process_replies_generate_requests internal_state1 channel1 internal_state2 channel2 bd replies new_requests complete.
  (internal_state2, channel2, new_requests, complete) =
  transferring_data_replies_requests replies process_replies_generate_requests internal_state1 channel1 bd
  ==>
  (internal_state2, new_requests, complete) = process_replies_generate_requests internal_state1 bd replies
Proof
INTRO_TAC THEN
PTAC transferring_data_replies_requests THEN
EQ_PAIR_ASM_TAC THEN
STAC
QED

Theorem TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_REQUESTS_LEMMA:
!internal_state1 internal_state2 channel1 channel2 bd replies
 process_replies_generate_requests new_requests complete request.
  (internal_state2, channel2, new_requests, complete) =
  transferring_data_replies_requests replies process_replies_generate_requests internal_state1 channel1 bd /\
  MEM request channel2.pending_accesses.requests.transferring_data
  ==>
  MEM request channel1.pending_accesses.requests.transferring_data
Proof
INTRO_TAC THEN
PTAC transferring_data_replies_requests THEN
EQ_PAIR_ASM_TAC THEN
PTAC transferring_data_clear_replies THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem TRANSFERRING_DATA_APPEND_REQUESTS_LEMMA:
!channel1 channel2 requests request.
  channel2 = transferring_data_append_requests channel1 requests /\
  MEM request channel2.pending_accesses.requests.transferring_data
  ==>
  MEM request channel1.pending_accesses.requests.transferring_data \/
  MEM request requests
Proof
INTRO_TAC THEN
PTAC transferring_data_append_requests THEN
LRTAC THEN
RECORD_TAC THEN
RW_HYP_LEMMA_TAC listTheory.MEM_APPEND THEN
STAC
QED

Theorem TRANSFERRING_DATA_CLEAR_REPLIES_PRESERVES_FETCHING_UPDATING_WRITING_BACK_BD_LEMMA:
!channel1 channel2.
  channel2 = transferring_data_clear_replies channel1
  ==>
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC transferring_data_clear_replies THEN
ASM_REWRITE_TAC [] THEN
WEAKEN_TAC (fn term => true) THEN
RECORD_TAC THEN
REWRITE_TAC []
QED

(*Theorem TRANSFERRING_DATA_REPLIES_PRESERVES_FETCHING_UPDATING_WRITING_BACK_BD_LEMMA:*)
Theorem TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_FETCHING_UPDATING_WRITING_BACK_BD_LEMMA:
!replies process_replies_generate_requests internal_state1 internal_state2 channel1 channel2 bd new_requests complete.
  (internal_state2, channel2, new_requests, complete) =
  transferring_data_replies_requests replies process_replies_generate_requests internal_state1 channel1 bd
  ==>
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC transferring_data_replies_requests THEN
EQ_PAIR_ASM_TAC THEN
ITAC TRANSFERRING_DATA_CLEAR_REPLIES_PRESERVES_FETCHING_UPDATING_WRITING_BACK_BD_LEMMA THEN
STAC
QED

Theorem TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_FETCHING_UPDATING_WRITING_BACK_BD_LEMMA:
!channel1 channel2 requests.
  channel2 = transferring_data_append_requests channel1 requests
  ==>
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC transferring_data_append_requests THEN
ASM_REWRITE_TAC [] THEN
WEAKEN_TAC (fn term => true) THEN
RECORD_TAC THEN
REWRITE_TAC []
QED

Theorem TRANSFERRING_DATA_UPDATE_QS_PRESERVES_FETCHING_UPDATING_WRITING_BACK_BD_LEMMA:
!channel1 channel2 bd bds.
  channel2 = transferring_data_update_qs channel1 bd bds
  ==>
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC transferring_data_update_qs THEN
ITAC updating_bd_suboperations_lemmasTheory.UPDATE_QS_PRESERVES_PENDING_ACCESSES_LEMMA THEN
STAC
QED

(*Theorem TRANSFERRING_DATA_REPLIES_PRESERVES_BD_TRANSFER_RAS_WAS_LEMMA:*)
Theorem TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_BD_TRANSFER_RAS_WAS_LEMMA:
!device_characteristics channel1 channel2 internal_state1 internal_state2 replies
 bd channel_id new_requests complete.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2, new_requests, complete) =
  transferring_data_replies_requests replies (coperation device_characteristics channel_id).process_replies_generate_requests internal_state1 channel1 bd
  ==>
  (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state2 bd =
  (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state1 bd
Proof
INTRO_TAC THEN
PTAC transferring_data_replies_requests THEN
EQ_PAIR_ASM_TAC THEN
ALL_RLTAC THEN
PTAC PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION THEN
FAITAC THEN
FAIRTAC THEN
STAC
QED

val _ = export_theory();
