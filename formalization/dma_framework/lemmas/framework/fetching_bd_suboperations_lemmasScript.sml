open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory;
open operationsTheory;

val _ = new_theory "fetching_bd_suboperations_lemmas";

Theorem FETCHING_BD_CLEAR_REPLY_PRESERVES_PENDING_REQUESTS_LEMMA:
!channel1 channel2.
  channel2 = fetching_bd_clear_reply channel1
  ==>
  channel2.pending_accesses.requests.fetching_bd = NONE /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC fetching_bd_clear_reply THEN
ASM_REWRITE_TAC [] THEN
RECORD_TAC THEN
REWRITE_TAC []
QED

Theorem FETCHING_BD_SET_REQUEST_PRESERVES_REQEUSTS_OR_SETS_FETCHING_BD_REQUEST_LEMMA:
!channel1 channel2 addresses tag.
channel2 = fetching_bd_set_request channel1 addresses tag
==>
channel2.pending_accesses.requests.fetching_bd = SOME (request_read addresses tag) /\
channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data /\
channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC fetching_bd_set_request THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem NO_BDS_TO_FETCH_IMPLIES_MEMORY_LOCATIONS_OF_BD_EQUAL_LEMMA:
!device_characteristics channel_id memory internal_state addresses tag.
  PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (cverification device_characteristics channel_id).bds_to_fetch memory internal_state = [] /\
  (addresses, tag) = (coperation device_characteristics channel_id).fetch_bd_addresses internal_state
  ==>
  !memory1 memory2.
    MAP memory2 addresses = MAP memory1 addresses
Proof
INTRO_TAC THEN
REPEAT GEN_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ THEN
AIRTAC THEN
LRTAC THEN
REWRITE_TAC [listTheory.MAP]
QED

val _ = export_theory();
