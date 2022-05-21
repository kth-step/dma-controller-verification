open HolKernel Parse boolLib bossLib helper_tactics;
open operationsTheory;
open access_propertiesTheory;

val _ = new_theory "transferring_data_properties_lemmas";

Theorem TRANSFERRING_DATA_REPLIES_REQUESTS_IMPLIES_PENDING_ACCESSES_UNEXPANDED_TRANSFERRING_DATA_LEMMA:
!replies process_replies_generate_requests internal_state1 internal_state2
 channel1 channel2 bd new_requests complete.
  (internal_state2, channel2, new_requests, complete) =
  transferring_data_replies_requests replies process_replies_generate_requests internal_state1 channel1 bd
  ==>
  PENDING_ACCESSES_UNEXPANDED_TRANSFERRING_DATA channel1 channel2
Proof
INTRO_TAC THEN
ETAC PENDING_ACCESSES_UNEXPANDED_TRANSFERRING_DATA THEN
INTRO_TAC THEN
IRTAC transferring_data_suboperations_lemmasTheory.TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_REQUESTS_LEMMA THEN
STAC
QED

Theorem TRANSFERRING_DATA_REPLIES_REQUESTS_IMPLIES_PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA_LEMMA:
!replies process_replies_generate_requests internal_state1 internal_state2
 channel1 channel2 bd new_requests complete.
  (internal_state2, channel2, new_requests, complete) =
  transferring_data_replies_requests replies process_replies_generate_requests internal_state1 channel1 bd
  ==>
  !R W memory. PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA R W memory channel1 channel2
Proof
INTRO_TAC THEN
REPEAT GEN_TAC THEN
ITAC TRANSFERRING_DATA_REPLIES_REQUESTS_IMPLIES_PENDING_ACCESSES_UNEXPANDED_TRANSFERRING_DATA_LEMMA THEN
ETAC PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA THEN
STAC
QED

Theorem TRANSFERRING_DATA_APPEND_REQUESTS_R_W_IMPLIES_CONDITIONALLY_EXPANDED_TRANSFERRING_DATA_LEMMA:
!R W memory channel1 channel2 new_requests.
  channel2 = transferring_data_append_requests channel1 new_requests /\
  READABLE_WRITABLE R W memory new_requests
  ==>
  PENDING_ACCESSES_CONDITIONALLY_EXPANDED_TRANSFERRING_DATA R W memory channel1 channel2
Proof
INTRO_TAC THEN
PTAC transferring_data_append_requests THEN
LRTAC THEN
ETAC PENDING_ACCESSES_CONDITIONALLY_EXPANDED_TRANSFERRING_DATA THEN
RECORD_TAC THEN
INTRO_TAC THEN
ETAC listTheory.MEM_APPEND THEN
SPLIT_ASM_DISJS_TAC THENL
[
 STAC
 ,
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 ITAC access_properties_lemmasTheory.READABLE_WRITABLE_REQUEST_SATISFIES_R_W_CONDITION_LEMMA THEN
 STAC
]
QED

Theorem TRANSFERRING_DATA_APPEND_REQUESTS_R_W_IMPLIES_PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA_LEMMA:
!R W memory channel1 channel2 new_requests.
  channel2 = transferring_data_append_requests channel1 new_requests /\
  READABLE_WRITABLE R W memory new_requests
  ==>
  PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA R W memory channel1 channel2
Proof
INTRO_TAC THEN
ETAC PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA THEN
ITAC TRANSFERRING_DATA_APPEND_REQUESTS_R_W_IMPLIES_CONDITIONALLY_EXPANDED_TRANSFERRING_DATA_LEMMA THEN
STAC
QED

Theorem TRANSFERRING_DATA_UPDATE_QS_IMPLIES_PENDING_ACCESS_UNMODIFIED_TRANSFERRING_DATA_LEMMA:
!channel1 channel2 bd_ras_was bd_ras_wass.
  channel2 = transferring_data_update_qs channel1 bd_ras_was bd_ras_wass
  ==>
  PENDING_ACCESSES_UNMODIFIED_TRANSFERRING_DATA channel1 channel2
Proof
INTRO_TAC THEN
ETAC transferring_data_update_qs THEN
ITAC updating_bd_suboperations_lemmasTheory.UPDATE_QS_PRESERVES_PENDING_ACCESSES_LEMMA THEN
ETAC PENDING_ACCESSES_UNMODIFIED_TRANSFERRING_DATA THEN
STAC
QED

Theorem TRANSFERRING_DATA_UPDATE_QS_IMPLIES_PENDING_ACCESS_RESTRICTED_TRANSFERRING_DATA_LEMMA:
!channel1 channel2 bd_ras_was bd_ras_wass.
  channel2 = transferring_data_update_qs channel1 bd_ras_was bd_ras_wass
  ==>
  !R W memory. PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA R W memory channel1 channel2
Proof
INTRO_TAC THEN
REPEAT GEN_TAC THEN
ETAC PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA THEN
ITAC TRANSFERRING_DATA_UPDATE_QS_IMPLIES_PENDING_ACCESS_UNMODIFIED_TRANSFERRING_DATA_LEMMA THEN
STAC
QED

Theorem TRANSFERRING_DATA_REPLIES_UPDATE_QS_IMPLIES_PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA_LEMMA:
!channel1 channel channel2 internal_state1 internal_state2 replies
 process_replies_generate_requests new_requests complete bd bd_ras_was
 bd_ras_wass.
  (internal_state2, channel, new_requests, complete) = transferring_data_replies_requests replies process_replies_generate_requests internal_state1 channel1 bd /\
  channel2 = transferring_data_update_qs channel bd_ras_was bd_ras_wass
  ==>
  !R W memory. PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA R W memory channel1 channel2
Proof
INTRO_TAC THEN
REPEAT GEN_TAC THEN
ITAC TRANSFERRING_DATA_REPLIES_REQUESTS_IMPLIES_PENDING_ACCESSES_UNEXPANDED_TRANSFERRING_DATA_LEMMA THEN
ITAC TRANSFERRING_DATA_UPDATE_QS_IMPLIES_PENDING_ACCESS_UNMODIFIED_TRANSFERRING_DATA_LEMMA THEN
ITAC access_properties_lemmasTheory.PENDING_ACCESSES_UNEXPANDED_UNMODIFIED_IMPLIES_UNEXPANDED_TRANSFERRING_DATA_LEMMA THEN
ETAC PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA THEN
STAC
QED

val _ = export_theory();

