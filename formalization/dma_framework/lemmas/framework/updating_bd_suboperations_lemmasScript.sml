open HolKernel Parse boolLib bossLib helper_tactics;
open operationsTheory;

val _ = new_theory "updating_bd_suboperations_lemmas";

Theorem UPDATE_QS_PRESERVES_PENDING_ACCESSES_LEMMA:
!channel1 channel2 new_qs.
  channel2 = update_channel_qs channel1 new_qs
  ==>
  channel2.pending_accesses = channel1.pending_accesses
Proof
INTRO_TAC THEN
PTAC update_channel_qs THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem UPDATING_BD_UPDATE_QS_PRESERVES_STATE_LEMMA:
!channel1 channel2 update_status bd_ras_was bd_ras_wass.
  channel2 = updating_bd_update_qs update_status channel1 bd_ras_was bd_ras_wass
  ==>
  channel2.pending_accesses = channel1.pending_accesses
Proof
INTRO_TAC THEN
PTAC updating_bd_update_qs THENL
[
 STAC
 ,
 ITAC UPDATE_QS_PRESERVES_PENDING_ACCESSES_LEMMA THEN
 STAC
]
QED

Theorem UPDATING_BD_UPDATE_QS_PRESERVES_OTHERS_REQUESTS_LEMMA:
!channel1 channel2 update_status bd_ras_was bd_ras_wass.
  channel2 = updating_bd_update_qs update_status channel1 bd_ras_was bd_ras_wass
  ==>
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
ITAC UPDATING_BD_UPDATE_QS_PRESERVES_STATE_LEMMA THEN
STAC
QED

Theorem UPDATING_BD_APPEND_REQUEST_EXTENDS_UPDATING_BD_LEMMA:
!channel1 channel2 address_bytes tag.
  channel2 = updating_bd_append_request channel1 address_bytes tag
  ==>
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd \/
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd ++ [request_write address_bytes tag]
Proof
INTRO_TAC THEN
PTAC updating_bd_append_request THENL
[
 STAC
 ,
 LRTAC THEN
 RECORD_TAC THEN
 STAC
]
QED

Theorem UPDATING_BD_APPEND_REQUEST_NOT_EMPTY_APPENDS_UPDATING_BD_WRITE_REQUEST_LEMMA:
!channel1 channel2 address_byte address_bytes tag.
  channel2 = updating_bd_append_request channel1 (address_byte::address_bytes) tag
  ==>
  channel2.pending_accesses.requests.updating_bd =
  channel1.pending_accesses.requests.updating_bd ++ [request_write (address_byte::address_bytes) tag]
Proof
INTRO_TAC THEN
PTAC updating_bd_append_request THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem UPDATING_BD_APPEND_REQUEST_PRESERVES_OTHERS_REQUESTS_LEMMA:
!channel1 channel2 address_bytes tag.
  channel2 = updating_bd_append_request channel1 address_bytes tag
  ==>
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC updating_bd_append_request THENL
[
 STAC
 ,
 LRTAC THEN
 RECORD_TAC THEN
 STAC
]
QED

val _ = export_theory();
