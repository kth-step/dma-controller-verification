open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory;
open operationsTheory;

val _ = new_theory "writing_back_bd_suboperations_lemmas";

Theorem WRITING_BACK_BD_REMOVE_RELEASED_BDS_PRESERVES_REQUESTS_LEMMA:
!channel1 channel2 released_bd_ras_wass.
  channel2 = writing_back_bd_remove_released_bds channel1 released_bd_ras_wass
  ==>
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC writing_back_bd_remove_released_bds THEN
ITAC updating_bd_suboperations_lemmasTheory.UPDATE_QS_PRESERVES_PENDING_ACCESSES_LEMMA THEN
STAC
QED

Theorem WRITING_BACK_BD_APPEND_REQUEST_APPEND_REQUEST_LEMMA:
!channel1 channel2 address_bytes tag request.
  channel2 = writing_back_bd_append_request channel1 address_bytes tag /\
  MEM request channel2.pending_accesses.requests.writing_back_bd
  ==>
  MEM request channel1.pending_accesses.requests.writing_back_bd \/
  request = request_write address_bytes tag
Proof
INTRO_TAC THEN
PTAC writing_back_bd_append_request THENL
[
 LRTAC THEN
 STAC
 ,
 LRTAC THEN
 RECORD_TAC THEN
 ETAC listTheory.MEM_APPEND THEN
 ETAC listTheory.MEM THEN
 REMOVE_F_DISJUNCTS_TAC THEN
 STAC
]
QED

Theorem WRITING_BACK_BD_REMOVE_RELEASED_BDS_PRESERVES_FETCHING_UPDATING_TRANSFERRING_DATA_LEMMA:
!channel1 channel2 released_bd_ras_wass.
  channel2 = writing_back_bd_remove_released_bds channel1 released_bd_ras_wass
  ==>
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data
Proof
INTRO_TAC THEN
PTAC writing_back_bd_remove_released_bds THEN
ITAC updating_bd_suboperations_lemmasTheory.UPDATE_QS_PRESERVES_PENDING_ACCESSES_LEMMA THEN
STAC
QED

Theorem WRITING_BACK_BD_APPEND_REQUEST_PRESERVES_FETCHING_UPDATING_TRANSFERRING_DATA_LEMMA:
!channel1 channel2 address_bytes tag.
  channel2 = writing_back_bd_append_request channel1 address_bytes tag
  ==>
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data
Proof
INTRO_TAC THEN
PTAC writing_back_bd_append_request THENL
[
 STAC
 ,
 LRTAC THEN
 RECORD_TAC THEN
 REWRITE_TAC []
]
QED

val _ = export_theory();
