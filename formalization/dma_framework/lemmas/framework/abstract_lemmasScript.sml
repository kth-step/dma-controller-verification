open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory abstractTheory;

val _ = new_theory "abstract_lemmas";

Theorem FETCHING_BD_UPDATE_QS_ABSTRACT_PRESERVES_PENDING_ACCESSES_LEMMA:
!channel2 channel1 bd_queue.
  channel2 = fetching_bd_update_qs_abstract channel1 bd_queue
  ==>
  channel2.pending_accesses = channel1.pending_accesses
Proof
INTRO_TAC THEN
PTAC fetching_bd_update_qs_abstract THENL
[
 STAC
 ,
 ITAC updating_bd_suboperations_lemmasTheory.UPDATE_QS_PRESERVES_PENDING_ACCESSES_LEMMA THEN STAC
 ,
 ITAC updating_bd_suboperations_lemmasTheory.UPDATE_QS_PRESERVES_PENDING_ACCESSES_LEMMA THEN STAC
]
QED

Theorem FETCHING_BD_FETCH_BD_ABSTRACT_PRESERVES_PENDING_ACCESSES_LEMMA:
!channel1 channel2 operation_fetch_bd internal_state1 internal_state2 byte_tags.
  (internal_state2, channel2) = fetching_bd_fetch_bd_abstract operation_fetch_bd internal_state1 channel1 byte_tags
  ==>
  channel2.pending_accesses = channel1.pending_accesses
Proof
INTRO_TAC THEN
PTAC fetching_bd_fetch_bd_abstract THENL
[
 EQ_PAIR_ASM_TAC THEN
 ITAC FETCHING_BD_UPDATE_QS_ABSTRACT_PRESERVES_PENDING_ACCESSES_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 STAC
]
QED

val _ = export_theory();

