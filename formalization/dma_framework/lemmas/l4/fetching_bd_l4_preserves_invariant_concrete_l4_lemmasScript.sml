open HolKernel Parse boolLib bossLib helper_tactics;
open l4Theory invariant_l4Theory invariant_l4_lemmasTheory;

val _ = new_theory "fetching_bd_l4_preserves_invariant_concrete_l4_lemmas";

(*******************************************************************************)

Theorem FETCHING_BD_UPDATING_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id internal_state1 internal_state2 channel1 channel2.
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1
  ==>
  (!channel_id memory.
     VALID_CHANNEL_ID device_characteristics channel_id
     ==>
     (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 =
     (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2) \/
  ?fetch_result.
    ((internal_state2, SOME fetch_result) = (coperation device_characteristics channel_id).fetch_bd internal_state1 NONE /\
     INTERNAL_BDS device_characteristics) \/
    (?reply.
       (internal_state2, SOME fetch_result) = (coperation device_characteristics channel_id).fetch_bd internal_state1 (SOME reply) /\
       channel1.pending_accesses.replies.fetching_bd = SOME reply /\
       EXTERNAL_BDS device_characteristics)
Proof
INTRO_TAC THEN
PTAC fetching_bd_l4 THENL
[
 PTAC concreteTheory.fetching_bd_fetch_bd_concrete THENL
 [
  EQ_PAIR_ASM_TAC THEN RLTAC THEN MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN PAXTAC THEN STAC
  ,
  EQ_PAIR_ASM_TAC THEN RLTAC THEN MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN PAXTAC THEN STAC
  ,
  EQ_PAIR_ASM_TAC THEN RLTAC THEN MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
  INTRO_TAC THEN
  Cases_on ‘channel_id = channel_id'’ THENL
  [
   RLTAC THEN PTAC proof_obligationsTheory.PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT THEN AIRTAC THEN STAC
   ,
   PTAC proof_obligationsTheory.PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE THEN FAIRTAC THEN AIRTAC THEN STAC
  ]
 ]
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
 IRTAC fetching_bd_lemmasTheory.NOT_IS_NONE_IMPLIES_EXISTS_SOME_LEMMA THEN
 AXTAC THEN
 LRTAC THEN
 LRTAC THEN
 PTAC concreteTheory.fetching_bd_fetch_bd_concrete THENL
 [
  EQ_PAIR_ASM_TAC THEN
  RLTAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  PAXTAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  PAXTAC THEN STAC
  ,
  EQ_PAIR_ASM_TAC THEN
  RLTAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  PAXTAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  PAXTAC THEN STAC
  ,
  EQ_PAIR_ASM_TAC THEN RLTAC THEN MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
  INTRO_TAC THEN
  Cases_on ‘channel_id = channel_id'’ THENL
  [
   RLTAC THEN PTAC proof_obligationsTheory.PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT THEN AIRTAC THEN STAC
   ,
   PTAC proof_obligationsTheory.PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE THEN FAIRTAC THEN AIRTAC THEN STAC
  ]
 ]
]
QED

Definition INTERNAL_STATE_BDS_TO_FETCH_DISJOINT:
INTERNAL_STATE_BDS_TO_FETCH_DISJOINT device_characteristics memory internal_state =
!bds_to_fetch channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state
  ==>
  BDS_TO_FETCH_DISJOINT bds_to_fetch
End

Theorem FETCHING_BD_L4_IMPLIES_NOT_EXPANDING_BDS_TO_FETCH_LEMMA:
!device_characteristics memory internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  EXTERNAL_BD_ADDRESSES device_characteristics channel_id memory internal_state1 channel1 /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INTERNAL_STATE_BDS_TO_FETCH_DISJOINT device_characteristics memory internal_state1 /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1
  ==>
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory internal_state1 internal_state2
Proof
INTRO_TAC THEN
ETAC BDS_TO_FETCH_NOT_EXPANDED THEN
INTRO_TAC THEN
FITAC FETCHING_BD_UPDATING_BDS_TO_FETCH_LEMMA THEN
SPLIT_ASM_DISJS_TAC THEN TRY (AIRTAC THEN STAC) THEN
AXTAC THEN
SPLIT_ASM_DISJS_TAC THENL
[
 Cases_on ‘channel_id' = channel_id’ THENL
 [
  LRTAC THEN
  FITAC fetching_bd_lemmasTheory.FETCHING_BD_IMPLIES_NON_EMPTY_BDS_TO_FETCH_LEMMA THEN
  PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC (mk_var ("memory", (type_of o #1 o dest_forall o concl) thm)) thm)) THEN AXTAC THEN
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT THEN
  AIRTAC THEN
  PTAC INTERNAL_STATE_BDS_TO_FETCH_DISJOINT THEN
  AITAC THEN
  FAITAC THEN
  RLTAC THEN
  LRTAC THEN
  LRTAC THEN
  LRTAC THEN
  REWRITE_TAC [listTheory.TL, listTheory.NULL]
  ,
  FITAC fetching_bd_lemmasTheory.FETCHING_BD_IMPLIES_NON_EMPTY_BDS_TO_FETCH_LEMMA THEN
  PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC (mk_var ("memory", (type_of o #1 o dest_forall o concl) thm)) thm)) THEN AXTAC THEN
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE THEN
  FAIRTAC THEN
  AIRTAC THEN
  STAC
 ]
 ,
 AXTAC THEN
 Cases_on ‘channel_id' = channel_id’ THENL
 [
  LRTAC THEN
  FITAC fetching_bd_lemmasTheory.FETCHING_BD_IMPLIES_NON_EMPTY_BDS_TO_FETCH_LEMMA THEN
  PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC (mk_var ("memory", (type_of o #1 o dest_forall o concl) thm)) thm)) THEN AXTAC THEN
  ASSUME_TAC (SPEC_ALL fetching_bd_lemmasTheory.FETCH_BD_ADDRESSES_EQ_ADDRESSES_TAG_LEMMA) THEN
  AXTAC THEN
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT THEN
  PTAC invariant_l3Theory.EXTERNAL_BD_ADDRESSES THEN
  AITAC THEN
  NRLTAC 2 THEN
  PTAC INTERNAL_STATE_BDS_TO_FETCH_DISJOINT THEN
  AITAC THEN
  AIRTAC THEN
  FAITAC THEN
  LRTAC THEN
  LRTAC THEN
  LRTAC THEN
  LRTAC THEN
  REWRITE_TAC [listTheory.TL, listTheory.NULL]
  ,
  FITAC fetching_bd_lemmasTheory.FETCHING_BD_IMPLIES_NON_EMPTY_BDS_TO_FETCH_LEMMA THEN
  PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC (mk_var ("memory", (type_of o #1 o dest_forall o concl) thm)) thm)) THEN AXTAC THEN
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE THEN
  FAIRTAC THEN
  AIRTAC THEN
  STAC
 ]
]
QED

Theorem INVARIANT_BDS_TO_FETCH_DISJOINT_IMPLIES_INTERNAL_STATE_BDS_TO_FETCH_DISJOINT_LEMMA:
!device_characteristics memory device1.
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device1
  ==>
  INTERNAL_STATE_BDS_TO_FETCH_DISJOINT device_characteristics memory device1.dma_state.internal_state
Proof
INTRO_TAC THEN
ETAC invariant_l3Theory.INVARIANT_BDS_TO_FETCH_DISJOINT THEN
ETAC INTERNAL_STATE_BDS_TO_FETCH_DISJOINT THEN
STAC
QED

Theorem FETCHING_BD_L4_IMPLIES_BDS_TO_FETCH_NOT_EXPANDED_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device1 /\
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device1 /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
IRTAC INVARIANT_BDS_TO_FETCH_DISJOINT_IMPLIES_INTERNAL_STATE_BDS_TO_FETCH_DISJOINT_LEMMA THEN
ITAC invariant_l3_lemmasTheory.INVARIANT_EXTERNAL_FETCH_BD_REPLY_IMPLIES_EXTERNAL_BD_ADDRESSES_LEMMA THEN
ITAC FETCHING_BD_L4_IMPLIES_NOT_EXPANDING_BDS_TO_FETCH_LEMMA THEN
IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
STAC
QED

(*******************************************************************************)

Theorem FETCHING_BD_L4_PRESERVES_INTERNAL_STATE_OR_FETCHES_PARITAL_BD_OR_FETCHES_COMPLETE_BD_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  EXTERNAL_BD_ADDRESSES device_characteristics channel_id memory internal_state1 channel1 /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1
  ==>
  (EXTERNAL_BDS device_characteristics /\ IS_NONE channel1.pending_accesses.replies.fetching_bd) \/
  (INTERNAL_BDS device_characteristics /\
   (internal_state2, NONE) = (coperation device_characteristics channel_id).fetch_bd internal_state1 NONE) \/
  (EXTERNAL_BDS device_characteristics /\
   (internal_state2, NONE) = (coperation device_characteristics channel_id).fetch_bd internal_state1 channel1.pending_accesses.replies.fetching_bd) \/
  (?bd. INTERNAL_BD_FETCH device_characteristics channel_id internal_state1 internal_state2 bd /\
        EXTERNAL_BD_FETCH device_characteristics memory channel_id internal_state1 channel1 internal_state2 bd)
Proof
INTRO_TAC THEN
PTAC fetching_bd_l4 THENL
[
 PTAC concreteTheory.fetching_bd_fetch_bd_concrete THENL
 [
  REPEAT (MATCH_MP_TAC boolTheory.OR_INTRO_THM2) THEN
  REWRITE_TAC [invariant_l3Theory.EXTERNAL_BD_FETCH] THEN
  ITAC state_lemmasTheory.INTERNAL_BDS_IMPLIES_NOT_EXTERNAL_BDS_LEMMA THEN
  ASM_REWRITE_TAC [invariant_l3Theory.INTERNAL_BD_FETCH] THEN
  EQ_PAIR_ASM_TAC THEN
  RLTAC THEN
  EXISTS_EQ_TAC
  ,
  REPEAT (MATCH_MP_TAC boolTheory.OR_INTRO_THM2) THEN
  REWRITE_TAC [invariant_l3Theory.EXTERNAL_BD_FETCH] THEN
  ITAC state_lemmasTheory.INTERNAL_BDS_IMPLIES_NOT_EXTERNAL_BDS_LEMMA THEN
  ASM_REWRITE_TAC [invariant_l3Theory.INTERNAL_BD_FETCH] THEN
  EQ_PAIR_ASM_TAC THEN
  RLTAC THEN
  EXISTS_EQ_TAC
  ,
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN EQ_PAIR_ASM_TAC THEN STAC
 ]
 ,
 IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN STAC
 ,
 PTAC concreteTheory.fetching_bd_fetch_bd_concrete THENL
 [
  REPEAT (MATCH_MP_TAC boolTheory.OR_INTRO_THM2) THEN
  EQ_PAIR_ASM_TAC THEN
  RLTAC THEN
  ITAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
  REWRITE_TAC [invariant_l3Theory.INTERNAL_BD_FETCH] THEN
  ITAC state_lemmasTheory.EXTERNAL_BDS_IMPLIES_NOT_INTERNAL_BDS_LEMMA THEN
  ASM_REWRITE_TAC [invariant_l3Theory.EXTERNAL_BD_FETCH] THEN
  IRTAC fetching_bd_lemmasTheory.NOT_IS_NONE_IMPLIES_EXISTS_SOME_LEMMA THEN
  AXTAC THEN
  ETAC invariant_l3Theory.EXTERNAL_BD_ADDRESSES THEN
  ASSUME_TAC (SPEC_ALL fetching_bd_lemmasTheory.FETCH_BD_ADDRESSES_EQ_ADDRESSES_TAG_LEMMA) THEN
  AXTAC THEN
  AITAC THEN
  PAXTAC THEN
  LRTAC THEN
  STAC
  ,
  REPEAT (MATCH_MP_TAC boolTheory.OR_INTRO_THM2) THEN
  EQ_PAIR_ASM_TAC THEN
  RLTAC THEN
  ITAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
  REWRITE_TAC [invariant_l3Theory.INTERNAL_BD_FETCH] THEN
  ITAC state_lemmasTheory.EXTERNAL_BDS_IMPLIES_NOT_INTERNAL_BDS_LEMMA THEN
  ASM_REWRITE_TAC [invariant_l3Theory.EXTERNAL_BD_FETCH] THEN
  IRTAC fetching_bd_lemmasTheory.NOT_IS_NONE_IMPLIES_EXISTS_SOME_LEMMA THEN
  AXTAC THEN
  ETAC invariant_l3Theory.EXTERNAL_BD_ADDRESSES THEN
  ASSUME_TAC (SPEC_ALL fetching_bd_lemmasTheory.FETCH_BD_ADDRESSES_EQ_ADDRESSES_TAG_LEMMA) THEN
  AXTAC THEN
  AITAC THEN
  PAXTAC THEN
  LRTAC THEN
  STAC
  ,
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
  IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
  EQ_PAIR_ASM_TAC THEN
  STAC
 ]
]
QED

Theorem FETCHING_BD_L4_PRESERVES_BD_QUEUES_LEMMA:
!device_characteristics channel_id internal_state1 internal_state2 channel1 channel2.
  EXTERNAL_BDS device_characteristics /\
  IS_NONE channel1.pending_accesses.replies.fetching_bd /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1
  ==>
  internal_state2 = internal_state1 /\
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC fetching_bd_l4 THENL
[
 IRTAC state_lemmasTheory.EXTERNAL_BDS_IMPLIES_NOT_INTERNAL_BDS_LEMMA THEN CONTR_ASMS_TAC
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 PTAC operationsTheory.fetching_bd_set_request THEN TRY STAC THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
]
QED

Theorem EXTERNAL_BDS_IS_NONE_FETCHING_BD_L4_IMPLIES_BD_TO_FETCH_TO_BDS_TO_UPDATE_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  EXTERNAL_BDS device_characteristics /\
  IS_NONE channel1.pending_accesses.replies.fetching_bd /\
  channel1 = schannel device1 channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TO_FETCH_TO_BDS_TO_UPDATE device_characteristics memory device1 device2
Proof
INTRO_TAC THEN
IRTAC FETCHING_BD_L4_PRESERVES_BD_QUEUES_LEMMA THEN
ETAC BD_TO_FETCH_TO_BDS_TO_UPDATE THEN
INTRO_TAC THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
LRTAC THEN
Cases_on ‘channel_id' = channel_id’ THENL
[
 LRTAC THEN
 RLTAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN
 LRTAC THEN
 STAC
 ,
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN AIRTAC THEN STAC
]
QED

Theorem FETCHING_BD_L4_NO_BD_PRESERVES_BD_QUEUES_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 bds_to_fetch1 bds_to_fetch2.
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  INTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  (internal_state2, NONE) = (coperation device_characteristics channel_id).fetch_bd internal_state1 NONE /\
  bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  bds_to_fetch2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2
  ==>
  bds_to_fetch2 = bds_to_fetch1 /\
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC fetching_bd_l4 THEN
PTAC concreteTheory.fetching_bd_fetch_bd_concrete THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 2 THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT THEN
AIRTAC THEN
STAC
QED

Theorem INTERNAL_BDS_NO_FETCH_FETCHING_BD_L4_IMPLIES_BD_TO_FETCH_TO_BDS_TO_UPDATE_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 device1 device2.
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  INTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channel1 = schannel device1 channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  (internal_state2, NONE) = (coperation device_characteristics channel_id).fetch_bd internal_state1 NONE /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TO_FETCH_TO_BDS_TO_UPDATE device_characteristics memory device1 device2
Proof
INTRO_TAC THEN
IRTAC FETCHING_BD_L4_NO_BD_PRESERVES_BD_QUEUES_LEMMA THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC (mk_var ("memory", (type_of o #1 o dest_forall o concl) thm)) thm)) THEN
SPLIT_ASM_TAC THEN
ETAC BD_TO_FETCH_TO_BDS_TO_UPDATE THEN
INTRO_TAC THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
Cases_on ‘channel_id' = channel_id’ THENL
[
 LRTAC THEN
 RLTAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN
 LRTAC THEN
 STAC
 ,
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN AIRTAC THEN STAC
]
QED

Theorem FETCHING_BD_L4_NO_BD_PRESERVES_BD_QUEUES_EXTERNAL_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 bds_to_fetch1 bds_to_fetch2.
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  (internal_state2, NONE) = (coperation device_characteristics channel_id).fetch_bd internal_state1 channel1.pending_accesses.replies.fetching_bd /\
  bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  bds_to_fetch2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2
  ==>
  bds_to_fetch2 = bds_to_fetch1 /\
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC fetching_bd_l4 THENL
[
 IRTAC state_lemmasTheory.EXTERNAL_BDS_IMPLIES_NOT_INTERNAL_BDS_LEMMA THEN CONTR_ASMS_TAC
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 PTAC operationsTheory.fetching_bd_set_request THEN TRY STAC THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 PTAC concreteTheory.fetching_bd_fetch_bd_concrete THENL
 [
  ALL_LRTAC THEN EQ_PAIR_ASM_TAC THEN IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC
  ,
  ALL_LRTAC THEN EQ_PAIR_ASM_TAC THEN IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC
  ,
  EQ_PAIR_ASM_TAC THEN
  NRLTAC 2 THEN
  PTAC operationsTheory.fetching_bd_clear_reply THEN
  LRTAC THEN
  RECORD_TAC THEN
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT THEN
  AIRTAC THEN
  STAC
 ]
]
QED

Theorem EXTERNAL_BDS_NO_FETCH_FETCHING_BD_L4_IMPLIES_BD_TO_FETCH_TO_BDS_TO_UPDATE_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 device1 device2.
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channel1 = schannel device1 channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  (internal_state2, NONE) = (coperation device_characteristics channel_id).fetch_bd internal_state1 channel1.pending_accesses.replies.fetching_bd /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TO_FETCH_TO_BDS_TO_UPDATE device_characteristics memory device1 device2
Proof
INTRO_TAC THEN
IRTAC FETCHING_BD_L4_NO_BD_PRESERVES_BD_QUEUES_EXTERNAL_LEMMA THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC (mk_var ("memory", (type_of o #1 o dest_forall o concl) thm)) thm)) THEN
SPLIT_ASM_TAC THEN
ETAC BD_TO_FETCH_TO_BDS_TO_UPDATE THEN
INTRO_TAC THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
Cases_on ‘channel_id' = channel_id’ THENL
[
 LRTAC THEN
 RLTAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN
 LRTAC THEN
 STAC
 ,
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN AIRTAC THEN STAC
]
QED

Theorem FETCHING_BD_L4_BD_SHIFTS_BD_QUEUES_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 bds_to_fetch1 bds_to_fetch2 bd.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INTERNAL_BD_FETCH device_characteristics channel_id internal_state1 internal_state2 bd /\
  EXTERNAL_BD_FETCH device_characteristics memory channel_id internal_state1 channel1 internal_state2 bd /\
  INTERNAL_STATE_BDS_TO_FETCH_DISJOINT device_characteristics memory internal_state1 /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  bds_to_fetch2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2
  ==>
  ~NULL bds_to_fetch1 /\
  (bds_to_fetch2 = TL bds_to_fetch1) /\
  (channel2.queue.bds_to_update = channel1.queue.bds_to_update ++ [FST (HD bds_to_fetch1)] \/
   channel2.queue.bds_to_update = channel1.queue.bds_to_update) /\
  (channel2.queue.bds_to_process = channel1.queue.bds_to_process ++ [FST (HD bds_to_fetch1)] \/
   channel2.queue.bds_to_process = channel1.queue.bds_to_process) /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC fetching_bd_l4 THENL
[
 PTAC INTERNAL_STATE_BDS_TO_FETCH_DISJOINT THEN AITAC THEN
 IRTAC fetching_bd_lemmasTheory.FETCHING_BD_FETCH_BD_CONCRETE_INTERNAL_LEMMA THEN STAC
 ,
 IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
 ETAC invariant_l3Theory.EXTERNAL_BD_FETCH THEN
 AIRTAC THEN
 AXTAC THEN
 ALL_LRTAC THEN
 RLTAC THEN
 ETAC optionTheory.IS_NONE_DEF THEN
 SOLVE_F_ASM_TAC
 ,
 IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
 PTAC INTERNAL_STATE_BDS_TO_FETCH_DISJOINT THEN AITAC THEN
 IRTAC fetching_bd_lemmasTheory.FETCHING_BD_FETCH_BD_CONCRETE_EXTERNAL_LEMMA THEN
 STAC
]
QED

Theorem FETCH_BD_FETCHING_BD_L4_IMPLIES_BD_TO_FETCH_TO_BDS_TO_UPDATE_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id bd.
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  EXTERNAL_BD_FETCH device_characteristics memory channel_id internal_state1 channel1 internal_state2 bd /\
  INTERNAL_BD_FETCH device_characteristics channel_id internal_state1 internal_state2 bd /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INTERNAL_STATE_BDS_TO_FETCH_DISJOINT device_characteristics memory internal_state1 /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TO_FETCH_TO_BDS_TO_UPDATE device_characteristics memory device1 device2
Proof
INTRO_TAC THEN
IRTAC FETCHING_BD_L4_BD_SHIFTS_BD_QUEUES_LEMMA THEN
ETAC BD_TO_FETCH_TO_BDS_TO_UPDATE THEN
INTRO_TAC THEN
Cases_on ‘channel_id' <> channel_id’ THEN TRY (IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN AIRTAC THEN STAC) THEN
PAT_X_ASSUM “~~X” (fn thm => ASSUME_TAC (REWRITE_RULE [boolTheory.NOT_CLAUSES] thm)) THEN
LRTAC THEN
IRTAC listTheory.CONS THEN
PAT_X_ASSUM “channel1 = schannel device1 channel_id” (fn thm => ASSUME_TAC thm) THEN
RLTAC THEN
ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN
LRTAC THEN
PAT_X_ASSUM “internal_state1 = device1.dma_state.internal_state” (fn thm => ASSUME_TAC thm) THEN
RLTAC THEN
IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
LRTAC THEN
SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 ALL_LRTAC THEN
 RLTAC THEN
 EXISTS_EQ_TAC THEN
 REWRITE_TAC [listTheory.HD, listTheory.TL, listTheory.CONS_11] THEN
 Cases_on ‘HD ((cverification device_characteristics channel_id).bds_to_fetch memory internal_state1)’ THEN
 REWRITE_TAC [pairTheory.FST] THEN
 EXISTS_EQ_TAC 
QED

Theorem FETCHING_BD_L4_EXTERNAL_BD_ADDRESSES_IMPLIES_BD_TO_FETCH_TO_BDS_TO_UPDATE_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  EXTERNAL_BD_ADDRESSES device_characteristics channel_id memory internal_state1 channel1 /\
  INTERNAL_STATE_BDS_TO_FETCH_DISJOINT device_characteristics memory internal_state1 /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TO_FETCH_TO_BDS_TO_UPDATE device_characteristics memory device1 device2
Proof
INTRO_TAC THEN
ITAC FETCHING_BD_L4_PRESERVES_INTERNAL_STATE_OR_FETCHES_PARITAL_BD_OR_FETCHES_COMPLETE_BD_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 IRTAC EXTERNAL_BDS_IS_NONE_FETCHING_BD_L4_IMPLIES_BD_TO_FETCH_TO_BDS_TO_UPDATE_LEMMA THEN STAC
 ,
 IRTAC INTERNAL_BDS_NO_FETCH_FETCHING_BD_L4_IMPLIES_BD_TO_FETCH_TO_BDS_TO_UPDATE_LEMMA THEN STAC
 ,
 IRTAC EXTERNAL_BDS_NO_FETCH_FETCHING_BD_L4_IMPLIES_BD_TO_FETCH_TO_BDS_TO_UPDATE_LEMMA THEN STAC
 ,
 AXTAC THEN IRTAC FETCH_BD_FETCHING_BD_L4_IMPLIES_BD_TO_FETCH_TO_BDS_TO_UPDATE_LEMMA THEN STAC
]
QED

Theorem FETCHING_BD_L4_IMPLIES_BD_TO_FETCH_TO_BDS_TO_UPDATE_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device1 /\
  INTERNAL_STATE_BDS_TO_FETCH_DISJOINT device_characteristics memory internal_state1 /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TO_FETCH_TO_BDS_TO_UPDATE device_characteristics memory device1 device2
Proof
INTRO_TAC THEN
ITAC invariant_l3_lemmasTheory.INVARIANT_EXTERNAL_FETCH_BD_REPLY_IMPLIES_EXTERNAL_BD_ADDRESSES_LEMMA THEN
IRTAC FETCHING_BD_L4_EXTERNAL_BD_ADDRESSES_IMPLIES_BD_TO_FETCH_TO_BDS_TO_UPDATE_LEMMA THEN
STAC
QED

(*******************************************************************************)

Theorem EXTERNAL_BDS_IS_NONE_FETCHING_BD_L4_IMPLIES_BD_TO_FETCH_TO_BDS_TO_PROCESS_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  EXTERNAL_BDS device_characteristics /\
  IS_NONE channel1.pending_accesses.replies.fetching_bd /\
  channel1 = schannel device1 channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TO_FETCH_TO_BDS_TO_PROCESS device_characteristics memory device1 device2
Proof
INTRO_TAC THEN
IRTAC FETCHING_BD_L4_PRESERVES_BD_QUEUES_LEMMA THEN
ETAC BD_TO_FETCH_TO_BDS_TO_PROCESS THEN
INTRO_TAC THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
LRTAC THEN
Cases_on ‘channel_id' = channel_id’ THENL
[
 LRTAC THEN RLTAC THEN IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN LRTAC THEN STAC
 ,
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN AIRTAC THEN STAC
]
QED

Theorem INTERNAL_BDS_NO_FETCH_FETCHING_BD_L4_IMPLIES_BD_TO_FETCH_TO_BDS_TO_PROCESS_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 device1 device2.
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  INTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channel1 = schannel device1 channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  (internal_state2, NONE) = (coperation device_characteristics channel_id).fetch_bd internal_state1 NONE /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TO_FETCH_TO_BDS_TO_PROCESS device_characteristics memory device1 device2
Proof
INTRO_TAC THEN
IRTAC FETCHING_BD_L4_NO_BD_PRESERVES_BD_QUEUES_LEMMA THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC (mk_var ("memory", (type_of o #1 o dest_forall o concl) thm)) thm)) THEN
SPLIT_ASM_TAC THEN
ETAC BD_TO_FETCH_TO_BDS_TO_PROCESS THEN
INTRO_TAC THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
Cases_on ‘channel_id' = channel_id’ THENL
[
 LRTAC THEN RLTAC THEN IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN LRTAC THEN STAC
 ,
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN AIRTAC THEN STAC
]
QED

Theorem EXTERNAL_BDS_NO_FETCH_FETCHING_BD_L4_IMPLIES_BD_TO_FETCH_TO_BDS_TO_PROCESS_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 device1 device2.
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channel1 = schannel device1 channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  (internal_state2, NONE) = (coperation device_characteristics channel_id).fetch_bd internal_state1 channel1.pending_accesses.replies.fetching_bd /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TO_FETCH_TO_BDS_TO_PROCESS device_characteristics memory device1 device2
Proof
INTRO_TAC THEN
IRTAC FETCHING_BD_L4_NO_BD_PRESERVES_BD_QUEUES_EXTERNAL_LEMMA THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC (mk_var ("memory", (type_of o #1 o dest_forall o concl) thm)) thm)) THEN
SPLIT_ASM_TAC THEN
ETAC BD_TO_FETCH_TO_BDS_TO_PROCESS THEN
INTRO_TAC THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
Cases_on ‘channel_id' = channel_id’ THENL
[
 LRTAC THEN RLTAC THEN IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN LRTAC THEN STAC
 ,
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN AIRTAC THEN STAC
]
QED

Theorem FETCH_BD_FETCHING_BD_L4_IMPLIES_BD_TO_FETCH_TO_BDS_TO_PROCESS_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id bd.
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  EXTERNAL_BD_FETCH device_characteristics memory channel_id internal_state1 channel1 internal_state2 bd /\
  INTERNAL_BD_FETCH device_characteristics channel_id internal_state1 internal_state2 bd /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INTERNAL_STATE_BDS_TO_FETCH_DISJOINT device_characteristics memory internal_state1 /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TO_FETCH_TO_BDS_TO_PROCESS device_characteristics memory device1 device2
Proof
INTRO_TAC THEN
IRTAC FETCHING_BD_L4_BD_SHIFTS_BD_QUEUES_LEMMA THEN
ETAC BD_TO_FETCH_TO_BDS_TO_PROCESS THEN
INTRO_TAC THEN
Cases_on ‘channel_id' <> channel_id’ THEN TRY (IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN AIRTAC THEN STAC) THEN
PAT_X_ASSUM “~~X” (fn thm => ASSUME_TAC (REWRITE_RULE [boolTheory.NOT_CLAUSES] thm)) THEN
LRTAC THEN
IRTAC listTheory.CONS THEN
PAT_X_ASSUM “channel1 = schannel device1 channel_id” (fn thm => ASSUME_TAC thm) THEN
RLTAC THEN
ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN
LRTAC THEN
PAT_X_ASSUM “internal_state1 = device1.dma_state.internal_state” (fn thm => ASSUME_TAC thm) THEN
RLTAC THEN
IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
LRTAC THEN
SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 ALL_LRTAC THEN
 RLTAC THEN
 EXISTS_EQ_TAC THEN
 REWRITE_TAC [listTheory.HD, listTheory.TL, listTheory.CONS_11] THEN
 Cases_on ‘HD ((cverification device_characteristics channel_id).bds_to_fetch memory internal_state1)’ THEN
 REWRITE_TAC [pairTheory.FST] THEN
 EXISTS_EQ_TAC 
QED

Theorem FETCHING_BD_L4_EXTERNAL_BD_ADDRESSES_IMPLIES_BD_TO_FETCH_TO_BDS_TO_PROCESS_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  EXTERNAL_BD_ADDRESSES device_characteristics channel_id memory internal_state1 channel1 /\
  INTERNAL_STATE_BDS_TO_FETCH_DISJOINT device_characteristics memory internal_state1 /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TO_FETCH_TO_BDS_TO_PROCESS device_characteristics memory device1 device2
Proof
INTRO_TAC THEN
ITAC FETCHING_BD_L4_PRESERVES_INTERNAL_STATE_OR_FETCHES_PARITAL_BD_OR_FETCHES_COMPLETE_BD_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 IRTAC EXTERNAL_BDS_IS_NONE_FETCHING_BD_L4_IMPLIES_BD_TO_FETCH_TO_BDS_TO_PROCESS_LEMMA THEN STAC
 ,
 IRTAC INTERNAL_BDS_NO_FETCH_FETCHING_BD_L4_IMPLIES_BD_TO_FETCH_TO_BDS_TO_PROCESS_LEMMA THEN STAC
 ,
 IRTAC EXTERNAL_BDS_NO_FETCH_FETCHING_BD_L4_IMPLIES_BD_TO_FETCH_TO_BDS_TO_PROCESS_LEMMA THEN STAC
 ,
 AXTAC THEN IRTAC FETCH_BD_FETCHING_BD_L4_IMPLIES_BD_TO_FETCH_TO_BDS_TO_PROCESS_LEMMA THEN STAC
]
QED

Theorem FETCHING_BD_L4_IMPLIES_BD_TO_FETCH_TO_BDS_TO_PROCESS_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device1 /\
  INTERNAL_STATE_BDS_TO_FETCH_DISJOINT device_characteristics memory internal_state1 /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TO_FETCH_TO_BDS_TO_PROCESS device_characteristics memory device1 device2
Proof
INTRO_TAC THEN
ITAC invariant_l3_lemmasTheory.INVARIANT_EXTERNAL_FETCH_BD_REPLY_IMPLIES_EXTERNAL_BD_ADDRESSES_LEMMA THEN
IRTAC FETCHING_BD_L4_EXTERNAL_BD_ADDRESSES_IMPLIES_BD_TO_FETCH_TO_BDS_TO_PROCESS_LEMMA THEN
STAC
QED

(*******************************************************************************)

Theorem FETCHING_BD_FETCH_BD_CONCRETE_PRESERVES_BDS_TO_WRITE_BACK_LEMMA:
!fetch_bd internal_state1 internal_state2 channel1 channel2 some_reply.
  (internal_state2, channel2) = fetching_bd_fetch_bd_concrete fetch_bd internal_state1 channel1 some_reply
  ==>
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC concreteTheory.fetching_bd_fetch_bd_concrete THENL
[
 EQ_PAIR_ASM_TAC THEN IRTAC fetching_bd_lemmasTheory.APPEND_BDS_TO_PROCESS_OPERATION_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN IRTAC fetching_bd_lemmasTheory.APPEND_BDS_TO_UPDATE_APPENDS_BDS_TO_UPDATE_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem FETCHING_BD_L4_IMPLIES_BDS_TO_WRITE_BACK_NOT_EXPANDED_LEMMA:
!device_characteristics device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BDS_TO_WRITE_BACK_NOT_EXPANDED device_characteristics device1 device2
Proof
INTRO_TAC THEN
ETAC BDS_TO_WRITE_BACK_NOT_EXPANDED THEN
ETAC BDS_TO_OPERATE_ON_NOT_EXPANDED THEN
INTRO_TAC THEN
Cases_on ‘channel_id' = channel_id’ THENL
[
 LRTAC THEN
 PTAC fetching_bd_l4 THENL
 [
  IRTAC FETCHING_BD_FETCH_BD_CONCRETE_PRESERVES_BDS_TO_WRITE_BACK_LEMMA THEN
  IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN
  ALL_LRTAC THEN
  REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
  ,
  PTAC operationsTheory.fetching_bd_set_request THEN
  EQ_PAIR_ASM_TAC THEN
  LRTAC THEN
  IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN
  LRTAC THEN
  RLTAC THEN
  ALL_LRTAC THEN
  RECORD_TAC THEN
  REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
  ,
  IRTAC FETCHING_BD_FETCH_BD_CONCRETE_PRESERVES_BDS_TO_WRITE_BACK_LEMMA THEN
  IRTAC fetching_bd_lemmasTheory.FETCHING_BD_CLEAR_REPLY_PRESERVES_BD_QUEUES_LEMMA THEN
  IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN
  LRTAC THEN
  RLTAC THEN
  RLTAC THEN
  RLTAC THEN
  RLTAC THEN
  ALL_LRTAC THEN
  REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
 ]
 ,
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN
 AIRTAC THEN
 ALL_LRTAC THEN
 REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
]
QED

(*******************************************************************************)

Theorem FETCHING_BD_L4_INTERNAL_STATE_LEMMA:
!device_characteristics channel_id internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1
  ==>
  internal_state2 = internal_state1 \/
  ?reply fetch_result.
    (internal_state2, fetch_result) = (coperation device_characteristics channel_id).fetch_bd internal_state1 reply
Proof
INTRO_TAC THEN
PTAC fetching_bd_l4 THENL
[
 PTAC concreteTheory.fetching_bd_fetch_bd_concrete THEN
  EQ_PAIR_ASM_TAC THEN MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN PAXTAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 PTAC concreteTheory.fetching_bd_fetch_bd_concrete THEN
  EQ_PAIR_ASM_TAC THEN MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN PAXTAC THEN STAC 
]
QED

Theorem FETCHING_BD_L4_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA:
!device_characteristics channel_id internal_state1 internal_state2 channel1 channel2.
  PROOF_OBLIGATION_FETCHING_BD_PRESERVES_BD_INTERPRETATION device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1
  ==>
  BD_TRANSFER_RAS_WAS_EQ device_characteristics internal_state1 internal_state2
Proof
INTRO_TAC THEN
IRTAC FETCHING_BD_L4_INTERNAL_STATE_LEMMA THEN
ETAC stateTheory.BD_TRANSFER_RAS_WAS_EQ THEN
SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
AXTAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHING_BD_PRESERVES_BD_INTERPRETATION THEN
AIRTAC THEN
INTRO_TAC THEN
AIRTAC THEN
STAC
QED

(*******************************************************************************)

Theorem FETCHING_BD_L4_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  PROOF_OBLIGATION_FETCHING_BD_PRESERVES_BD_INTERPRETATION device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  (internal_state2, channel2) = fetching_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device1 /\
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device1 /\
  INVARIANT_CONCRETE_L4 device_characteristics memory device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ITAC INVARIANT_BDS_TO_FETCH_DISJOINT_IMPLIES_INTERNAL_STATE_BDS_TO_FETCH_DISJOINT_LEMMA THEN
ETAC INVARIANT_CONCRETE_L4 THEN
ITAC FETCHING_BD_L4_IMPLIES_BDS_TO_FETCH_NOT_EXPANDED_LEMMA THEN
ITAC FETCHING_BD_L4_IMPLIES_BD_TO_FETCH_TO_BDS_TO_UPDATE_LEMMA THEN
ITAC FETCHING_BD_L4_IMPLIES_BD_TO_FETCH_TO_BDS_TO_PROCESS_LEMMA THEN
ITAC FETCHING_BD_L4_IMPLIES_BDS_TO_WRITE_BACK_NOT_EXPANDED_LEMMA THEN
IRTAC FETCHING_BD_L4_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4_LEMMA THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4_LEMMA THEN
ITAC BDS_TO_FETCH_TO_BDS_TO_UPDATE_PRESERVES_INVARIANT_UPDATE_BD_BD_WRITE_L4_LEMMA THEN
ITAC BDS_TO_FETCH_TO_BDS_TO_PROCESS_PRESERVES_INVARIANT_PROCESS_BD_BD_WRITE_L4_LEMMA THEN
ITAC BDS_TO_WRITE_BACK_NOT_EXPANDED_PRESERVES_INVARIANT_WRITE_BACK_BD_BD_WRITE_L4_LEMMA THEN
IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_INVARIANT_FETCH_BD_DMA_WRITE_L4_LEMMA THEN
ITAC BD_TO_FETCH_TO_BDS_TO_UPDATE_PRESERVES_INVARIANT_UPDATE_BD_DMA_WRITE_L4_LEMMA THEN
ITAC BD_TO_FETCH_TO_BDS_TO_PROCESS_PRESERVES_INVARIANT_PROCESS_BD_DMA_WRITE_L4_LEMMA THEN
STAC
QED

val _ = export_theory();

