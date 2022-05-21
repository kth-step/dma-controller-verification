open HolKernel Parse boolLib bossLib helper_tactics;
open l3Theory l4Theory proof_obligationsTheory invariant_l4Theory;

val _ = new_theory "updating_bd_l3_eq_l4";

Theorem UPDATING_BD_L4_EQ_L3_LEMMA:
!device_characteristics channel_id memory device channel internal_state.
  PROOF_OBLIGATION_DECLARED_UPDATE_WRITES_BD_WAS device_characteristics /\
  INVARIANT_UPDATE_BD_BD_WRITE_L4 device_characteristics memory device /\
  BDS_TO_FETCH_EQ device_characteristics memory device.dma_state.internal_state internal_state /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channel = schannel device channel_id
  ==>
  updating_bd_l4 device_characteristics channel_id        internal_state channel =
  updating_bd_l3 device_characteristics channel_id memory internal_state channel
Proof
INTRO_TAC THEN
PTAC updating_bd_l4 THEN PTAC updating_bd_l3 THENL
[
 RLTAC THEN
 PAT_X_ASSUM “(coperation device_characteristics channel_id).update_bd internal_state h = r” (fn thm => ASSUME_TAC thm) THEN LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 NLRTAC 4 THEN
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN
 STAC
 ,
 IRTAC lists_lemmasTheory.MEM_HD_LEMMA THEN
 PTAC INVARIANT_UPDATE_BD_BD_WRITE_L4 THEN
 ETAC BD_WRITE THEN
 AITAC THEN
 ITAC bd_queues_lemmasTheory.BDS_TO_FETCH_EQ_PRESERVES_CONSISTENT_BD_WRITE_LEMMA THEN
 PTAC PROOF_OBLIGATION_DECLARED_UPDATE_WRITES_BD_WAS THEN
 AIRTAC THEN
 IRTAC bd_queues_lemmasTheory.LIST1_IN_LIST2_PRESERVES_CONSISTENT_BD_WRITE_LEMMA THEN
 CONTR_ASMS_TAC
 ,
 RLTAC THEN
 PAT_X_ASSUM “(coperation device_characteristics channel_id).update_bd internal_state h = r” (fn thm => ASSUME_TAC thm) THEN LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 NLRTAC 4 THEN
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN
 STAC
 ,
 IRTAC lists_lemmasTheory.MEM_HD_LEMMA THEN
 PTAC INVARIANT_UPDATE_BD_BD_WRITE_L4 THEN
 ETAC BD_WRITE THEN
 AITAC THEN
 ITAC bd_queues_lemmasTheory.BDS_TO_FETCH_EQ_PRESERVES_CONSISTENT_BD_WRITE_LEMMA THEN
 PTAC PROOF_OBLIGATION_DECLARED_UPDATE_WRITES_BD_WAS THEN
 AIRTAC THEN
 IRTAC bd_queues_lemmasTheory.LIST1_IN_LIST2_PRESERVES_CONSISTENT_BD_WRITE_LEMMA THEN
 CONTR_ASMS_TAC 
 ,
 STAC
]
QED

val _ = export_theory();

