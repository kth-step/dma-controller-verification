open HolKernel Parse boolLib bossLib helper_tactics;
open operationsTheory;
open invariant_l1Theory;

val _ = new_theory "append_external_abstract_bds_l1";

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVS_INVARIANT_L1_LEMMA:
!device_characteristics memory device1 device2.
  device2 = dma_append_external_abstract_bds device_characteristics memory device1 /\
  INVARIANT_L1 device_characteristics memory device1
  ==>
  INVARIANT_L1 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_L1 THEN
ITAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_DEVICE_REQUESTING_R_ADDRESSES_LEMMA THEN
ITAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_DEVICE_REQUESTING_W_ADDRESSES_LEMMA THEN
STAC
QED

Theorem APPEND_EXTERNAL_ABSTRACT_BDS_L1_PRESERVS_INVARIANT_L1_LEMMA:
!device_characteristics memory device1 device2.
  device2 = append_external_abstract_bds_l1 device_characteristics memory device1 /\
  INVARIANT_L1 device_characteristics memory device1
  ==>
  INVARIANT_L1 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC l1Theory.append_external_abstract_bds_l1 THEN
IF_SPLIT_TAC THENL
[
 ITAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVS_INVARIANT_L1_LEMMA THEN STAC
 ,
 STAC
]
QED

Theorem DEVICE_TRANSITION_L1_EXTERNAL_BDS_APPENDED_PRESERVES_INVARIANT_L1_LEMMA:
!device_characteristics device1 device2 memory.
  device_transition_l1 device_characteristics device1 (memory, external_bds_appended) device2 /\
  INVARIANT_L1 device_characteristics memory device1
  ==>
  INVARIANT_L1 device_characteristics memory device2
Proof
REPEAT GEN_TAC THEN
REWRITE_TAC [l1Theory.device_transitions_l1_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
ITAC APPEND_EXTERNAL_ABSTRACT_BDS_L1_PRESERVS_INVARIANT_L1_LEMMA THEN
STAC
QED

val _ = export_theory();

