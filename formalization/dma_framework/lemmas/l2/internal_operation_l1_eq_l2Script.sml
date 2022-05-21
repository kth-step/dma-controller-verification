open HolKernel Parse boolLib bossLib helper_tactics;
open invariant_l2Theory;
open proof_obligations_dma_l2Theory;
open operationsTheory;
open l1Theory l2Theory;

val _ = new_theory "internal_operation_l1_eq_l2";

Theorem CHANNEL_OPERATION_L2_EQ_L1_LEMMA:
!device_characteristics memory device1 internal_state1 internal_state_pre_scheduling
 scheduler channel_id pipelines pending_register_memory_accesses
 dma_channel_operation environment channel1 function_state.
  INVARIANT_L2 device_characteristics memory device1 /\
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation
  ==>
  channel_operation_l2 device_characteristics channel_id dma_channel_operation (SOME memory) environment internal_state1 channel1 =
  channel_operation_l1 device_characteristics channel_id dma_channel_operation (SOME memory) environment internal_state1 channel1
Proof
INTRO_TAC THEN
PTAC channel_operation_l2 THEN PTAC channel_operation_l1 THEN
  PTAC channel_operation_case_l2 THEN PTAC channel_operation_case_l1 THENL
[
 FIRTAC fetching_bd_l1_eq_l2Theory.FETCHING_BD_L2_EQ_L1_LEMMA THEN STAC
 ,
 ITAC updating_bd_l1_eq_l2Theory.UPDATING_BD_L2_EQ_L1_LEMMA THEN LRTAC THEN STAC
 ,
 ITAC transferring_data_l1_eq_l2Theory.TRANSFERRING_DATA_L2_EQ_L1_LEMMA THEN STAC
 ,
 ITAC writing_back_bd_l1_eq_l2Theory.WRITING_BACK_BD_L2_EQ_L1_LEMMA THEN STAC
]
QED

Theorem DEVICE_BSIM_L1_L2_INTERNAL_DEVICE_OPERATION_LEMMA:
!device_characteristics memory device environment.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  INVARIANT_L2 device_characteristics memory device
  ==>
  internal_device_operation device_characteristics channel_operation_l2 (SOME memory) environment device =
  internal_device_operation device_characteristics channel_operation_l1 (SOME memory) environment device
Proof
INTRO_TAC THEN
REPEAT (PTAC internal_device_operation) THENL
[
 STAC
 ,
 REWRITE_TAC [internal_dma_operation] THEN
 LETS_TAC THEN
 ITAC state_lemmasTheory.DEVICE_CHANNELS_CHANNEL_ID_IMPLIES_SCHANNEL_LEMMA THEN
 IRTAC ((GEN_ALL o #2 o EQ_IMP_RULE o SPEC_ALL) INTERNAL_DMA_OPERATION) THEN
 IRTAC CHANNEL_OPERATION_L2_EQ_L1_LEMMA THEN
 LRTAC THEN
 LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 STAC
 ,
 STAC
 ,
 STAC
]
QED

val _ = export_theory();

