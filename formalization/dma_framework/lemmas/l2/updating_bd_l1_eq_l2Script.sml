open HolKernel Parse boolLib bossLib helper_tactics;
open invariant_l2Theory proof_obligations_dma_l2Theory;
open stateTheory operationsTheory l1Theory l2Theory;

val _ = new_theory "updating_bd_l1_eq_l2";

Theorem INVARIANT_L2_UPDATE_BD_ADDRESSES_W_LEMMA:
!device_characteristics environment device1 internal_state_pre_scheduling
 internal_state1 channel1 function_state scheduler channel_id pipelines
 pending_register_memory_accesses dma_channel_operation memory bd_ras_was
 bd_ras_wass write_addresses.
  INVARIANT_L2 device_characteristics memory device1 /\
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  EXTERNAL_BDS device_characteristics /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation /\
  (bd_ras_was::bd_ras_wass) = channel1.queue.bds_to_update /\
  write_addresses = (cverification device_characteristics channel_id).update_bd_addresses internal_state1 bd_ras_was
  ==>
  EVERY (device_characteristics.dma_characteristics.W memory) write_addresses
Proof
INTRO_TAC THEN
ITAC proof_obligations_dma_l2_lemmasTheory.PROOF_OBLIGATIONS_DMA_L2_INTERNAL_DMA_OPERATION_IMPLIES_VALID_CHANNEL_ID_LEMMA THEN
IRTAC proof_obligations_dma_l2_lemmasTheory.PROOF_OBLIGATIONS_DMA_L2_IMPLIES_DECLARED_UPDATE_WRITES_BD_WAS_LEMMA THEN
IRTAC invariant_l2_lemmasTheory.INVARIANT_L2_IMPLIES_UPDATE_BD_LEMMA THEN
ITAC internal_operation_lemmasTheory.INTERNAL_DMA_OPERATION_IMPLIES_CHANNEL_STATE_LEMMA THEN
LRTAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_DECLARED_UPDATE_WRITES_BD_WAS THEN
AITAC THEN
IRTAC lists_lemmasTheory.MEM_HD_LEMMA THEN
PTAC INVARIANT_UPDATE_BD_L2 THEN
AITAC THEN
PTAC BD_WRITE THEN
AIRTAC THEN
IRTAC lists_lemmasTheory.EVERY_SUBLIST_LEMMA THEN
STAC
QED

Theorem UPDATING_BD_L2_EQ_L1_LEMMA:
!device_characteristics environment device1 internal_state_pre_scheduling
 internal_state1 channel1 pipelines pending_register_memory_accesses
 function_state scheduler channel_id dma_channel_operation memory.
  INVARIANT_L2 device_characteristics memory device1 /\
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation
  ==>
  (updating_bd_l2 device_characteristics channel_id memory internal_state1 channel1 =
   updating_bd_l1 device_characteristics channel_id memory internal_state1 channel1)
Proof
INTRO_TAC THEN
PTAC updating_bd_l2 THEN PTAC updating_bd_l1 THENL
[
 STAC
 ,
 STAC
 ,
 IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
 IRTAC INVARIANT_L2_UPDATE_BD_ADDRESSES_W_LEMMA THEN
 CONTR_ASMS_TAC
 ,
 STAC
 ,
 STAC
]
QED

val _ = export_theory();

