open HolKernel Parse boolLib bossLib helper_tactics;
open invariant_l2Theory proof_obligations_dma_l2Theory operationsTheory;
open stateTheory l1Theory l2Theory;

val _ = new_theory "writing_back_bd_l1_eq_l2";

Theorem PROOF_OBLIGATIONS_DMA_L2_IMPLIES_PROOF_OBLIGATION_DECLARED_WRITE_BACK_WRITES_BD_WAS_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics
  ==>
  PROOF_OBLIGATION_DECLARED_WRITE_BACK_WRITES_BD_WAS device_characteristics
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATIONS_DMA_L2 THEN
STAC
QED

Theorem INVARIANT_L2_IMPLIES_INVARIANT_WRITE_BACK_BD_L2_LEMMA:
!device_characteristics memory device.
  INVARIANT_L2 device_characteristics memory device
  ==>
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device
Proof
INTRO_TAC THEN
PTAC INVARIANT_L2 THEN
STAC
QED

Theorem INVARIANT_L2_WRITE_BACK_BD_ADDRESSES_W_LEMMA:
!device_characteristics environment device1 internal_state_pre_scheduling
 internal_state1 channel1 function_state scheduler channel_id write_addresses
 dma_channel_operation memory pipelines pending_register_memory_accesses.
  INVARIANT_L2 device_characteristics memory device1 /\
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  EXTERNAL_BDS device_characteristics /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation /\
  write_addresses = (cverification device_characteristics channel_id).write_back_bd_addresses environment internal_state1 channel1.queue.bds_to_write_back
  ==>
  EVERY (device_characteristics.dma_characteristics.W memory) write_addresses
Proof
INTRO_TAC THEN
ITAC proof_obligations_dma_l2_lemmasTheory.PROOF_OBLIGATIONS_DMA_L2_INTERNAL_DMA_OPERATION_EQS_LEMMA THEN
IRTAC PROOF_OBLIGATIONS_DMA_L2_IMPLIES_PROOF_OBLIGATION_DECLARED_WRITE_BACK_WRITES_BD_WAS_LEMMA THEN
ETAC listTheory.EVERY_MEM THEN
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_DECLARED_WRITE_BACK_WRITES_BD_WAS THEN
AITAC THEN
AXTAC THEN
IRTAC INVARIANT_L2_IMPLIES_INVARIANT_WRITE_BACK_BD_L2_LEMMA THEN
PTAC INVARIANT_WRITE_BACK_BD_L2 THEN
IRTAC internal_operation_lemmasTheory.INTERNAL_DMA_OPERATION_IMPLIES_CHANNEL_STATE_LEMMA THEN
LRTAC THEN
AITAC THEN
PTAC BD_WRITE THEN
AITAC THEN
ETAC listTheory.EVERY_MEM THEN
AIRTAC THEN
STAC
QED

Theorem WRITING_BACK_BD_L2_EQ_L1_LEMMA:
!device_characteristics environment device1 internal_state_pre_scheduling
 internal_state1 channel1 function_state scheduler channel_id
 dma_channel_operation memory pipelines pending_register_memory_accesses.
  INVARIANT_L2 device_characteristics memory device1 /\
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation
  ==>
  (writing_back_bd_l2 device_characteristics channel_id memory environment internal_state1 channel1 =
   writing_back_bd_l1 device_characteristics channel_id memory environment internal_state1 channel1)
Proof
INTRO_TAC THEN
PTAC writing_back_bd_l2 THEN PTAC writing_back_bd_l1 THENL
[
 STAC
 ,
 STAC
 ,
 EQ_PAIR_TAC THEN
 REWRITE_TAC [] THEN
 ITAC INVARIANT_L2_WRITE_BACK_BD_ADDRESSES_W_LEMMA THEN
 IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
 AIRTAC THEN
 CONTR_ASMS_TAC
 ,
 STAC
]
QED

val _ = export_theory();

