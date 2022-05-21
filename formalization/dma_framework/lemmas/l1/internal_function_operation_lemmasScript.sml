open HolKernel Parse boolLib bossLib helper_tactics;
open operationsTheory invariant_l1Theory;

val _ = new_theory "internal_function_operation_lemmas";

Theorem INTERNAL_FUNCTION_OPERATION_PRESERVES_INVARIANT_L1_LEMMA:
!device_characteristics environment device1 device2 memory.
  device2 = internal_function_operation (THE device_characteristics.function_characteristics) environment device1 /\
  INVARIANT_L1 device_characteristics memory device1
  ==>
  INVARIANT_L1 device_characteristics memory device2
Proof
INTRO_TAC THEN
ITAC internal_operation_lemmasTheory.INTERNAL_FUNCTION_OPERATION_PRESERVES_ALL_DMA_CHANNELS_PENDING_ACCESSES_LEMMA THEN
IRTAC internal_operation_lemmasTheory.INTERNAL_FUNCTION_OPERATION_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA THEN
IRTAC l1_dma_lemmasTheory.ALL_DMA_CHANNELS_EQ_PENDING_ACCESSES_PRESERVES_INVARIANT_L1_LEMMA THEN
STAC
QED

val _ = export_theory();

