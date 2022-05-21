open HolKernel Parse boolLib bossLib helper_tactics;
open proof_obligations_dma_l2Theory operationsTheory;

val _ = new_theory "proof_obligations_dma_l2_lemmas";

Theorem PROOF_OBLIGATIONS_DMA_L2_IMPLIES_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics
  ==>
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION device_characteristics
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATIONS_DMA_L2 THEN
STAC
QED

(*
Theorem PROOF_OBLIGATIONS_DMA_L2_IMPLIES_SCHEDULER_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics
  ==>
  PROOF_OBLIGATION_SCHEDULER device_characteristics
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATIONS_DMA_L2 THEN
STAC
QED
*)

Theorem PROOF_OBLIGATIONS_DMA_L2_IMPLIES_READ_REQUESTS_CONSISTENT_WITH_BD_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics
  ==>
  PROOF_OBLIGATION_READ_REQUESTS_CONSISTENT_WITH_BD device_characteristics
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATIONS_DMA_L2 THEN
STAC
QED

Theorem PROOF_OBLIGATIONS_DMA_L2_IMPLIES_WRITE_REQUESTS_CONSISTENT_WITH_BD_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics
  ==>
  PROOF_OBLIGATION_WRITE_REQUESTS_CONSISTENT_WITH_BD device_characteristics
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATIONS_DMA_L2 THEN
STAC
QED

Theorem PROOF_OBLIGATIONS_DMA_L2_IMPLIES_SCHEDULER_PRESERVES_BD_INTERPRETATION_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics
  ==>
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION device_characteristics
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATIONS_DMA_L2 THEN
STAC
QED
(*
Theorem PROOF_OBLIGATIONS_DMA_L2_IMPLIES_SCHEDULER_PRESERVES_REGISTER_RAS_WAS_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics
  ==>
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_REGISTER_RAS_WAS device_characteristics
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATIONS_DMA_L2 THEN
STAC
QED
*)
Theorem PROOF_OBLIGATIONS_DMA_L2_INTERNAL_DMA_OPERATION_IMPLIES_VALID_CHANNEL_ID_LEMMA:
!device_characteristics environment device1 internal_state_pre_scheduling
 internal_state1 channel1 function_state
 scheduler pipelines pending_register_memory_accesses channel_id dma_channel_operation.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation
  ==>
  VALID_CHANNEL_ID device_characteristics channel_id
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATIONS_DMA_L2 THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_SCHEDULER THEN
PTAC INTERNAL_DMA_OPERATION THEN
AIRTAC THEN
STAC
QED

Theorem PROOF_OBLIGATIONS_DMA_L2_IMPLIES_DECLARED_UPDATE_WRITES_BD_WAS_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics
  ==>
  PROOF_OBLIGATION_DECLARED_UPDATE_WRITES_BD_WAS device_characteristics
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATIONS_DMA_L2 THEN
STAC
QED

Theorem PROOF_OBLIGATIONS_DMA_L2_IMPLIES_DECLARED_WRITE_BACK_WRITES_BD_WAS_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics
  ==>
  PROOF_OBLIGATION_DECLARED_WRITE_BACK_WRITES_BD_WAS device_characteristics
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATIONS_DMA_L2 THEN
STAC
QED

Theorem PROOF_OBLIGATIONS_DMA_L2_INTERNAL_DMA_OPERATION_EQS_LEMMA:
!device_characteristics environment device1 internal_state_pre_scheduling
 internal_state1 channel1 function_state scheduler channel_id
 dma_channel_operation pipelines pending_register_memory_accesses.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation
  ==>
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state_pre_scheduling = device1.dma_state.internal_state /\
  (internal_state1, channel_id, dma_channel_operation) = scheduler environment function_state internal_state_pre_scheduling (pipelines, pending_register_memory_accesses)
Proof
INTRO_TAC THEN
ITAC PROOF_OBLIGATIONS_DMA_L2_INTERNAL_DMA_OPERATION_IMPLIES_VALID_CHANNEL_ID_LEMMA THEN
PTAC INTERNAL_DMA_OPERATION THEN
STAC
QED

val _ = export_theory();

