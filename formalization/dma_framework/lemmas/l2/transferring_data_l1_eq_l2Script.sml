open HolKernel Parse boolLib bossLib helper_tactics;
open proof_obligations_dma_l2Theory operationsTheory;
open invariant_l2Theory l1Theory l2Theory;

val _ = new_theory "transferring_data_l1_eq_l2";

Theorem TRANSFERRING_DATA_L2_EQ_L1_LEMMA:
!device_characteristics environment device1 internal_state_pre_scheduling
 internal_state1 channel1 function_state scheduler channel_id memory
 dma_channel_operation pipelines pending_register_memory_accesses.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  INVARIANT_L2 device_characteristics memory device1 /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation
  ==>
  (transferring_data_l2 device_characteristics channel_id memory internal_state1 channel1 =
   transferring_data_l1 device_characteristics channel_id memory internal_state1 channel1)
Proof
INTRO_TAC THEN
PTAC transferring_data_l2 THEN PTAC transferring_data_l1 THENL
[
 STAC
 ,
 ITAC invariant_l2_lemmasTheory.INVARIANT_L2_NEW_REQUESTS_R_W_LEMMA THEN CONTR_ASMS_TAC
 ,
 STAC
 ,
 STAC
]
QED

val _ = export_theory();

