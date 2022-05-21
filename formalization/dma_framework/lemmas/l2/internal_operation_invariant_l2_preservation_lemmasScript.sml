open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory invariant_l2Theory;

val _ = new_theory "internal_operation_invariant_l2_preservation_lemmas";

Theorem SCHEDULER_OPERATION_PRESERVES_DEFINED_CHANNELS_LEMMA:
!device_characteristics channel_id device1 device2 dma_channel_operation environment.
  (device2, channel_id, dma_channel_operation) = scheduler_operation device_characteristics device1 environment /\
  DEFINED_CHANNELS device_characteristics device1
  ==>
  DEFINED_CHANNELS device_characteristics device2
Proof
INTRO_TAC THEN
ETAC DEFINED_CHANNELS THEN
ETAC VALID_CHANNELS THEN
INTRO_TAC THEN
AIRTAC THEN
PTAC operationsTheory.scheduler_operation THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 3 THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem SCHEDULER_OPERATION_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA:
!device_characteristics channel_id device1 device2 dma_channel_operation environment memory.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION device_characteristics /\
  (device2, channel_id, dma_channel_operation) = scheduler_operation device_characteristics device1 environment /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_FETCH_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_FETCH_BD_L2 THEN
INTRO_TAC THEN
RW_HYPS_TAC stateTheory.schannel THEN
PTAC operationsTheory.scheduler_operation THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 3 THEN
LRTAC THEN
RECORD_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION THEN
AIRTAC THEN
AITAC THEN
AIRTAC THEN
STAC
QED

Theorem SCHEDULER_OPERATION_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA:
!device_characteristics channel_id device1 device2 dma_channel_operation environment memory.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION device_characteristics /\
  (device2, channel_id, dma_channel_operation) = scheduler_operation device_characteristics device1 environment /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_UPDATE_BD_L2 THEN
INTRO_TAC THEN
RW_HYPS_TAC stateTheory.schannel THEN
PTAC operationsTheory.scheduler_operation THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 3 THEN
LRTAC THEN
RECORD_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION THEN
AIRTAC THEN
AITAC THEN
AIRTAC THEN
STAC
QED

Theorem SCHEDULER_OPERATION_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA:
!device_characteristics channel_id device1 device2 dma_channel_operation environment memory.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION device_characteristics /\
  (device2, channel_id, dma_channel_operation) = scheduler_operation device_characteristics device1 environment /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device1
  ==>
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_TRANSFER_DATA_L2 THEN
INTRO_TAC THEN
RW_HYPS_TAC stateTheory.schannel THEN
PTAC operationsTheory.scheduler_operation THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 3 THEN
LRTAC THEN
RECORD_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION THEN
AIRTAC THEN
AITAC THEN
AIRTAC THEN
STAC
QED

Theorem SCHEDULER_OPERATION_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA:
!device_characteristics channel_id device1 device2 dma_channel_operation environment memory.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION device_characteristics /\
  (device2, channel_id, dma_channel_operation) = scheduler_operation device_characteristics device1 environment /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_WRITE_BACK_BD_L2 THEN
INTRO_TAC THEN
RW_HYPS_TAC stateTheory.schannel THEN
PTAC operationsTheory.scheduler_operation THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 3 THEN
LRTAC THEN
RECORD_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION THEN
AIRTAC THEN
AITAC THEN
AIRTAC THEN
STAC
QED

Theorem SCHEDULER_OPERATION_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA:
!device_characteristics channel_id device1 device2 dma_channel_operation environment memory.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_SCRATCHPAD device_characteristics /\
  (device2, channel_id, dma_channel_operation) = scheduler_operation device_characteristics device1 environment /\
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device1
  ==>
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_SCRATCHPAD_R_L2 THEN
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_SCHEDULER_PRESERVES_SCRATCHPAD THEN
PTAC operationsTheory.scheduler_operation THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 3 THEN
AIRTAC THEN
RLTAC THEN
LRTAC THEN
RECORD_TAC THEN
RLTAC THEN
AIRTAC THEN
STAC
QED

Theorem SCHEDULER_OPERATION_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA:
!device_characteristics channel_id device1 device2 dma_channel_operation environment memory.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_SCRATCHPAD device_characteristics /\
  (device2, channel_id, dma_channel_operation) = scheduler_operation device_characteristics device1 environment /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device1
  ==>
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_SCRATCHPAD_W_L2 THEN
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_SCHEDULER_PRESERVES_SCRATCHPAD THEN
PTAC operationsTheory.scheduler_operation THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 3 THEN
AIRTAC THEN
RLTAC THEN
LRTAC THEN
RECORD_TAC THEN
RLTAC THEN
AIRTAC THEN
STAC
QED

Theorem SCHEDULER_OPERATION_PRESERVES_INVARIANT_L2_LEMMA:
!device_characteristics channel_id device1 device2 dma_channel_operation environment memory.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_SCRATCHPAD device_characteristics /\
  (device2, channel_id, dma_channel_operation) = scheduler_operation device_characteristics device1 environment /\
  INVARIANT_L2 device_characteristics memory device1
  ==>
  INVARIANT_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_L2 THEN
ITAC SCHEDULER_OPERATION_PRESERVES_DEFINED_CHANNELS_LEMMA THEN
ITAC SCHEDULER_OPERATION_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA THEN
ITAC SCHEDULER_OPERATION_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA THEN
ITAC SCHEDULER_OPERATION_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA THEN
ITAC SCHEDULER_OPERATION_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA THEN
ITAC SCHEDULER_OPERATION_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA THEN
ITAC SCHEDULER_OPERATION_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA THEN
STAC
QED

Theorem SCHEDULER_OPERATION_IMPLIES_VALID_CHANNEL_ID_LEMMA:
!device2 channel_id dma_channel_operation device_characteristics device1 environment.
  PROOF_OBLIGATION_SCHEDULER device_characteristics /\
  (device2, channel_id, dma_channel_operation) = scheduler_operation device_characteristics device1 environment
  ==>
  VALID_CHANNEL_ID device_characteristics channel_id
Proof
INTRO_TAC THEN
PTAC operationsTheory.scheduler_operation THEN
ETAC proof_obligationsTheory.PROOF_OBLIGATION_SCHEDULER THEN
EQ_PAIR_ASM_TAC THEN
ALL_RLTAC THEN
AIRTAC THEN
STAC
QED





(****************************************)

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_DEFINED_CHANNELS_LEMMA:
!device_characteristics device1 device2.
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1 /\
  DEFINED_CHANNELS device_characteristics device1
  ==>
  DEFINED_CHANNELS device_characteristics device2
Proof
INTRO_TAC THEN
ETAC DEFINED_CHANNELS THEN
ETAC VALID_CHANNELS THEN
INTRO_TAC THEN
AIRTAC THEN
PTAC operationsTheory.process_register_related_memory_access THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA:
!device_characteristics memory device1 device2.
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_BD_INTERPRETATION device_characteristics /\
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1 /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_FETCH_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_FETCH_BD_L2 THEN
INTRO_TAC THEN
RW_HYPS_TAC stateTheory.schannel THEN
PTAC operationsTheory.process_register_related_memory_access THEN
LRTAC THEN
RECORD_TAC THEN
REMOVE_SINGLE_VAR_EQ_ASMS_TAC THEN
RLTAC THEN
RLTAC THEN
RLTAC THEN
RLTAC THEN
RLTAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_BD_INTERPRETATION THEN
AIRTAC THEN
AITAC THEN
QRLTAC THEN
AIRTAC THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA:
!device_characteristics memory device1 device2.
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_BD_INTERPRETATION device_characteristics /\
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1 /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_UPDATE_BD_L2 THEN
INTRO_TAC THEN
RW_HYPS_TAC stateTheory.schannel THEN
PTAC operationsTheory.process_register_related_memory_access THEN
LRTAC THEN
RECORD_TAC THEN
REMOVE_SINGLE_VAR_EQ_ASMS_TAC THEN
RLTAC THEN
RLTAC THEN
RLTAC THEN
RLTAC THEN
RLTAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_BD_INTERPRETATION THEN
AIRTAC THEN
AITAC THEN
QRLTAC THEN
AIRTAC THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA:
!device_characteristics memory device1 device2.
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_BD_INTERPRETATION device_characteristics /\
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1 /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device1
  ==>
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_TRANSFER_DATA_L2 THEN
INTRO_TAC THEN
RW_HYPS_TAC stateTheory.schannel THEN
PTAC operationsTheory.process_register_related_memory_access THEN
LRTAC THEN
RECORD_TAC THEN
REMOVE_SINGLE_VAR_EQ_ASMS_TAC THEN
RLTAC THEN
RLTAC THEN
RLTAC THEN
RLTAC THEN
RLTAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_BD_INTERPRETATION THEN
AIRTAC THEN
AITAC THEN
QRLTAC THEN
AIRTAC THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA:
!device_characteristics memory device1 device2.
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1 /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_WRITE_BACK_BD_L2 THEN
INTRO_TAC THEN
RW_HYPS_TAC stateTheory.schannel THEN
PTAC operationsTheory.process_register_related_memory_access THEN
LRTAC THEN
RECORD_TAC THEN
REMOVE_SINGLE_VAR_EQ_ASMS_TAC THEN
RLTAC THEN
RLTAC THEN
AIRTAC THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA:
!device_characteristics memory device1 device2.
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_SCRATCHPAD device_characteristics /\
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1 /\
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device1
  ==>
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_SCRATCHPAD_R_L2 THEN
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_SCRATCHPAD THEN
PTAC operationsTheory.process_register_related_memory_access THEN
LRTAC THEN
RECORD_TAC THEN
REMOVE_SINGLE_VAR_EQ_ASMS_TAC THEN
RLTAC THEN
AIRTAC THEN
AIRTAC THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA:
!device_characteristics memory device1 device2.
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_SCRATCHPAD device_characteristics /\
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1 /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device1
  ==>
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_SCRATCHPAD_W_L2 THEN
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_SCRATCHPAD THEN
PTAC operationsTheory.process_register_related_memory_access THEN
LRTAC THEN
RECORD_TAC THEN
REMOVE_SINGLE_VAR_EQ_ASMS_TAC THEN
RLTAC THEN
AIRTAC THEN
AIRTAC THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_L2_LEMMA:
!device_characteristics memory device1 device2.
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_SCRATCHPAD device_characteristics /\
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1 /\
  INVARIANT_L2 device_characteristics memory device1
  ==>
  INVARIANT_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_L2 THEN
ITAC PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_DEFINED_CHANNELS_LEMMA THEN
ITAC PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA THEN
ITAC PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA THEN
ITAC PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA THEN
ITAC PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA THEN
ITAC PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA THEN
ITAC PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA THEN
STAC
QED

(****************************************)





Theorem DMA_OPERATION_PRESERVES_DEFINED_CHANNELS_LEMMA:
!device_characteristics channel_operation memory environment device1 device2 channel_id dma_channel_operation.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  device2 = dma_operation device_characteristics channel_operation memory environment (device1, channel_id, dma_channel_operation) /\
  DEFINED_CHANNELS device_characteristics device1
  ==>
  DEFINED_CHANNELS device_characteristics device2
Proof
INTRO_TAC THEN
ETAC DEFINED_CHANNELS THEN
ETAC VALID_CHANNELS THEN
INTRO_TAC THEN
PTAC operationsTheory.dma_operation THEN
RLTAC THEN
LRTAC THEN
ETAC operationsTheory.update_device_state THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 LEMMA_TAC optionTheory.IS_SOME_DEF
 ,
 AIRTAC THEN
 STAC
]
QED

Theorem DMA_OPERATION_PRESERVES_INVARIANT_FETCH_UPDATE_PROCESS_WRITE_BACK_BD_SCRATCHPAD_L2_LEMMA:
!device_characteristics memory environment device1 device2 channel_id dma_channel_operation.
  PROOF_OBLIGATION_FETCH_BD_PRESERVES_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_UPDATE_BD_PRESERVES_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_BD_PRESERVES_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_FETCHING_BD_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_UPDATING_BD_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_PRESERVES_BD_INTERPRETATION device_characteristics /\

  VALID_CHANNEL_ID device_characteristics channel_id /\
  device2 = dma_operation device_characteristics channel_operation_l2 (SOME memory) environment (device1, channel_id, dma_channel_operation) /\

  INVARIANT_L2 device_characteristics memory device1
  ==>
  INVARIANT_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_L2 THEN
ITAC DMA_OPERATION_PRESERVES_DEFINED_CHANNELS_LEMMA THEN
PTAC operationsTheory.dma_operation THEN
PTAC l2Theory.channel_operation_l2 THEN
EQ_PAIR_ASM_TAC THEN
NLRTAC 2 THEN
PTAC l2Theory.channel_operation_case_l2 THENL
[
 IRTAC fetch_bd_invariant_l2_preservation_lemmasTheory.FETCHING_BD_L2_PRESERVES_FETCH_UPDATE_PROCESS_WRITE_BACK_SCRATCHPAD_LEMMA THEN
 STAC
 ,
 IRTAC update_bd_invariant_l2_preservation_lemmasTheory.UPDATING_BD_L2_PRESERVES_FETCH_UPDATE_PROCESS_WRITE_BACK_SCRATCHPAD_LEMMA THEN
 STAC
 ,
 IRTAC process_bd_invariant_l2_preservation_lemmasTheory.PROCESSING_BD_L2_PRESERVES_FETCH_UPDATE_PROCESS_WRITE_BACK_SCRATCHPAD_LEMMA THEN
 STAC
 ,
 IRTAC write_back_bd_invariant_l2_preservation_lemmasTheory.WRITING_BACK_BD_L2_PRESERVES_FETCH_UPDATE_PROCESS_WRITE_BACK_SCRATCHPAD_LEMMA THEN
 STAC
]
QED





Theorem SCHEDULER_DMA_OPERATION_PRESERVES_INVARIANT_L2_LEMMA:
!device_characteristics memory environment device1 device2.
  PROOF_OBLIGATION_INTERNAL_DEVICE_OPERATION_L2 device_characteristics /\
  device2 = scheduler_dma_operation device_characteristics channel_operation_l2 (SOME memory) environment device1 /\
  INVARIANT_L2 device_characteristics memory device1
  ==>
  INVARIANT_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC proof_obligations_dma_l2Theory.PROOF_OBLIGATION_INTERNAL_DEVICE_OPERATION_L2 THEN
PTAC operationsTheory.scheduler_dma_operation THEN
ITAC SCHEDULER_OPERATION_IMPLIES_VALID_CHANNEL_ID_LEMMA THEN
IRTAC SCHEDULER_OPERATION_PRESERVES_INVARIANT_L2_LEMMA THEN
IRTAC DMA_OPERATION_PRESERVES_INVARIANT_FETCH_UPDATE_PROCESS_WRITE_BACK_BD_SCRATCHPAD_L2_LEMMA THEN
STAC
QED

Theorem INTERNAL_DMA_OPERATION_PRESERVES_INVARIANT_L2_LEMMA:
!device_characteristics memory environment device1 device2.
  PROOF_OBLIGATION_INTERNAL_DEVICE_OPERATION_L2 device_characteristics /\
  device2 = internal_dma_operation device_characteristics channel_operation_l2 (SOME memory) environment device1 /\
  INVARIANT_L2 device_characteristics memory device1
  ==>
  INVARIANT_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC proof_obligations_dma_l2Theory.PROOF_OBLIGATION_INTERNAL_DEVICE_OPERATION_L2 THEN
ETAC internal_operation_lemmasTheory.SCHEDULER_DMA_OPERATION_EQ_INTERNAL_DMA_OPERATION_LEMMA THEN
IRTAC (REWRITE_RULE [proof_obligations_dma_l2Theory.PROOF_OBLIGATION_INTERNAL_DEVICE_OPERATION_L2] SCHEDULER_DMA_OPERATION_PRESERVES_INVARIANT_L2_LEMMA) THEN
STAC
QED

Theorem INTERNAL_FUNCTION_OPERATION_PRESERVES_INVARIANT_L2_LEMMA:
!device_characteristics device1 device2 memory environment.
  device2 = internal_function_operation (THE device_characteristics.function_characteristics) environment device1 /\
  INVARIANT_L2 device_characteristics memory device1
  ==>
  INVARIANT_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC operationsTheory.internal_function_operation THEN
LRTAC THEN
ETAC INVARIANT_L2 THEN
CONJS_TAC THENL
[
 ETAC DEFINED_CHANNELS THEN ETAC VALID_CHANNELS THEN RECORD_TAC THEN STAC
 ,
 ETAC INVARIANT_FETCH_BD_L2 THEN RW_HYPS_TAC stateTheory.schannel THEN REWRITE_TAC [stateTheory.schannel] THEN RECORD_TAC THEN STAC
 ,
 ETAC INVARIANT_UPDATE_BD_L2 THEN RW_HYPS_TAC stateTheory.schannel THEN REWRITE_TAC [stateTheory.schannel] THEN RECORD_TAC THEN STAC
 ,
 ETAC INVARIANT_TRANSFER_DATA_L2 THEN RW_HYPS_TAC stateTheory.schannel THEN REWRITE_TAC [stateTheory.schannel] THEN RECORD_TAC THEN STAC
 ,
 ETAC INVARIANT_WRITE_BACK_BD_L2 THEN RW_HYPS_TAC stateTheory.schannel THEN REWRITE_TAC [stateTheory.schannel] THEN RECORD_TAC THEN STAC
 ,
 ETAC INVARIANT_SCRATCHPAD_R_L2 THEN RECORD_TAC THEN STAC
 ,
 ETAC INVARIANT_SCRATCHPAD_W_L2 THEN RECORD_TAC THEN STAC
]
QED

Theorem INTERNAL_DEVICE_OPERATION_PRESERVES_INVARIANT_L2_LEMMA:
!device_characteristics memory environment device1 device2.
  PROOF_OBLIGATION_INTERNAL_DEVICE_OPERATION_L2 device_characteristics /\
  device2 = internal_device_operation_l2 device_characteristics memory environment device1 /\
  INVARIANT_L2 device_characteristics memory device1
  ==>
  INVARIANT_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC l2Theory.internal_device_operation_l2 THEN
PTAC operationsTheory.internal_device_operation THENL
[
 STAC
 ,
 IRTAC INTERNAL_DMA_OPERATION_PRESERVES_INVARIANT_L2_LEMMA THEN STAC
 ,
 PTAC proof_obligations_dma_l2Theory.PROOF_OBLIGATION_INTERNAL_DEVICE_OPERATION_L2 THEN
 IRTAC PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_L2_LEMMA THEN STAC
 ,
 IRTAC INTERNAL_FUNCTION_OPERATION_PRESERVES_INVARIANT_L2_LEMMA THEN STAC
]
QED

val _ = export_theory();

