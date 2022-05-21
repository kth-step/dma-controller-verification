open HolKernel Parse boolLib bossLib helper_tactics;
open read_propertiesTheory write_propertiesTheory operationsTheory;

val _ = new_theory "internal_operation_properties_lemmas";

Theorem UPDATE_DEVICE_STATE_PRESERVES_REGISTER_REQUESTING_READ_ADDRESSES_LEMMA:
!device_characteristics device1 device2 channel_id internal_state channel memory.
  device2 = update_device_state device1 channel_id internal_state channel /\
  REGISTER_REQUESTING_READ_ADDRESSES device_characteristics memory device1
  ==>
  REGISTER_REQUESTING_READ_ADDRESSES device_characteristics memory device2  
Proof
INTRO_TAC THEN
ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA THEN
ITAC read_properties_lemmasTheory.EQ_PENDING_REGIESTER_RELATED_MEMORY_REQUESTS_PRESERVES_REGISTER_REQUESTING_READ_ADDRESSES_LEMMA THEN
STAC
QED

Theorem UPDATE_DEVICE_STATE_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA:
!device_characteristics device1 device2 channel_id internal_state channel memory.
  device2 = update_device_state device1 channel_id internal_state channel /\
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device1
  ==>
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device2  
Proof
INTRO_TAC THEN
ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA THEN
ITAC write_properties_lemmasTheory.EQ_PENDING_REGIESTER_RELATED_MEMORY_REQUESTS_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA THEN
STAC
QED

Theorem UPDATE_DEVICE_STATE_PRESERVED_DEVICE_REQUESTING_READ_ADDRESSES_LEMMA:
!device1 device2 channel_id internal_state2 channel2 memory device_characteristics.
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  CHANNEL_REQUESTING_READ_ADDRESSES device_characteristics.dma_characteristics.R memory channel2 /\
  DEVICE_REQUESTING_READ_ADDRESSES device_characteristics memory device1
  ==>
  DEVICE_REQUESTING_READ_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC DEVICE_REQUESTING_READ_ADDRESSES THEN
CONJ_TAC THENL
[
 ETAC DMA_REQUESTING_READ_ADDRESSES THEN
 INTRO_TAC THEN
 PTAC update_device_state THEN
 LRTAC THEN
 RW_HYPS_TAC stateTheory.schannel THEN
 RECORD_TAC THEN
 ETAC combinTheory.UPDATE_def THEN
 APP_SCALAR_TAC THEN
 IF_SPLIT_TAC THENL
 [
  ASM_REWRITE_TAC [optionTheory.THE_DEF]
  ,
  ASM_INST_IMP_ASM_TAC THEN
  STAC
 ]
 ,
 ITAC UPDATE_DEVICE_STATE_PRESERVES_REGISTER_REQUESTING_READ_ADDRESSES_LEMMA THEN STAC
]
QED

Theorem UPDATE_DEVICE_STATE_PRESERVED_DEVICE_REQUESTING_WRITE_ADDRESSES_LEMMA:
!device1 device2 channel_id internal_state2 channel2 memory device_characteristics.
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  CHANNEL_REQUESTING_WRITE_ADDRESSES device_characteristics.dma_characteristics.W memory channel2 /\
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device1
  ==>
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC DEVICE_REQUESTING_WRITE_ADDRESSES THEN
CONJ_TAC THENL
[
 ETAC DMA_REQUESTING_WRITE_ADDRESSES THEN
 INTRO_TAC THEN
 PTAC update_device_state THEN
 LRTAC THEN
 RW_HYPS_TAC stateTheory.schannel THEN
 RECORD_TAC THEN
 ETAC combinTheory.UPDATE_def THEN
 APP_SCALAR_TAC THEN
 IF_SPLIT_TAC THENL
 [
  ASM_REWRITE_TAC [optionTheory.THE_DEF]
  ,
  ASM_INST_IMP_ASM_TAC THEN
  STAC
 ]
 ,
 ITAC UPDATE_DEVICE_STATE_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA THEN STAC
]
QED

Theorem PROOF_OBLIGATION_SCHEDULER_IMPLIES_VALID_SCHEDULED_CHANNEL_LEMMA:
!device_characteristics channel_id dma_channel_operation environment function_state internal_state1 internal_state2 channels.
  PROOF_OBLIGATION_SCHEDULER device_characteristics /\
  (internal_state2, channel_id, dma_channel_operation) = device_characteristics.dma_characteristics.scheduler environment function_state internal_state1 channels
  ==>
  VALID_CHANNEL_ID device_characteristics channel_id
Proof
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_SCHEDULER THEN
AITAC THEN
STAC
QED

Theorem SCHEDULES_CHANNEL_REQUESTING_READ_ADDRESSES_LEMMA:
!device_characteristics channel device channel_id dma_channel_operation
 environment memory internal_state collected_dma_state.
  PROOF_OBLIGATION_SCHEDULER device_characteristics /\
  collected_dma_state = collect_dma_state device_characteristics.dma_characteristics device.dma_state /\
  (internal_state, channel_id, dma_channel_operation) = device_characteristics.dma_characteristics.scheduler environment device.function_state device.dma_state.internal_state collected_dma_state /\
  channel = schannel device channel_id /\
  DEVICE_REQUESTING_READ_ADDRESSES device_characteristics memory device
  ==>
  CHANNEL_REQUESTING_READ_ADDRESSES device_characteristics.dma_characteristics.R memory channel
Proof
INTRO_TAC THEN
PTAC DEVICE_REQUESTING_READ_ADDRESSES THEN
PTAC DMA_REQUESTING_READ_ADDRESSES THEN
ITAC PROOF_OBLIGATION_SCHEDULER_IMPLIES_VALID_SCHEDULED_CHANNEL_LEMMA THEN
AITAC THEN
STAC
QED

Theorem SCHEDULES_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA:
!device_characteristics channel device channel_id dma_channel_operation
 environment memory internal_state collected_dma_state.
  PROOF_OBLIGATION_SCHEDULER device_characteristics /\
  collected_dma_state = collect_dma_state device_characteristics.dma_characteristics device.dma_state /\
  (internal_state, channel_id, dma_channel_operation) = device_characteristics.dma_characteristics.scheduler environment device.function_state device.dma_state.internal_state collected_dma_state /\
  channel = schannel device channel_id /\
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device
  ==>
  CHANNEL_REQUESTING_WRITE_ADDRESSES device_characteristics.dma_characteristics.W memory channel
Proof
INTRO_TAC THEN
PTAC DEVICE_REQUESTING_WRITE_ADDRESSES THEN
PTAC DMA_REQUESTING_WRITE_ADDRESSES THEN
ITAC PROOF_OBLIGATION_SCHEDULER_IMPLIES_VALID_SCHEDULED_CHANNEL_LEMMA THEN
AITAC THEN
STAC
QED

Theorem UPDATE_DEVICE_STATE_PRESERVES_DMA_REQUESTING_READ_ADDRESSES_LEMMA:
!memory device_characteristics device1 device2
 current_channel_id current_internal_state current_channel_state.
  device2 = update_device_state device1 current_channel_id current_internal_state current_channel_state /\
  CHANNEL_REQUESTING_READ_ADDRESSES device_characteristics.dma_characteristics.R memory current_channel_state /\
  DEVICE_REQUESTING_READ_ADDRESSES device_characteristics memory device1
  ==>
  DEVICE_REQUESTING_READ_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC DEVICE_REQUESTING_READ_ADDRESSES THEN
CONJ_TAC THENL
[
 PTAC update_device_state THEN
 ETAC DMA_REQUESTING_READ_ADDRESSES THEN
 LRTAC THEN
 REWRITE_TAC [stateTheory.schannel] THEN
 RECORD_TAC THEN
 INTRO_TAC THEN
 ETAC combinTheory.UPDATE_def THEN
 APP_SCALAR_TAC THEN
 IF_SPLIT_TAC THENL
 [
  ETAC optionTheory.THE_DEF THEN STAC
  ,
  RW_HYPS_TAC stateTheory.schannel THEN AITAC THEN RECORD_TAC THEN STAC
 ]
 ,
 ITAC UPDATE_DEVICE_STATE_PRESERVES_REGISTER_REQUESTING_READ_ADDRESSES_LEMMA THEN STAC
]
QED

Theorem UPDATE_DEVICE_STATE_PRESERVES_DMA_REQUESTING_WRITE_ADDRESSES_LEMMA:
!memory device_characteristics device1 device2
 current_channel_id current_internal_state current_channel_state.
  device2 = update_device_state device1 current_channel_id current_internal_state current_channel_state /\
  CHANNEL_REQUESTING_WRITE_ADDRESSES device_characteristics.dma_characteristics.W memory current_channel_state /\
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device1
  ==>
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC DEVICE_REQUESTING_WRITE_ADDRESSES THEN
CONJ_TAC THENL
[
 PTAC update_device_state THEN
 ETAC DMA_REQUESTING_WRITE_ADDRESSES THEN
 LRTAC THEN
 REWRITE_TAC [stateTheory.schannel] THEN
 RECORD_TAC THEN
 INTRO_TAC THEN
 ETAC combinTheory.UPDATE_def THEN
 APP_SCALAR_TAC THEN
 IF_SPLIT_TAC THENL
 [
  ETAC optionTheory.THE_DEF THEN STAC
  ,
  RW_HYPS_TAC stateTheory.schannel THEN AITAC THEN RECORD_TAC THEN STAC
 ]
 ,
 ITAC UPDATE_DEVICE_STATE_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA THEN STAC
]
QED

val _ = export_theory();

