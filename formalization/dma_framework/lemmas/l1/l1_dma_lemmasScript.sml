open HolKernel Parse boolLib bossLib helper_tactics;
open l1Theory proof_obligationsTheory read_propertiesTheory write_propertiesTheory;

val _ = new_theory "l1_dma_lemmas";

Theorem CHANNEL_OPERATION_L1_PRESERVES_CHANNEL_REQUESTING_ACCESSES_LEMMA:
!device_characteristics dma_channel_operation memory environment internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_UPDATE_WRITES_DECLARED device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_WRITES_DECLARED device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = channel_operation_l1 device_characteristics channel_id dma_channel_operation (SOME memory) environment internal_state1 channel1 /\
  CHANNEL_REQUESTING_READ_ADDRESSES device_characteristics.dma_characteristics.R memory channel1 /\
  CHANNEL_REQUESTING_WRITE_ADDRESSES device_characteristics.dma_characteristics.W memory channel1
  ==>
  CHANNEL_REQUESTING_READ_ADDRESSES device_characteristics.dma_characteristics.R memory channel2 /\
  CHANNEL_REQUESTING_WRITE_ADDRESSES device_characteristics.dma_characteristics.W memory channel2
Proof
INTRO_TAC THEN
PTAC channel_operation_l1 THEN PTAC channel_operation_case_l1 THENL
[
 EQ_PAIR_ASM_TAC THEN
 ITAC l1_fetching_bd_lemmasTheory.FETCHING_BD_L1_PRESERVES_CHANNEL_REQUESTING_ACCESSES_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ITAC l1_updating_bd_lemmasTheory.UPDATING_BD_L1_PRESERVES_CHANNEL_REQUESTING_ACCESSES_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ITAC l1_transferring_data_lemmasTheory.TRANSFERRING_DATA_L1_PRESERVES_CHANNEL_REQUESTING_ACCESSES_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ITAC l1_writing_back_bd_lemmasTheory.WRITING_BACK_BD_L1_PRESERVES_CHANNEL_REQUESTING_ACCESSES_LEMMA THEN
 STAC
]
QED

Theorem CHANNEL_OPERATION_L1_DEVICE_PRESERVES_DEVICE_REQUESTING_ACCESSES_LEMMA:
!device_characteristics memory environment device1 device2.
  PROOF_OBLIGATION_SCHEDULER device_characteristics /\
  PROOF_OBLIGATION_UPDATE_WRITES_DECLARED device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_WRITES_DECLARED device_characteristics /\
  device2 = internal_dma_operation device_characteristics channel_operation_l1 (SOME memory) environment device1 /\
  DEVICE_REQUESTING_READ_ADDRESSES device_characteristics memory device1 /\
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device1
  ==>
  DEVICE_REQUESTING_READ_ADDRESSES device_characteristics memory device2 /\
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC operationsTheory.internal_dma_operation THEN
ITAC internal_operation_properties_lemmasTheory.SCHEDULES_CHANNEL_REQUESTING_READ_ADDRESSES_LEMMA THEN
ITAC internal_operation_properties_lemmasTheory.SCHEDULES_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA THEN
ITAC internal_operation_properties_lemmasTheory.PROOF_OBLIGATION_SCHEDULER_IMPLIES_VALID_SCHEDULED_CHANNEL_LEMMA THEN
ETAC stateTheory.schannel THEN
ITAC CHANNEL_OPERATION_L1_PRESERVES_CHANNEL_REQUESTING_ACCESSES_LEMMA THEN
ITAC internal_operation_properties_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVED_DEVICE_REQUESTING_READ_ADDRESSES_LEMMA THEN
ITAC internal_operation_properties_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVED_DEVICE_REQUESTING_WRITE_ADDRESSES_LEMMA THEN
STAC
QED

Theorem CHANNEL_OPERATION_L1_DEVICE_PRESERVES_INVARIANT_LEMMA:
!device_characteristics memory environment device1 device2.
  PROOF_OBLIGATION_SCHEDULER device_characteristics /\
  PROOF_OBLIGATION_UPDATE_WRITES_DECLARED device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_WRITES_DECLARED device_characteristics /\
  device2 = internal_dma_operation device_characteristics channel_operation_l1 (SOME memory) environment device1 /\
  INVARIANT_L1 device_characteristics memory device1
  ==>
  INVARIANT_L1 device_characteristics memory device2
Proof
REWRITE_TAC [invariant_l1Theory.INVARIANT_L1, CHANNEL_OPERATION_L1_DEVICE_PRESERVES_DEVICE_REQUESTING_ACCESSES_LEMMA]
QED

Theorem ALL_DMA_CHANNELS_EQ_PENDING_ACCESSES_PRESERVES_INVARIANT_L1_LEMMA:
!device_characteristics memory (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
                               (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  (!channel_id.
     (schannel device2 channel_id).pending_accesses = (schannel device1 channel_id).pending_accesses) /\
  device2.dma_state.pending_register_related_memory_requests = device1.dma_state.pending_register_related_memory_requests /\
  INVARIANT_L1 device_characteristics memory device1
  ==>
  INVARIANT_L1 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC invariant_l1Theory.INVARIANT_L1 THEN
CONJ_TAC THENL
[
 MATCH_MP_TAC read_properties_lemmasTheory.ALL_DMA_CHANNELS_EQ_PENDING_ACCESSES_PRESERVES_DEVICE_REQUESTING_READ_ADDRESSES_LEMMA THEN
 PAXTAC THEN
 STAC
 ,
 MATCH_MP_TAC write_properties_lemmasTheory.ALL_DMA_CHANNELS_EQ_PENDING_ACCESSES_PRESERVES_DEVICE_REQUESTING_WRITE_ADDRESSES_LEMMA THEN
 PAXTAC THEN
 STAC
]
QED

Theorem WRITABLE_WRITE_REQUEST_PRESERVES_INVARIANT_L1_LEMMA:
!device_characteristics address_bytes tag device memory1 memory2.
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l1 device_characteristics device) /\
  memory2 = update_memory memory1 address_bytes /\
  INVARIANT_L1 device_characteristics memory1 device
  ==>
  INVARIANT_L1 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC dma_pending_requests_l1 THEN
ETAC invariant_l1Theory.INVARIANT_L1 THEN
ITAC dma_pending_requests_properties_lemmasTheory.PROOF_OBLIGATION_READABLE_WRITABLE_DEVICE_REQUESTING_WRITE_ADDRESSES_IMPLIES_MEMORY_WRITES_PRESERVE_R_W_LEMMA THEN
ITAC read_properties_lemmasTheory.EQ_READABLE_PRESERVES_DEVICE_REQUESTING_READ_ADDRESSES_LEMMA THEN
ITAC write_properties_lemmasTheory.EQ_READABLE_PRESERVES_DEVICE_REQUESTING_WRITE_ADDRESSES_LEMMA THEN
STAC
QED

Theorem IS_VALID_IMPLIES_REQUEST_VALIDATION_READABLE_LEMMA:
!device_characteristics memory device.
  REQUEST_VALIDATION_READABLE device_characteristics.dma_characteristics.R memory (is_valid_l1 device_characteristics memory device)
Proof
REPEAT GEN_TAC THEN
ETAC REQUEST_VALIDATION_READABLE THEN
INTRO_TAC THEN
ETAC is_valid_l1 THEN
ETAC access_propertiesTheory.is_valid_readable_writable THEN
STAC
QED

Theorem IS_VALID_IMPLIES_REQUEST_VALIDATION_WRITABLE_LEMMA:
!device_characteristics memory device.
  REQUEST_VALIDATION_WRITABLE device_characteristics.dma_characteristics.W memory (is_valid_l1 device_characteristics memory device)
Proof
REPEAT GEN_TAC THEN
ETAC REQUEST_VALIDATION_WRITABLE THEN
INTRO_TAC THEN
ETAC is_valid_l1 THEN
ETAC access_propertiesTheory.is_valid_readable_writable THEN
STAC
QED

Theorem DMA_REGISTER_WRITE_PRESERVES_INVARIANT_L1_LEMMA:
!device_characteristics is_valid device1 device2 memory memory_option addresses write_requests.
  is_valid = is_valid_l1 device_characteristics memory device1 /\
  REQUEST_VALIDATION_READABLE device_characteristics.dma_characteristics.R memory is_valid /\
  REQUEST_VALIDATION_WRITABLE device_characteristics.dma_characteristics.W memory is_valid /\
  (device2, write_requests) = dma_register_write device_characteristics is_valid memory_option device1 addresses /\
  INVARIANT_L1 device_characteristics memory device1
  ==>
  INVARIANT_L1 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC invariant_l1Theory.INVARIANT_L1 THEN
ITAC dma_register_write_properties_lemmasTheory.DMA_REGISTER_WRITE_PRESERVES_DEVICE_REQUESTING_READ_WRITE_ADDRESSES_LEMMA THEN
STAC
QED

Theorem FUNCTION_REGISTER_WRITE_PRESERVES_INVARIANT_L1_LEMMA:
!memory device_characteristics device1 device2 address_bytes.
  device2 = function_register_write device_characteristics device1 address_bytes /\
  INVARIANT_L1 device_characteristics memory device1
  ==>
  INVARIANT_L1 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC invariant_l1Theory.INVARIANT_L1 THEN
ITAC function_register_write_properties_lemmasTheory.FUNCTION_REGISTER_WRITE_PRESERVES_DEVICE_REQUESTING_READ_WRITE_ADDRESSES_LEMMA THEN
STAC
QED

Theorem DEVICE_REGISTER_WRITE_L1_PRESERVES_L1_INVARIANT_LEMMA:
!device_characteristics device1 device2 memory address_bytes write_requests.
  (device2, write_requests) = device_register_write_l1 device_characteristics memory device1 address_bytes /\
  INVARIANT_L1 device_characteristics memory device1
  ==>
  INVARIANT_L1 device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC l1Theory.device_register_write_l1 THEN
PTAC operationsTheory.device_register_write THENL
[
 MATCH_MP_TAC DMA_REGISTER_WRITE_PRESERVES_INVARIANT_L1_LEMMA THEN
 PAXTAC THEN
 ASM_REWRITE_TAC [IS_VALID_IMPLIES_REQUEST_VALIDATION_READABLE_LEMMA, IS_VALID_IMPLIES_REQUEST_VALIDATION_WRITABLE_LEMMA]
 ,
 EQ_PAIR_ASM_TAC THEN ITAC FUNCTION_REGISTER_WRITE_PRESERVES_INVARIANT_L1_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem DMA_REQUEST_SERVED_PRESERVES_INVARIANT_L1_LEMMA:
!memory device_characteristics device1 device2 reply.
  device2 = dma_request_served device_characteristics device1 reply /\
  INVARIANT_L1 device_characteristics memory device1
  ==>
  INVARIANT_L1 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC invariant_l1Theory.INVARIANT_L1 THEN
ITAC dma_request_served_properties_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_DEVICE_REQUESTING_READ_WRITE_ADDRESSES_LEMMA THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_L1_LEMMA:
!device_characteristics device1 device2 memory.
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1 /\
  INVARIANT_L1 device_characteristics memory device1
  ==>
  INVARIANT_L1 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC invariant_l1Theory.INVARIANT_L1 THEN
IRTAC process_register_related_memory_access_properties_lemmasTheory.PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_DEVICE_REQUESTING_READ_WRITE_ADDRESSES_LEMMA THEN
STAC
QED

Theorem UPDATING_INTERNAL_STATE_PRESERVES_INVARIANT_L1_LEMMA:
!device_characteristics device1 device2 internal_state2 memory.
  device2 = device1 with dma_state := device1.dma_state with internal_state := internal_state2 /\
  INVARIANT_L1 device_characteristics memory device1
  ==>
  INVARIANT_L1 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC invariant_l1Theory.INVARIANT_L1 THEN
ITAC read_properties_lemmasTheory.UPDATING_INTERNAL_STATE_PRESERVES_DEVICE_REQUESTING_READ_ADDRESSES_LEMMA THEN
ITAC write_properties_lemmasTheory.UPDATING_INTERNAL_STATE_PRESERVES_DEVICE_REQUESTING_WRITE_ADDRESSES_LEMMA THEN
STAC
QED

val _ = export_theory();

