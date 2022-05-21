open HolKernel Parse boolLib bossLib helper_tactics;
open operationsTheory invariant_l1Theory proof_obligations_cpu_l1Theory proof_obligations_dma_l1Theory;

val _ = new_theory "l1_system";

Theorem SYSTEM_CPU_INTERNAL_OPERATION_PRESERVES_L1_INVARIANT_LEMMA:
!device_characteristics cpu_transition memory1 memory2 device1 device2 cpu1 cpu2.
  INVARIANT_L1 device_characteristics memory1 device1 /\
  system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1,memory1,device1) cpu_internal_operation (cpu2,memory2,device2)
  ==>
  INVARIANT_L1 device_characteristics memory2 device2
Proof
REPEAT GEN_TAC THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
EQ_PAIR_ASM_TAC THEN
ALL_LRTAC THEN
STAC
QED

Theorem SYSTEM_CPU_MEMORY_READ_PRESERVES_L1_INVARIANT_LEMMA:
!device_characteristics cpu_transition memory1 memory2 device1 device2 cpu1 cpu2 address_bytes.
  INVARIANT_L1 device_characteristics memory1 device1 /\
  system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1,memory1,device1) (cpu_memory_read address_bytes) (cpu2,memory2,device2)
  ==>
  INVARIANT_L1 device_characteristics memory2 device2
Proof
REPEAT GEN_TAC THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
EQ_PAIR_ASM_TAC THEN
ALL_LRTAC THEN
STAC
QED











Theorem PENDING_CHANNEL_MEMORY_REQUEST_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA:
!device_characteristics channel_id channel device request.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channel = schannel device channel_id /\
  MEM request (channel_pending_requests channel.pending_accesses.requests)
  ==>
  DMAC_CAN_ACCESS_MEMORY device_characteristics device
Proof
INTRO_TAC THEN
ETAC proof_obligationsTheory.DMAC_CAN_ACCESS_MEMORY THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
ETAC proof_obligationsTheory.NO_CHANNEL_MEMORY_REQUESTS THEN
CCONTR_TAC THEN
ETAC boolTheory.NOT_CLAUSES THEN
AIRTAC THEN
ETAC operationsTheory.channel_pending_requests THEN
ALL_LRTAC THEN
ETAC operationsTheory.collect_pending_fetch_bd_request THEN
ETAC listTheory.APPEND THEN
ETAC listTheory.MEM THEN
STAC
QED

Theorem CPU_MEMORY_WRITE_PRESERVES_DMA_REQUESTING_READ_ADDRESSES_LEMMA:
!INVARIANT_CPU cpu_transition
 (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory1 memory2 cpu1 cpu2 address_bytes.
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes /\
  DMA_REQUESTING_READ_ADDRESSES device_characteristics memory1 device
  ==>
  DMA_REQUESTING_READ_ADDRESSES device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC read_propertiesTheory.DMA_REQUESTING_READ_ADDRESSES THEN
INTRO_TAC THEN
RW_HYPS_TAC read_propertiesTheory.CHANNEL_REQUESTING_READ_ADDRESSES THEN
ETAC read_propertiesTheory.CHANNEL_REQUESTING_READ_ADDRESSES THEN
PTAC PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY THEN
INTRO_TAC THEN
AITAC THEN
ITAC PENDING_CHANNEL_MEMORY_REQUEST_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA THEN
RW_HYPS_TAC DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
AIRTAC THEN
AIRTAC THEN
AIRTAC THEN
ETAC stateTheory.R_W_EQ THEN
STAC
QED

Theorem CPU_MEMORY_WRITE_PRESERVES_DMA_REQUESTING_WRITE_ADDRESSES_LEMMA:
!INVARIANT_CPU cpu_transition
 (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory1 memory2 cpu1 cpu2 address_bytes.
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes /\
  DMA_REQUESTING_WRITE_ADDRESSES device_characteristics memory1 device
  ==>
  DMA_REQUESTING_WRITE_ADDRESSES device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC write_propertiesTheory.DMA_REQUESTING_WRITE_ADDRESSES THEN
INTRO_TAC THEN
RW_HYPS_TAC write_propertiesTheory.CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
ETAC write_propertiesTheory.CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
PTAC PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY THEN
INTRO_TAC THEN
AITAC THEN
RW_HYPS_TAC DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
ITAC PENDING_CHANNEL_MEMORY_REQUEST_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA THEN
AIRTAC THEN
AIRTAC THEN
AIRTAC THEN
ETAC stateTheory.R_W_EQ THEN
STAC
QED

Theorem PENDING_REGISTER_RELATED_MEMORY_REQUEST_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 request.
  MEM request device.dma_state.pending_register_related_memory_requests
  ==>
  DMAC_CAN_ACCESS_MEMORY device_characteristics device
Proof
INTRO_TAC THEN
ETAC proof_obligationsTheory.DMAC_CAN_ACCESS_MEMORY THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
CCONTR_TAC THEN
ETAC boolTheory.NOT_CLAUSES THEN
ETAC proof_obligationsTheory.NO_REGISTER_RELATED_MEMORY_REQUEST THEN
LRTAC THEN
ETAC listTheory.MEM THEN
STAC
QED

Theorem CPU_MEMORY_WRITE_PRESERVES_REGISTER_REQUESTING_READ_ADDRESSES_LEMMA:
!INVARIANT_CPU cpu_transition
 (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory1 memory2 cpu1 cpu2 address_bytes.
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes /\
  REGISTER_REQUESTING_READ_ADDRESSES device_characteristics memory1 device
  ==>
  REGISTER_REQUESTING_READ_ADDRESSES device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC read_propertiesTheory.REGISTER_REQUESTING_READ_ADDRESSES THEN
INTRO_TAC THEN
AITAC THEN
PTAC PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY THEN
AITAC THEN
RW_HYPS_TAC DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
ITAC PENDING_REGISTER_RELATED_MEMORY_REQUEST_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA THEN
AIRTAC THEN
ETAC stateTheory.R_W_EQ THEN
STAC
QED

Theorem CPU_MEMORY_WRITE_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA:
!INVARIANT_CPU cpu_transition
 (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory1 memory2 cpu1 cpu2 address_bytes.
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes /\
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory1 device
  ==>
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC write_propertiesTheory.REGISTER_REQUESTING_WRITE_ADDRESSES THEN
INTRO_TAC THEN
AITAC THEN
PTAC PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY THEN
AITAC THEN
RW_HYPS_TAC DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
ITAC PENDING_REGISTER_RELATED_MEMORY_REQUEST_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA THEN
AIRTAC THEN
ETAC stateTheory.R_W_EQ THEN
STAC
QED

Theorem CPU_MEMORY_WRITE_PRESERVES_INVARIANT_L1_LEMMA:
!INVARIANT_CPU cpu_transition
 (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory1 memory2 cpu1 cpu2 address_bytes.
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes /\
  INVARIANT_L1 device_characteristics memory1 device
  ==>
  INVARIANT_L1 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC INVARIANT_L1 THEN
ETAC read_propertiesTheory.DEVICE_REQUESTING_READ_ADDRESSES THEN
ETAC write_propertiesTheory.DEVICE_REQUESTING_WRITE_ADDRESSES THEN
ITAC CPU_MEMORY_WRITE_PRESERVES_REGISTER_REQUESTING_READ_ADDRESSES_LEMMA THEN
ITAC CPU_MEMORY_WRITE_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA THEN
ITAC CPU_MEMORY_WRITE_PRESERVES_DMA_REQUESTING_READ_ADDRESSES_LEMMA THEN
ITAC CPU_MEMORY_WRITE_PRESERVES_DMA_REQUESTING_WRITE_ADDRESSES_LEMMA THEN
STAC
QED















Theorem SYSTEM_CPU_MEMORY_WRITE_PRESERVES_L1_INVARIANT_LEMMA:
!INVARIANT_CPU device_characteristics cpu_transition memory1 memory2 device1 device2 cpu1 cpu2 address_bytes.
  PROOF_OBLIGATIONS_DMA_L1 device_characteristics /\
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_L1 device_characteristics memory1 device1 /\
  system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1,memory1,device1) (cpu_memory_write address_bytes) (cpu2,memory2,device2)
  ==>
  INVARIANT_L1 device_characteristics memory2 device2
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
EQ_PAIR_ASM_TAC THEN
ETAC operationsTheory.system_transition_labels_type_11 THEN
ALL_RLTAC THEN
ITAC CPU_MEMORY_WRITE_PRESERVES_INVARIANT_L1_LEMMA THEN
ITAC append_external_abstract_bds_l1Theory.DEVICE_TRANSITION_L1_EXTERNAL_BDS_APPENDED_PRESERVES_INVARIANT_L1_LEMMA THEN
STAC
QED

Theorem R_W_EQ_PRESERVES_INVARIANT_L1_LEMMA:
!device_characteristics memory1 memory2 device.
  R_W_EQ device_characteristics memory1 memory2 /\
  INVARIANT_L1 device_characteristics memory1 device
  ==>
  INVARIANT_L1 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC stateTheory.R_W_EQ THEN
ETAC INVARIANT_L1 THEN
CONJS_TAC THENL
[
 ETAC read_propertiesTheory.DEVICE_REQUESTING_READ_ADDRESSES THEN
 CONJS_TAC THENL
 [
  ETAC read_propertiesTheory.DMA_REQUESTING_READ_ADDRESSES THEN
  INTRO_TAC THEN
  AIRTAC THEN
  ETAC read_propertiesTheory.CHANNEL_REQUESTING_READ_ADDRESSES THEN
  STAC
  ,
  ETAC read_propertiesTheory.REGISTER_REQUESTING_READ_ADDRESSES THEN
  STAC
 ]
 ,
 ETAC write_propertiesTheory.DEVICE_REQUESTING_WRITE_ADDRESSES THEN
 CONJS_TAC THENL
 [
  ETAC write_propertiesTheory.DMA_REQUESTING_WRITE_ADDRESSES THEN
  INTRO_TAC THEN
  AIRTAC THEN
  ETAC write_propertiesTheory.CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
  STAC
  ,
  ETAC write_propertiesTheory.REGISTER_REQUESTING_WRITE_ADDRESSES THEN
  STAC
 ]
]
QED

Theorem FUNCTION_REGISTER_READ_PRESERVES_MEMORY_LEMMA:
!device_characteristics device1 device2 addresses dma_address_bytes bytes memory1 memory2.
  (device2, dma_address_bytes, bytes) = function_register_read device_characteristics device1 addresses /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  memory2 = memory1
Proof
INTRO_TAC THEN
PTAC operationsTheory.function_register_read THEN
EQ_PAIR_ASM_TAC THEN
IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
STAC
QED

Theorem VALID_L1_WRITE_REQUEST_IMPLIES_W_LEMMA:
!device_characteristics memory device new_requests requests address_bytes tag address byte is_valid.
  is_valid = is_valid_l1 device_characteristics memory device /\
  requests = FILTER is_valid new_requests /\
  MEM (request_write address_bytes tag) requests /\
  MEM (address, byte) address_bytes
  ==>
  device_characteristics.dma_characteristics.W memory address
Proof
INTRO_TAC THEN
LRTAC THEN
LRTAC THEN
ETAC listTheory.MEM_FILTER THEN
PTAC l1Theory.is_valid_l1 THEN
PTAC access_propertiesTheory.is_valid_readable_writable THEN
ETAC listTheory.EVERY_MEM THEN
IRTAC lists_lemmasTheory.MEM_ADDRESS_BYTE_IMPLIES_MEM_ADDRESS_LEMMA THEN
AIRTAC THEN
STAC
QED

Theorem DEVICE_REGISTER_READ_L1_WRITE_WRITABLE_MEMORY_LEMMA:
!device_characteristics memory device1 device2 cpu_address_bytes dma_address_bytes.
  (device2, dma_address_bytes, MAP SND cpu_address_bytes) = device_register_read_l1 device_characteristics memory device1 (MAP FST cpu_address_bytes)
  ==>
  EVERY (device_characteristics.dma_characteristics.W memory) (MAP FST dma_address_bytes)
Proof
INTRO_TAC THEN
PTAC l1Theory.device_register_read_l1 THEN
PTAC operationsTheory.device_register_read THENL
[
 WEAKEN_TAC (fn term => (not o is_eq) term) THEN
 PTAC operationsTheory.dma_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 3 THEN
 IRTAC write_properties_lemmasTheory.WRITE_REQUESTS_IMPLIES_WRITE_REQUEST_LEMMA THEN
 ETAC listTheory.EVERY_MEM THEN
 INTRO_TAC THEN
 IRTAC lists_lemmasTheory.MEM_ADDRESS_IMPLIES_MEM_ADDRESS_BYTES_LEMMA THEN
 AXTAC THEN
 AIRTAC THEN
 AXTAC THEN
 IRTAC VALID_L1_WRITE_REQUEST_IMPLIES_W_LEMMA THEN
 STAC
 ,
 PTAC operationsTheory.function_register_read THEN EQ_PAIR_ASM_TAC THEN LRTAC THEN REWRITE_TAC [listTheory.MAP, listTheory.EVERY_DEF]
 ,
 EQ_PAIR_ASM_TAC THEN LRTAC THEN REWRITE_TAC [listTheory.MAP, listTheory.EVERY_DEF] 
 ,
 EQ_PAIR_ASM_TAC THEN LRTAC THEN REWRITE_TAC [listTheory.MAP, listTheory.EVERY_DEF] 
]
QED

Theorem DEVICE_REGISTER_WRITE_L1_WRITE_WRITABLE_MEMORY_LEMMA:
!device_characteristics memory device1 device2 cpu_address_bytes dma_address_bytes.
  (device2, dma_address_bytes) = device_register_write_l1 device_characteristics memory device1 cpu_address_bytes
  ==>
  EVERY (device_characteristics.dma_characteristics.W memory) (MAP FST dma_address_bytes)
Proof
INTRO_TAC THEN
PTAC l1Theory.device_register_write_l1 THEN
PTAC operationsTheory.device_register_write THENL
[
 WEAKEN_TAC (fn term => (not o is_eq) term) THEN
 PTAC operationsTheory.dma_register_write THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 2 THEN
 IRTAC write_properties_lemmasTheory.WRITE_REQUESTS_IMPLIES_WRITE_REQUEST_LEMMA THEN
 ETAC listTheory.EVERY_MEM THEN
 INTRO_TAC THEN
 IRTAC lists_lemmasTheory.MEM_ADDRESS_IMPLIES_MEM_ADDRESS_BYTES_LEMMA THEN
 AXTAC THEN
 AIRTAC THEN
 AXTAC THEN
 IRTAC VALID_L1_WRITE_REQUEST_IMPLIES_W_LEMMA THEN
 STAC
 ,
 PTAC operationsTheory.function_register_write THEN EQ_PAIR_ASM_TAC THEN LRTAC THEN REWRITE_TAC [listTheory.MAP, listTheory.EVERY_DEF]
 ,
 EQ_PAIR_ASM_TAC THEN LRTAC THEN REWRITE_TAC [listTheory.MAP, listTheory.EVERY_DEF] 
 ,
 EQ_PAIR_ASM_TAC THEN LRTAC THEN REWRITE_TAC [listTheory.MAP, listTheory.EVERY_DEF] 
]
QED

Theorem DEVICE_REGISTER_READ_L1_IMPLIES_R_W_EQ_LEMMA:
!device_characteristics memory1 memory2 device1 device2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  (device2, dma_address_bytes, MAP SND cpu_address_bytes) = device_register_read_l1 device_characteristics memory1 device1 (MAP FST cpu_address_bytes) /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  R_W_EQ device_characteristics memory1 memory2
Proof
INTRO_TAC THEN
IRTAC DEVICE_REGISTER_READ_L1_WRITE_WRITABLE_MEMORY_LEMMA THEN
ITAC write_properties_lemmasTheory.WRITING_WRITABLE_MEMORY_PRESERVES_UNWRITABLE_MEMORY_LEMMA THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_READABLE_WRITABLE THEN
AIRTAC THEN
ETAC stateTheory.R_W_EQ THEN
STAC
QED

Theorem DEVICE_REGISTER_WRITE_L1_IMPLIES_R_W_EQ_LEMMA:
!device_characteristics memory1 memory2 device1 device2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  (device2, dma_address_bytes) = device_register_write_l1 device_characteristics memory1 device1 cpu_address_bytes /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  R_W_EQ device_characteristics memory1 memory2
Proof
INTRO_TAC THEN
IRTAC DEVICE_REGISTER_WRITE_L1_WRITE_WRITABLE_MEMORY_LEMMA THEN
ITAC write_properties_lemmasTheory.WRITING_WRITABLE_MEMORY_PRESERVES_UNWRITABLE_MEMORY_LEMMA THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_READABLE_WRITABLE THEN
AIRTAC THEN
ETAC stateTheory.R_W_EQ THEN
STAC
QED


Theorem SYSTEM_CPU_REGISTER_READ_PRESERVES_L1_INVARIANT_LEMMA:
!device_characteristics cpu_transition memory1 memory2 device1 device2 cpu1 cpu2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  INVARIANT_L1 device_characteristics memory1 device1 /\
  system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1,memory1,device1) (cpu_register_read_memory_write (cpu_address_bytes, dma_address_bytes)) (cpu2,memory2,device2)
  ==>
  INVARIANT_L1 device_characteristics memory2 device2
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [l1Theory.device_transitions_l1_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
INTRO_TAC THEN
AXTAC THEN
NRLTAC 8 THEN
AXTAC THEN
NRLTAC 3 THEN
WEAKEN_TAC is_disj THEN
RLTAC THEN
ITAC device_register_read_l1Theory.DEVICE_REGISTER_READ_L1_PRESERVES_INVARIANT_L1_LEMMA THEN
IRTAC DEVICE_REGISTER_READ_L1_IMPLIES_R_W_EQ_LEMMA THEN
IRTAC R_W_EQ_PRESERVES_INVARIANT_L1_LEMMA THEN
IRTAC append_external_abstract_bds_l1Theory.APPEND_EXTERNAL_ABSTRACT_BDS_L1_PRESERVS_INVARIANT_L1_LEMMA THEN
STAC
QED

Theorem SYSTEM_CPU_REGISTER_WRITE_PRESERVES_L1_INVARIANT_LEMMA:
!device_characteristics cpu_transition memory1 memory2 device1 device2 cpu1 cpu2 address_bytes.
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  INVARIANT_L1 device_characteristics memory1 device1 /\
  system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1,memory1,device1) (cpu_register_write_memory_write address_bytes) (cpu2,memory2,device2)
  ==>
  INVARIANT_L1 device_characteristics memory2 device2
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [l1Theory.device_transitions_l1_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
INTRO_TAC THEN
AXTAC THEN
PAT_X_ASSUM “x = (y, z)” (fn thm => ASSUME_TAC (GSYM thm)) THEN
NRLTAC 7 THEN
AXTAC THEN
WEAKEN_TAC is_disj THEN
NRLTAC 3 THEN
ITAC device_register_write_l1Theory.DEVICE_REGISTER_WRITE_L1_PRESERVES_INVARIANT_L1_LEMMA THEN
IRTAC DEVICE_REGISTER_WRITE_L1_IMPLIES_R_W_EQ_LEMMA THEN
IRTAC R_W_EQ_PRESERVES_INVARIANT_L1_LEMMA THEN
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
IRTAC l1_dma_lemmasTheory.PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_L1_LEMMA THEN
STAC
QED

Theorem SYSTEM_DEVICE_INTERNAL_OPERATION_PRESERVES_L1_INVARIANT_LEMMA:
!device_characteristics cpu_transition cpu1 cpu2 memory1 memory2 device1 device2.
  PROOF_OBLIGATION_SCHEDULER device_characteristics /\
  PROOF_OBLIGATION_UPDATE_WRITES_DECLARED device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_WRITES_DECLARED device_characteristics /\
  system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1,memory1,device1) device_internal_operation (cpu2,memory2,device2) /\
  INVARIANT_L1 device_characteristics memory1 device1
  ==>
  INVARIANT_L1 device_characteristics memory2 device2
Proof
REPEAT GEN_TAC THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [l1Theory.device_transitions_l1_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
ALL_RLTAC THEN
AXTAC THEN
RLTAC THEN
ETAC l1Theory.internal_device_operation_l1 THEN
PTAC internal_device_operation THENL
[
 STAC
 ,
 ITAC l1_dma_lemmasTheory.CHANNEL_OPERATION_L1_DEVICE_PRESERVES_INVARIANT_LEMMA THEN STAC
 ,
 ITAC PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_L1_LEMMA THEN STAC
 ,
 ITAC internal_function_operation_lemmasTheory.INTERNAL_FUNCTION_OPERATION_PRESERVES_INVARIANT_L1_LEMMA THEN STAC
]
QED

Theorem SYSTEM_DEVICE_MEMORY_READ_PRESERVES_L1_INVARIANT_LEMMA:
!device_characteristics cpu_transition cpu1 cpu2 memory1 memory2 device1 device2 address_bytes.
  system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1,memory1,device1) (device_memory_read address_bytes) (cpu2,memory2,device2) /\
  INVARIANT_L1 device_characteristics memory1 device1
  ==>
  INVARIANT_L1 device_characteristics memory2 device2
Proof
REPEAT GEN_TAC THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [l1Theory.device_transitions_l1_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
ETAC operationsTheory.system_transition_labels_type_11 THEN
ALL_RLTAC THEN
AXTAC THEN
ETAC l1Theory.dma_request_served_l1 THEN
ITAC l1_dma_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INVARIANT_L1_LEMMA THEN
STAC
QED

Theorem SYSTEM_DEVICE_MEMORY_WRITE_PRESERVES_L1_INVARIANT_LEMMA:
!device_characteristics cpu_transition cpu1 cpu2 memory1 memory2 device1 device2 address_bytes.
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1,memory1,device1) (device_memory_write address_bytes) (cpu2,memory2,device2) /\
  INVARIANT_L1 device_characteristics memory1 device1
  ==>
  INVARIANT_L1 device_characteristics memory2 device2
Proof
REPEAT GEN_TAC THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [l1Theory.device_transitions_l1_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
ETAC operationsTheory.system_transition_labels_type_11 THEN
ALL_RLTAC THEN
REMOVE_SINGLE_VAR_EQ_ASMS_TAC THEN
AXTAC THEN
ETAC l1Theory.dma_request_served_l1 THEN
ETAC stateTheory.device_transition_labels_type_11 THEN
REMOVE_SINGLE_VAR_EQ_ASMS_TAC THEN
RLTAC THEN
ITAC l1_dma_lemmasTheory.WRITABLE_WRITE_REQUEST_PRESERVES_INVARIANT_L1_LEMMA THEN
ITAC l1_dma_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INVARIANT_L1_LEMMA THEN
STAC
QED

(*******************************************************************************)
(* Invariant preservation. *****************************************************)
(*******************************************************************************)

Theorem SYSTEM_PRESERVES_INVARIANT_L1_LEMMA:
!cpu_transition INVARIANT_CPU device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 operation.
  PROOF_OBLIGATIONS_DMA_L1 device_characteristics /\
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_L1 device_characteristics memory1 device1 /\
  INVARIANT_CPU memory1 cpu1 /\
  system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1, memory1, device1) operation (cpu2, memory2, device2)
  ==>
  INVARIANT_L1 device_characteristics memory2 device2
Proof
REWRITE_TAC [proof_obligations_dma_l1Theory.PROOF_OBLIGATIONS_DMA_L1] THEN
INTRO_TAC THEN
EXPAND_TERM_TAC "operation" THENL
[
 ITAC SYSTEM_CPU_INTERNAL_OPERATION_PRESERVES_L1_INVARIANT_LEMMA THEN STAC
 ,
 ITAC SYSTEM_CPU_MEMORY_READ_PRESERVES_L1_INVARIANT_LEMMA THEN STAC
 ,
 ITAC (REWRITE_RULE [proof_obligations_dma_l1Theory.PROOF_OBLIGATIONS_DMA_L1] SYSTEM_CPU_MEMORY_WRITE_PRESERVES_L1_INVARIANT_LEMMA) THEN STAC
 ,
 ITAC SYSTEM_CPU_REGISTER_READ_PRESERVES_L1_INVARIANT_LEMMA THEN STAC
 ,
 ITAC SYSTEM_CPU_REGISTER_WRITE_PRESERVES_L1_INVARIANT_LEMMA THEN STAC
 ,
 ITAC SYSTEM_DEVICE_INTERNAL_OPERATION_PRESERVES_L1_INVARIANT_LEMMA THEN STAC
 ,
 ITAC SYSTEM_DEVICE_MEMORY_READ_PRESERVES_L1_INVARIANT_LEMMA THEN STAC
 ,
 ITAC SYSTEM_DEVICE_MEMORY_WRITE_PRESERVES_L1_INVARIANT_LEMMA THEN STAC
]
QED

(*******************************************************************************)
(* Reading only readable memory. ***********************************************)
(*******************************************************************************)

Theorem SYSTEM_L1_DMA_READ_LEMMA:
!cpu_transition device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 address_bytes.
  INVARIANT_L1 device_characteristics memory1 device1 /\
  system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1, memory1, device1) (device_memory_read address_bytes) (cpu2, memory2, device2)
  ==>
  EVERY (device_characteristics.dma_characteristics.R memory1) (MAP FST address_bytes)
Proof
REPEAT GEN_TAC THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [l1Theory.device_transitions_l1_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
AXTAC THEN
ETAC stateTheory.device_transition_labels_type_11 THEN
ETAC operationsTheory.system_transition_labels_type_11 THEN
ALL_RLTAC THEN
REPEAT (WEAKEN_TAC is_eq) THEN
ETAC l1Theory.dma_pending_requests_l1 THEN
ETAC INVARIANT_L1 THEN
ITAC dma_pending_requests_properties_lemmasTheory.DEVICE_REQUESTING_READ_ADDRESSES_IMPLIES_READABLE_REQUEST_LEMMA THEN
STAC
QED

(*******************************************************************************)
(* Writing only writable memory. ***********************************************)
(*******************************************************************************)

Theorem SYSTEM_L1_DMA_WRITE_LEMMA:
!cpu_transition device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 address_bytes.
  INVARIANT_L1 device_characteristics memory1 device1 /\
  system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1, memory1, device1) (device_memory_write address_bytes) (cpu2, memory2, device2)
  ==>
  EVERY (device_characteristics.dma_characteristics.W memory1) (MAP FST address_bytes)
Proof
REPEAT GEN_TAC THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [l1Theory.device_transitions_l1_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
AXTAC THEN
ETAC stateTheory.device_transition_labels_type_11 THEN
ETAC operationsTheory.system_transition_labels_type_11 THEN
ALL_RLTAC THEN
REPEAT (WEAKEN_TAC is_eq) THEN
ETAC l1Theory.dma_pending_requests_l1 THEN
ETAC INVARIANT_L1 THEN
ITAC dma_pending_requests_properties_lemmasTheory.DEVICE_REQUESTING_WRITE_ADDRESSES_IMPLIES_WRITABLE_REQUEST_LEMMA THEN
STAC
QED

Theorem SYSTEM_L1_CPU_REGISTER_READ_DMA_WRITE_LEMMA:
!cpu_transition device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_address_bytes dma_address_bytes.
  system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1, memory1, device1) (cpu_register_read_memory_write (cpu_address_bytes, dma_address_bytes)) (cpu2, memory2, device2)
  ==>
  EVERY (device_characteristics.dma_characteristics.W memory1) (MAP FST dma_address_bytes)
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [l1Theory.device_transitions_l1_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
INTRO_TAC THEN
AXTAC THEN
NRLTAC 8 THEN
AXTAC THEN
RLTAC THEN
IRTAC DEVICE_REGISTER_READ_L1_WRITE_WRITABLE_MEMORY_LEMMA THEN
STAC
QED

Theorem SYSTEM_L1_CPU_REGISTER_WRITE_DMA_WRITE_LEMMA:
!cpu_transition device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_address_bytes dma_address_bytes.
  system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1, memory1, device1) (cpu_register_write_memory_write (cpu_address_bytes, dma_address_bytes)) (cpu2, memory2, device2)
  ==>
  EVERY (device_characteristics.dma_characteristics.W memory1) (MAP FST dma_address_bytes)
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [l1Theory.device_transitions_l1_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
INTRO_TAC THEN
AXTAC THEN
NRLTAC 8 THEN
AXTAC THEN
RLTAC THEN
IRTAC DEVICE_REGISTER_WRITE_L1_WRITE_WRITABLE_MEMORY_LEMMA THEN
STAC
QED


(*******************************************************************************)
(* DMA device performs only allowed memory accesses. ***************************)
(*******************************************************************************)

Theorem SYSTEM_L1_DMA_READ_WRITE_LEMMA:
!cpu_transition device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 operation cpu_address_bytes dma_address_bytes.
  INVARIANT_L1 device_characteristics memory1 device1 /\
  system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1, memory1, device1) operation (cpu2, memory2, device2)
  ==>
  (operation = device_memory_read  dma_address_bytes ==> EVERY (device_characteristics.dma_characteristics.R memory1) (MAP FST dma_address_bytes)) /\
  (operation = device_memory_write dma_address_bytes ==> EVERY (device_characteristics.dma_characteristics.W memory1) (MAP FST dma_address_bytes)) /\
  (operation = cpu_register_read_memory_write (cpu_address_bytes, dma_address_bytes) ==> EVERY (device_characteristics.dma_characteristics.W memory1) (MAP FST dma_address_bytes)) /\
  (operation = cpu_register_write_memory_write (cpu_address_bytes, dma_address_bytes) ==> EVERY (device_characteristics.dma_characteristics.W memory1) (MAP FST dma_address_bytes))
Proof
INTRO_TAC THEN
CONJS_TAC THEN DISCH_TAC THEN LRTAC THENL
[
 IRTAC SYSTEM_L1_DMA_READ_LEMMA THEN STAC
 ,
 IRTAC SYSTEM_L1_DMA_WRITE_LEMMA THEN STAC
 ,
 IRTAC SYSTEM_L1_CPU_REGISTER_READ_DMA_WRITE_LEMMA THEN STAC
 ,
 IRTAC SYSTEM_L1_CPU_REGISTER_WRITE_DMA_WRITE_LEMMA THEN STAC
]
QED

val _ = export_theory();

