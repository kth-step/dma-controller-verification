open HolKernel Parse boolLib bossLib;
open stateTheory l3Theory proof_obligations_dma_l3Theory invariant_l3Theory;

val _ = new_theory "proof_obligations_cpu_l3";

Definition PROOF_OBLIGATION_CPU_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L3:
PROOF_OBLIGATION_CPU_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L3 INVARIANT_CPU cpu_transition
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type) =
!cpu1 cpu2 memory1 memory2 address_bytes
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  PROOF_OBLIGATIONS_DMA_L3 device_characteristics /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  (memory2 = update_memory memory1 address_bytes) /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_CONCRETE_L3 device_characteristics memory1 device
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory2 device
End

Definition PROOF_OBLIGATION_CPU_REGISTER_READ_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L3:
PROOF_OBLIGATION_CPU_REGISTER_READ_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L3 INVARIANT_CPU cpu_transition
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type) =
!cpu1 cpu2 memory1 memory2 cpu_address_bytes dma_address_bytes new_requests read_requests write_requests internal_state2
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  PROOF_OBLIGATIONS_DMA_L3 device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_read cpu_address_bytes) cpu2 /\
  (internal_state2, MAP SND cpu_address_bytes, new_requests) = device_characteristics.dma_characteristics.register_read device1.dma_state.internal_state (MAP FST cpu_address_bytes) /\
  read_requests = FILTER READ_REQUEST new_requests /\
  write_requests = FILTER WRITE_REQUEST new_requests /\
  device2 = device1 with dma_state := device1.dma_state with <|internal_state := internal_state2; pending_register_related_memory_requests := device1.dma_state.pending_register_related_memory_requests ++ read_requests|> /\
  dma_address_bytes = FLAT (MAP request_to_address_bytes write_requests) /\
  memory2 = update_memory memory1 dma_address_bytes /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_CONCRETE_L3 device_characteristics memory1 device1
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory2 device2
End

Definition PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L3:
PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L3 INVARIANT_CPU cpu_transition
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type) =
!cpu1 cpu2 memory1 memory2 cpu_address_bytes dma_address_bytes new_requests read_requests write_requests internal_state2
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  PROOF_OBLIGATIONS_DMA_L3 device_characteristics /\
  cpu_transition cpu1 (cpu_memory_write cpu_address_bytes) cpu2 /\
  (internal_state2, new_requests) = device_characteristics.dma_characteristics.register_write device1.dma_state.internal_state cpu_address_bytes /\
  read_requests = FILTER READ_REQUEST new_requests /\
  write_requests = FILTER WRITE_REQUEST new_requests /\
  device2 = device1 with dma_state := device1.dma_state with <|internal_state := internal_state2; pending_register_related_memory_requests := device1.dma_state.pending_register_related_memory_requests ++ read_requests|> /\
  dma_address_bytes = FLAT (MAP request_to_address_bytes write_requests) /\
  memory2 = update_memory memory1 dma_address_bytes /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_CONCRETE_L3 device_characteristics memory1 device1
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory2 device2
End

val _ = export_theory();

