open HolKernel Parse boolLib bossLib stateTheory proof_obligationsTheory;

val _ = new_theory "proof_obligations_cpu_l1";

Definition DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ:
DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ device_characteristics memory1 memory2 device = (
  DMAC_CAN_ACCESS_MEMORY device_characteristics device
  ==>
  R_W_EQ device_characteristics memory1 memory2
)
End

Definition PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY:
PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY
INVARIANT_CPU
cpu_transition 
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type,
                           'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type) =
!cpu1 cpu2 memory1 memory2 address_bytes
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes
  ==>
  DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ device_characteristics memory1 memory2 device
End

val _ = export_theory();

