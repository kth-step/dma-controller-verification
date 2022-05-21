open HolKernel Parse boolLib bossLib stateTheory;
open proof_obligations_cpu_l1Theory;

val _ = new_theory "proof_obligations_cpu_l2";

(* Proof obligation ensuring that the CPU can modify the BD queue only by
 * appending BDs.
 *)
Definition PROOF_OBLIGATION_CPU_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W:
PROOF_OBLIGATION_CPU_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W
INVARIANT_CPU
cpu_transition
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type) =
!cpu1 cpu2 memory1 memory2 address_bytes
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  EXTERNAL_BDS device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes
  ==>
  MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W device_characteristics device1.dma_state.internal_state memory1 memory2
End

(* Proof obligation ensuring that the CPU can modify the BD queue only by
 * appending BDs.
 *
 * THIS COVERS A PART OF THE CASE OF EXTERNAL BDS WHEN FOR INSTANCE THE HEAD
 * POINTER REGISTER IS WRITTEN IN A STATE WHERE THE BDS TO FETCH IS AN EMPTY
 * QUEUE!
 *)
Definition PROOF_OBLIGATION_CPU_REGISTER_READ_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W:
PROOF_OBLIGATION_CPU_REGISTER_READ_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W
INVARIANT_CPU
cpu_transition
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type) =
!cpu1 cpu2 memory1 memory2 cpu_address_bytes dma_address_bytes internal_state1 internal_state2 write_requests new_requests.
  EXTERNAL_BDS device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_read cpu_address_bytes) cpu2 /\
  (internal_state2, MAP SND cpu_address_bytes, new_requests) = device_characteristics.dma_characteristics.register_read internal_state1 (MAP FST cpu_address_bytes) /\
  write_requests = FILTER WRITE_REQUEST new_requests /\
  dma_address_bytes = FLAT (MAP request_to_address_bytes write_requests) /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W device_characteristics internal_state2 memory1 memory2
End

Definition APPENDED_BDS_R_W:
APPENDED_BDS_R_W device_characteristics memory internal_state channel_id appended_bds =
!EXTERNAL_MEMORY_BDS R W bd_transfer_ras_was.
  EXTERNAL_MEMORY_BDS = EXTERNAL_BDS device_characteristics /\
  R = device_characteristics.dma_characteristics.R memory /\
  W = device_characteristics.dma_characteristics.W memory /\
  bd_transfer_ras_was = (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state
  ==>
  !bd bd_ras bd_was u ras_was.
    MEM ((bd, bd_ras, bd_was), u) appended_bds /\
    ras_was = bd_transfer_ras_was bd
    ==>
    BD_READ R EXTERNAL_MEMORY_BDS bd_ras /\
    BD_WRITE W EXTERNAL_MEMORY_BDS bd_was /\
    BD_DATA R W ras_was
End

Definition REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W:
REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W device_characteristics memory1 memory2 internal_state1 internal_state2 =
!channel_id bds_to_fetch1 bds_to_fetch2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory1 internal_state1 /\
  bds_to_fetch2 = (cverification device_characteristics channel_id).bds_to_fetch memory2 internal_state2
  ==>
  ?appended_bds.
    bds_to_fetch2 = bds_to_fetch1 ++ appended_bds /\
    APPENDED_BDS_R_W device_characteristics memory2 internal_state2 channel_id appended_bds
End

Definition PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W:
PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics =
!cpu1 cpu2 memory1 memory2 cpu_address_bytes dma_address_bytes internal_state1 internal_state2 write_requests new_requests.
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write cpu_address_bytes) cpu2 /\
  (internal_state2, new_requests) = device_characteristics.dma_characteristics.register_write internal_state1 cpu_address_bytes /\
  write_requests = FILTER WRITE_REQUEST new_requests /\
  dma_address_bytes = FLAT (MAP request_to_address_bytes write_requests) /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W device_characteristics memory1 memory2 internal_state1 internal_state2
End

Definition PROOF_OBLIGATION_CPU_REGISTER_WRITE_SCRATCHPAD_R_W:
PROOF_OBLIGATION_CPU_REGISTER_WRITE_SCRATCHPAD_R_W
INVARIANT_CPU
cpu_transition
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type) =
!cpu1 cpu2 memory address_bytes internal_state1 internal_state2 requests.
  INVARIANT_CPU memory cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  (internal_state2, requests) = device_characteristics.dma_characteristics.register_write internal_state1 address_bytes
  ==>
  SCRATCHPAD_R_W device_characteristics memory internal_state2
End

Definition NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W:
NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W device_characteristics device memory1 memory2 = (
  ~DMAC_CAN_ACCESS_MEMORY device_characteristics device
  ==>
  (device_characteristics.dma_characteristics.R memory2 = device_characteristics.dma_characteristics.R memory1 /\
   device_characteristics.dma_characteristics.W memory2 = device_characteristics.dma_characteristics.W memory1) \/
  (SCRATCHPAD_R device_characteristics memory2 device.dma_state.internal_state /\ SCRATCHPAD_W device_characteristics memory2 device.dma_state.internal_state)
)
End

Definition PROOF_OBLIGATION_CPU_PRESERVES_R_W_OR_SUPERSET_OF_SCRATCHPAD:
PROOF_OBLIGATION_CPU_PRESERVES_R_W_OR_SUPERSET_OF_SCRATCHPAD
INVARIANT_CPU
cpu_transition 
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type) =
!cpu1 cpu2 memory1 memory2 address_bytes
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes
  ==>
  NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W device_characteristics device memory1 memory2
End

Definition PROOF_OBLIGATIONS_CPU_L2:
PROOF_OBLIGATIONS_CPU_L2 INVARIANT_CPU cpu_transition device_characteristics = (
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_OR_SUPERSET_OF_SCRATCHPAD INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_SCRATCHPAD_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_REGISTER_READ_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics
)
End

val _ = export_theory();

