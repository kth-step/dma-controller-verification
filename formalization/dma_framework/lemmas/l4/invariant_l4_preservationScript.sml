open HolKernel Parse boolLib bossLib helper_tactics;
open l4Theory invariant_l1Theory invariant_l2Theory invariant_l3Theory invariant_l4Theory;
open invariant_l3_preservationTheory;
open proof_obligations_cpu_l1Theory proof_obligations_cpu_l2Theory;
open proof_obligations_cpu_l3Theory proof_obligations_cpu_l4Theory;

val _ = new_theory "invariant_l4_preservation";

(*************************************DEVICE************************************)

Theorem DEVICE_INTERNAL_OPERATION_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!device_characteristics device1 device2 memory environment.
  PROOF_OBLIGATION_SCHEDULER device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLY_PRESERVES_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_BD_PRESERVES_BD_INTERPRETATION device_characteristics  /\
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  PROOF_OBLIGATION_DECLARED_UPDATE_WRITES_BD_WAS device_characteristics /\
  PROOF_OBLIGATION_UPDATING_BD_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  PROOF_OBLIGATION_DECLARED_WRITE_BACK_WRITES_BD_WAS device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_PRESERVES_BD_INTERPRETATION device_characteristics /\
  device_transition_l4 device_characteristics device1 (memory, device_internal_operation environment) device2 /\
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device1 /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device1 /\
  INVARIANT_CONCRETE_L4 device_characteristics memory device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory device2
Proof
REWRITE_TAC [device_transitions_l4_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
INTRO_TAC THEN
AXTAC THEN
NRLTAC 2 THEN
IRTAC device_internal_operation_invariant_concrete_l4_lemmasTheory.INTERNAL_DEVICE_OPERATION_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN
STAC
QED

Theorem DEVICE_MEMORY_READ_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!device_characteristics device1 device2 address_bytes memory.
  MAP memory (MAP FST address_bytes) = MAP SND address_bytes /\
  device_transition_l4 device_characteristics device1 (memory, device_memory_read address_bytes) device2 /\
  INVARIANT_CONCRETE_L4 device_characteristics memory device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory device2
Proof
REWRITE_TAC [device_transitions_l4_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
INTRO_TAC THEN
AXTAC THEN
NRLTAC 2 THEN
IRTAC dma_request_served_invariant_concrete_l4_preservation_lemmasTheory.DMA_REQUEST_SERVED_L4_READ_REQUEST_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN
STAC
QED

Theorem DEVICE_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!device_characteristics device1 device2 address_bytes memory1 memory2.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device1 /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device1 /\
  device_transition_l4 device_characteristics device1 (memory1, device_memory_write address_bytes) device2 /\
  memory2 = update_memory memory1 address_bytes /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory2 device2
Proof
REWRITE_TAC [device_transitions_l4_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
INTRO_TAC THEN
AXTAC THEN
NRLTAC 2 THEN
IRTAC dma_request_served_invariant_concrete_l4_preservation_lemmasTheory.DMA_REQUEST_SERVED_L4_WRITE_REQUEST_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN
STAC
QED

Theorem DEVICE_EXTERNAL_BDS_APPENDED_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!device_characteristics device1 device2 memory2.
  device_transition_l4 device_characteristics device1 (memory2, external_bds_appended) device2 /\
  INVARIANT_CONCRETE_L4 device_characteristics memory2 device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory2 device2
Proof
REWRITE_TAC [device_transitions_l4_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
RLTAC THEN
STAC
QED






(***********************************SYSTEM**************************************)





Theorem SYSTEM_CPU_INTERNAL_OPERATION_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_transition.
  system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) cpu_internal_operation (cpu2, memory2, device2) /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory2 device2
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
EQ_PAIR_ASM_TAC THEN
ALL_RLTAC THEN
STAC
QED

Theorem SYSTEM_CPU_MEMORY_READ_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_transition address_bytes.
  system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) (cpu_memory_read address_bytes) (cpu2, memory2, device2) /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory2 device2
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
EQ_PAIR_ASM_TAC THEN
ETAC operationsTheory.system_transition_labels_type_11 THEN
ALL_RLTAC THEN
STAC
QED

Theorem SYSTEM_CPU_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!cpu_transition INVARIANT_CPU device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 address_bytes.
  PROOF_OBLIGATION_CPU_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) (cpu_memory_write address_bytes) (cpu2, memory2, device2) /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory2 device2
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [device_transitions_l4_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
INTRO_TAC THEN
AXTAC THEN
AXTAC THEN
ALL_RLTAC THEN
LRTAC THEN
PTAC proof_obligations_cpu_l4Theory.PROOF_OBLIGATION_CPU_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4 THEN
AIRTAC THEN
STAC
QED

Theorem SYSTEM_CPU_REGISTER_READ_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!INVARIANT_CPU device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_transition cpu_dma_address_bytes.
  PROOF_OBLIGATION_CPU_REGISTER_READ_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) (cpu_register_read_memory_write cpu_dma_address_bytes) (cpu2, memory2, device2) /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory2 device2
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [l4Theory.device_transitions_l4_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
INTRO_TAC THEN
AXTAC THEN
PAT_X_ASSUM “x = (y, z)” (fn thm => ASSUME_TAC (GSYM thm)) THEN
NRLTAC 7 THEN
AXTAC THEN
NRLTAC 3 THEN
WEAKEN_TAC is_disj THEN
RLTAC THEN
LRTAC THEN
IRTAC device_register_read_invariant_concrete_l4_preservation_lemmasTheory.DEVICE_REGISTER_READ_L4_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN
STAC
QED

Theorem SYSTEM_CPU_REGISTER_WRITE_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!cpu_transition INVARIANT_CPU device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_dma_address_bytes.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) (cpu_register_write_memory_write cpu_dma_address_bytes) (cpu2, memory2, device2) /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory2 device2
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [l4Theory.device_transitions_l4_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
INTRO_TAC THEN
AXTAC THEN
PAT_X_ASSUM “x = (y, z)” (fn thm => ASSUME_TAC (GSYM thm)) THEN
NRLTAC 7 THEN
AXTAC THEN
NRLTAC 3 THEN
WEAKEN_TAC is_disj THEN
IRTAC device_register_write_invariant_concrete_l4_preservation_lemmasTheory.DEVICE_REGISTER_WRITE_L4_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN
STAC
QED

Theorem SYSTEM_DEVICE_INTERNAL_OPERATION_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_transition.
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) device_internal_operation (cpu2, memory2, device2) /\
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory1 device1 /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory1 device1 /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory2 device2
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [proof_obligations_dma_l4Theory.PROOF_OBLIGATIONS_DMA_L4] THEN
INTRO_TAC THEN
AXTAC THEN
EQ_PAIR_ASM_TAC THEN
ALL_RLTAC THEN
IRTAC DEVICE_INTERNAL_OPERATION_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN
STAC
QED

Theorem SYSTEM_DEVICE_MEMORY_READ_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_transition address_bytes.
  system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) (device_memory_read address_bytes) (cpu2, memory2, device2) /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory2 device2
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
EQ_PAIR_ASM_TAC THEN
ETAC operationsTheory.system_transition_labels_type_11 THEN
ALL_RLTAC THEN
IRTAC DEVICE_MEMORY_READ_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN
STAC
QED

Theorem SYSTEM_DEVICE_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_transition address_bytes.
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device1 /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device1 /\
  system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) (device_memory_write address_bytes) (cpu2, memory2, device2) /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory2 device2
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [proof_obligations_dma_l4Theory.PROOF_OBLIGATIONS_DMA_L4] THEN
INTRO_TAC THEN
AXTAC THEN
EQ_PAIR_ASM_TAC THEN
ALL_RLTAC THEN
IRTAC DEVICE_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN
STAC
QED

Theorem SYSTEM_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!cpu_transition INVARIANT_CPU 
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 cpu1 cpu2 memory1 memory2 device1 device2 operation.
  PROOF_OBLIGATION_CPU_REGISTER_READ_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) operation (cpu2, memory2, device2) /\
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory1 device1 /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory1 device1 /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device1 /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device1 /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
Cases_on ‘operation’ THENL
[
 IRTAC SYSTEM_CPU_INTERNAL_OPERATION_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN STAC
 ,
 IRTAC SYSTEM_CPU_MEMORY_READ_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN STAC
 ,
 IRTAC SYSTEM_CPU_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN STAC
 ,
 IRTAC SYSTEM_CPU_REGISTER_READ_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN STAC
 ,
 ITAC SYSTEM_CPU_REGISTER_WRITE_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN STAC
 ,
 IRTAC SYSTEM_DEVICE_INTERNAL_OPERATION_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN STAC
 ,
 ITAC SYSTEM_DEVICE_MEMORY_READ_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN STAC
 ,
 ITAC SYSTEM_DEVICE_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN STAC
]
QED

Theorem PROOF_OBLIGATIONS_CPU_DMA_L4_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics.
  PROOF_OBLIGATIONS_CPU_L4 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics
  ==>
  PROOF_OBLIGATIONS_L3 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_REGISTER_READ_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4 INVARIANT_CPU cpu_transition device_characteristics
Proof
INTRO_TAC THEN
ETAC proof_obligations_cpu_l4Theory.PROOF_OBLIGATIONS_CPU_L4 THEN
ETAC proof_obligations_dma_l4Theory.PROOF_OBLIGATIONS_DMA_L4 THEN
ETAC PROOF_OBLIGATIONS_L3 THEN
STAC
QED

Theorem SYSTEM_PRESERVES_INVARIANT_L4_LEMMA:
!cpu_transition INVARIANT_CPU
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 cpu1 cpu2 memory1 memory2 device1 device2 operation.
  PROOF_OBLIGATIONS_CPU_L4 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) operation (cpu2, memory2, device2) /\
  INVARIANT_L4 device_characteristics memory1 device1
  ==>
  INVARIANT_L4 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
ITAC PROOF_OBLIGATIONS_CPU_DMA_L4_LEMMA THEN
ITAC invariant_l4_lemmasTheory.INVARIANT_L4_IMPLIES_INVARIANT_CONCRETE_L4_BDS_TO_FETCH_DISJOINT_EXTERNAL_FETCH_BD_REPLY_NO_MEMORY_WRITES_TO_BDS_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA THEN
FITAC SYSTEM_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN
ITAC l3_eq_l4Theory.SYSTEM_BSIM_L3_L4_LEMMA THEN
QLRTAC THEN
IRTAC invariant_l4_lemmasTheory.INVARIANT_L4_IMPLIES_INVARIANT_L3_LEMMA THEN
IRTAC invariant_l3_preservationTheory.SYSTEM_PRESERVES_INVARIANT_L1_L2_L3_LEMMA THEN
IRTAC invariant_l4_lemmasTheory.INVARIANT_L3_INVARIANT_CONCRETE_L4_IMPLIES_INVARIANT_L4_LEMMA THEN
STAC
QED

val _ = export_theory();

