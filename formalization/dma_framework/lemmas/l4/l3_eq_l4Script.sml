open HolKernel Parse boolLib bossLib helper_tactics;
open l3Theory l4Theory proof_obligations_dma_l4Theory proof_obligations_cpu_l4Theory invariant_l4Theory;

val _ = new_theory "l3_eq_l4";

(*************************************DEVICE************************************)

Theorem DEVICE_BSIM_L3_L4_DEVICE_INTERNAL_OPERATION_LEMMA:
!device_characteristics device1 device2 memory environment.
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INVARIANT_UPDATE_BD_BD_WRITE_L4 device_characteristics memory device1 /\
  INVARIANT_PROCESS_BD_DMA_WRITE_L4 device_characteristics memory device1 /\
  INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 device_characteristics memory device1
  ==>
  (device_transition_l4 device_characteristics device1 (memory, device_internal_operation environment) device2
   =
   device_transition_l3 device_characteristics device1 (memory, device_internal_operation environment) device2)
Proof
INTRO_TAC THEN
REWRITE_TAC [device_transitions_l4_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [device_transitions_l3_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [internal_device_operation_l4] THEN
REWRITE_TAC [internal_device_operation_l3] THEN
EQ_TAC THEN
 DISCH_TAC THEN
 AXTAC THEN
 PAXTAC THEN
 ETAC stateTheory.device_transition_labels_type_11 THEN
 ALL_RLTAC THEN
 REWRITE_TAC [] THEN
 ITAC internal_device_operation_l3_l4Theory.DEVICE_BSIM_L3_L4_INTERNAL_DEVICE_OPERATION_LEMMA THEN
 STAC
QED

Theorem DEVICE_BSIM_L3_L4_DEVICE_MEMORY_READ_LEMMA:
!device_characteristics device1 device2 address_bytes memory.
  device_transition_l4 device_characteristics device1 (memory, device_memory_read address_bytes) device2
  =
  device_transition_l3 device_characteristics device1 (memory, device_memory_read address_bytes) device2
Proof
REPEAT GEN_TAC THEN
REWRITE_TAC [device_transitions_l4_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [device_transitions_l3_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [dma_pending_requests_l4] THEN
REWRITE_TAC [dma_pending_requests_l3] THEN
REWRITE_TAC [dma_request_served_l4] THEN
REWRITE_TAC [dma_request_served_l3]
QED

Theorem DEVICE_BSIM_L3_L4_DEVICE_MEMORY_WRITE_LEMMA:
!device_characteristics device1 device2 address_bytes memory.
  device_transition_l4 device_characteristics device1 (memory, device_memory_write address_bytes) device2
  =
  device_transition_l3 device_characteristics device1 (memory, device_memory_write address_bytes) device2
Proof
REPEAT GEN_TAC THEN
REWRITE_TAC [device_transitions_l4_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [device_transitions_l3_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [dma_pending_requests_l4] THEN
REWRITE_TAC [dma_pending_requests_l3] THEN
REWRITE_TAC [dma_request_served_l4] THEN
REWRITE_TAC [dma_request_served_l3]
QED

Theorem DEVICE_BSIM_L3_L4_EXTERNAL_BDS_APPENDED_LEMMA:
!device_characteristics device1 device2 memory.
  device_transition_l4 device_characteristics device1 (memory, external_bds_appended) device2
  =
  device_transition_l3 device_characteristics device1 (memory, external_bds_appended) device2
Proof
REPEAT GEN_TAC THEN
REWRITE_TAC [device_transitions_l4_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [device_transitions_l3_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct]
QED

Theorem DEVICE_BSIM_L3_L4_DEVICE_REGISTER_READ_LEMMA:
!device_characteristics device1 device2 address_bytes memory.
  device_transition_l4 device_characteristics device1 (memory, device_register_read address_bytes) device2
  =
  device_transition_l3 device_characteristics device1 (memory, device_register_read address_bytes) device2
Proof
REPEAT GEN_TAC THEN
REWRITE_TAC [device_transitions_l4_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [device_transitions_l3_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
EQ_TAC THEN
 INTRO_TAC THEN
 AXTAC THEN
 PAXTAC THEN
 ETAC stateTheory.device_transition_labels_type_11 THEN
 ALL_RLTAC THEN
 ASM_REWRITE_TAC [] THEN
 WEAKEN_TAC is_disj THEN
 REWRITE_TAC [register_read_l3_l4Theory.DEVICE_REGISTER_READ_L3_EQ_L4_LEMMA]
QED

Theorem DEVICE_BSIM_L3_L4_DEVICE_REGISTER_WRITE_LEMMA:
!device_characteristics device1 device2 address_bytes memory.
  device_transition_l4 device_characteristics device1 (memory, device_register_write address_bytes) device2
  =
  device_transition_l3 device_characteristics device1 (memory, device_register_write address_bytes) device2
Proof
REPEAT GEN_TAC THEN
REWRITE_TAC [device_transitions_l4_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [device_transitions_l3_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
EQ_TAC THEN
 INTRO_TAC THEN
 AXTAC THEN
 PAXTAC THEN
 ETAC stateTheory.device_transition_labels_type_11 THEN
 ALL_RLTAC THEN
 ASM_REWRITE_TAC [] THEN
 WEAKEN_TAC is_disj THEN
 REWRITE_TAC [register_write_l3_l4Theory.DEVICE_REGISTER_WRITE_L3_EQ_L4_LEMMA]
QED

Theorem DEVICE_BISIM_L3_L4_LEMMA:
!device_characteristics memory operation device1 device2.
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INVARIANT_UPDATE_BD_BD_WRITE_L4 device_characteristics memory device1 /\
  INVARIANT_PROCESS_BD_DMA_WRITE_L4 device_characteristics memory device1 /\
  INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 device_characteristics memory device1
  ==>
  (device_transition_l4 device_characteristics device1 (memory, operation) device2
   =
   device_transition_l3 device_characteristics device1 (memory, operation) device2)
Proof
INTRO_TAC THEN
EXPAND_TERM_TAC "operation" THENL
[
 ITAC DEVICE_BSIM_L3_L4_DEVICE_INTERNAL_OPERATION_LEMMA THEN STAC
 ,
 REWRITE_TAC [DEVICE_BSIM_L3_L4_DEVICE_MEMORY_READ_LEMMA]
 ,
 REWRITE_TAC [DEVICE_BSIM_L3_L4_DEVICE_MEMORY_WRITE_LEMMA]
 ,
 REWRITE_TAC [DEVICE_BSIM_L3_L4_EXTERNAL_BDS_APPENDED_LEMMA]
 ,
 REWRITE_TAC [DEVICE_BSIM_L3_L4_DEVICE_REGISTER_READ_LEMMA] THEN STAC
 ,
 REWRITE_TAC [DEVICE_BSIM_L3_L4_DEVICE_REGISTER_WRITE_LEMMA] THEN STAC
]
QED






(***********************************SYSTEM**************************************)





Theorem SYSTEM_BSIM_L3_L4_CPU_INTERNAL_OPERATION_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_transition.
  (system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) cpu_internal_operation (cpu2, memory2, device2)
   =
   system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device1) cpu_internal_operation (cpu2, memory2, device2))
Proof
REPEAT GEN_TAC THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct]
QED

Theorem SYSTEM_BSIM_L3_L4_CPU_MEMORY_READ_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_transition address_bytes.
  (system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) (cpu_memory_read address_bytes) (cpu2, memory2, device2)
   =
   system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device1) (cpu_memory_read address_bytes) (cpu2, memory2, device2))
Proof
REPEAT GEN_TAC THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct]
QED

Theorem SYSTEM_BSIM_L3_L4_CPU_MEMORY_WRITE_LEMMA:
!cpu_transition INVARIANT_CPU device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 address_bytes.
  PROOF_OBLIGATION_CPU_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device1
  ==>
  (system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) (cpu_memory_write address_bytes) (cpu2, memory2, device2)
   =
   system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device1) (cpu_memory_write address_bytes) (cpu2, memory2, device2))
Proof
INTRO_TAC THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
EQ_TAC THEN
 DISCH_TAC THEN
 AXTAC THEN
 EQ_PAIR_ASM_TAC THEN
 ETAC operationsTheory.system_transition_labels_type_11 THEN
 NRLTAC 7 THEN
 REWRITE_TAC [pairTheory.PAIR_EQ, operationsTheory.system_transition_labels_type_11] THEN
 EXISTS_EQ_TAC THEN
 PAXTAC THEN
 CONJS_TAC THEN TRY STAC THEN
 PTAC PROOF_OBLIGATION_CPU_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4 THEN
 AITAC THEN
 ETAC INVARIANT_CONCRETE_L4 THEN
 ITAC DEVICE_BISIM_L3_L4_LEMMA THEN
 QLRTAC THEN
 STAC
QED

Theorem SYSTEM_BSIM_L3_L4_CPU_REGISTER_READ_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_transition cpu_dma_address_bytes.
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device1
  ==>
  (system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) (cpu_register_read_memory_write cpu_dma_address_bytes) (cpu2, memory2, device2)
   =
   system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device1) (cpu_register_read_memory_write cpu_dma_address_bytes) (cpu2, memory2, device2))
Proof
INTRO_TAC THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
ETAC INVARIANT_CONCRETE_L4 THEN
EQ_TAC THEN
 DISCH_TAC THEN
 AXTAC THEN
 PAT_X_ASSUM “x = (y, z)” (fn thm => ASSUME_TAC (GSYM thm)) THEN
 NRLTAC 7 THEN
 EXISTS_EQ_TAC THEN
 IRTAC DEVICE_BISIM_L3_L4_LEMMA THEN
 QLRTAC THEN
 PAXTAC THEN
 ETAC DEVICE_BSIM_L3_L4_EXTERNAL_BDS_APPENDED_LEMMA THEN
 STAC
QED

Theorem SYSTEM_BSIM_L3_L4_CPU_REGISTER_WRITE_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_transition cpu_dma_address_bytes.
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device1
  ==>
  (system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) (cpu_register_write_memory_write cpu_dma_address_bytes) (cpu2, memory2, device2)
   =
   system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device1) (cpu_register_write_memory_write cpu_dma_address_bytes) (cpu2, memory2, device2))
Proof
INTRO_TAC THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
ETAC INVARIANT_CONCRETE_L4 THEN
EQ_TAC THEN
 DISCH_TAC THEN
 AXTAC THEN
 PAT_X_ASSUM “x = (y, z)” (fn thm => ASSUME_TAC (GSYM thm)) THEN
 NRLTAC 7 THEN
 EXISTS_EQ_TAC THEN
 IRTAC DEVICE_BISIM_L3_L4_LEMMA THEN
 QLRTAC THEN
 STAC
QED

Theorem SYSTEM_BSIM_L3_L4_DEVICE_INTERNAL_OPERATION_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_transition.
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device1
  ==>
  (system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) device_internal_operation (cpu2, memory2, device2)
   =
   system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device1) device_internal_operation (cpu2, memory2, device2))
Proof
INTRO_TAC THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
ETAC INVARIANT_CONCRETE_L4 THEN
EQ_TAC THEN
 DISCH_TAC THEN
 AXTAC THEN
 ALL_RLTAC THEN
 EXISTS_EQ_TAC THEN
 PAXTAC THEN
 IRTAC DEVICE_BISIM_L3_L4_LEMMA THEN
 QLRTAC THEN
 STAC
QED

Theorem SYSTEM_BSIM_L3_L4_DEVICE_MEMORY_READ_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_transition address_bytes.
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device1
  ==>
  (system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) (device_memory_read address_bytes) (cpu2, memory2, device2)
   =
   system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device1) (device_memory_read address_bytes) (cpu2, memory2, device2))
Proof
INTRO_TAC THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
ETAC INVARIANT_CONCRETE_L4 THEN
EQ_TAC THEN
 DISCH_TAC THEN
 AXTAC THEN
 ETAC operationsTheory.system_transition_labels_type_11 THEN
 ALL_RLTAC THEN
 REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
 EXISTS_EQ_TAC THEN
 IRTAC DEVICE_BISIM_L3_L4_LEMMA THEN
 QLRTAC THEN
 STAC
QED

Theorem SYSTEM_BSIM_L3_L4_DEVICE_MEMORY_WRITE_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_transition address_bytes.
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device1
  ==>
  (system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) (device_memory_write address_bytes) (cpu2, memory2, device2)
   =
   system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device1) (device_memory_write address_bytes) (cpu2, memory2, device2))
Proof
INTRO_TAC THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
ETAC INVARIANT_CONCRETE_L4 THEN
EQ_TAC THEN
 DISCH_TAC THEN
 AXTAC THEN
 ETAC operationsTheory.system_transition_labels_type_11 THEN
 ALL_RLTAC THEN
 REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
 EXISTS_EQ_TAC THEN
 IRTAC DEVICE_BISIM_L3_L4_LEMMA THEN
 QLRTAC THEN
 STAC
QED

Theorem SYSTEM_BSIM_L3_L4_LEMMA:
!cpu_transition INVARIANT_CPU device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 operation.
  PROOF_OBLIGATION_CPU_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device1
  ==>
  (system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) operation (cpu2, memory2, device2)
   =
   system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device1) operation (cpu2, memory2, device2))
Proof
INTRO_TAC THEN
EXPAND_TERM_TAC "operation" THENL
[
 REWRITE_TAC [SYSTEM_BSIM_L3_L4_CPU_INTERNAL_OPERATION_LEMMA]
 ,
 REWRITE_TAC [SYSTEM_BSIM_L3_L4_CPU_MEMORY_READ_LEMMA]
 ,
 IRTAC SYSTEM_BSIM_L3_L4_CPU_MEMORY_WRITE_LEMMA THEN STAC
 ,
 IRTAC SYSTEM_BSIM_L3_L4_CPU_REGISTER_READ_LEMMA THEN STAC
 ,
 IRTAC SYSTEM_BSIM_L3_L4_CPU_REGISTER_WRITE_LEMMA THEN STAC
 ,
 IRTAC SYSTEM_BSIM_L3_L4_DEVICE_INTERNAL_OPERATION_LEMMA THEN STAC
 ,
 IRTAC SYSTEM_BSIM_L3_L4_DEVICE_MEMORY_READ_LEMMA THEN STAC
 ,
 IRTAC SYSTEM_BSIM_L3_L4_DEVICE_MEMORY_WRITE_LEMMA THEN STAC
]
QED

val _ = export_theory();

