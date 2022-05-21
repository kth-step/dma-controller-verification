open HolKernel Parse boolLib bossLib helper_tactics;
open proof_obligations_dma_l2Theory invariant_l2Theory l1Theory l2Theory;

val _ = new_theory "l1_eq_l2";

(*************************************DEVICE************************************)

Theorem DEVICE_BSIM_L1_L2_DEVICE_INTERNAL_OPERATION_LEMMA:
!device_characteristics device1 device2 memory environment.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  INVARIANT_L2 device_characteristics memory device1
  ==>
  (device_transition_l2 device_characteristics device1 (memory, device_internal_operation environment) device2
   =
   device_transition_l1 device_characteristics device1 (memory, device_internal_operation environment) device2)
Proof
INTRO_TAC THEN
REWRITE_TAC [device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [device_transitions_l1_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [internal_device_operation_l2] THEN
REWRITE_TAC [internal_device_operation_l1] THEN
EQ_TAC THEN
 DISCH_TAC THEN
 AXTAC THEN
 PAXTAC THEN
 ETAC stateTheory.device_transition_labels_type_11 THEN
 ITAC internal_operation_l1_eq_l2Theory.DEVICE_BSIM_L1_L2_INTERNAL_DEVICE_OPERATION_LEMMA THEN
 RLTAC THEN
 RLTAC THEN
 STAC
QED

Theorem DEVICE_BSIM_L1_L2_DEVICE_MEMORY_READ_LEMMA:
!device_characteristics device1 device2 address_bytes memory.
  device_transition_l2 device_characteristics device1 (memory, device_memory_read address_bytes) device2
  =
  device_transition_l1 device_characteristics device1 (memory, device_memory_read address_bytes) device2
Proof
REPEAT GEN_TAC THEN
REWRITE_TAC [device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [device_transitions_l1_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [dma_pending_requests_l2] THEN
REWRITE_TAC [dma_pending_requests_l1] THEN
REWRITE_TAC [dma_request_served_l2] THEN
REWRITE_TAC [dma_request_served_l1]
QED

Theorem DEVICE_BSIM_L1_L2_DEVICE_MEMORY_WRITE_LEMMA:
!device_characteristics device1 device2 address_bytes memory.
  device_transition_l2 device_characteristics device1 (memory, device_memory_write address_bytes) device2
  =
  device_transition_l1 device_characteristics device1 (memory, device_memory_write address_bytes) device2
Proof
REPEAT GEN_TAC THEN
REWRITE_TAC [device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [device_transitions_l1_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [dma_pending_requests_l2] THEN
REWRITE_TAC [dma_pending_requests_l1] THEN
REWRITE_TAC [dma_request_served_l2] THEN
REWRITE_TAC [dma_request_served_l1]
QED

Theorem DEVICE_BSIM_L1_L2_EXTERNAL_BDS_APPENDED_LEMMA:
!device_characteristics device1 device2 memory.
  device_transition_l2 device_characteristics device1 (memory, external_bds_appended) device2
  =
  device_transition_l1 device_characteristics device1 (memory, external_bds_appended) device2
Proof
REPEAT GEN_TAC THEN
REWRITE_TAC [device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [device_transitions_l1_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [append_external_abstract_bds_l2] THEN
REWRITE_TAC [append_external_abstract_bds_l1]
QED

Theorem DEVICE_BSIM_L1_L2_DEVICE_REGISTER_READ_LEMMA:
!device_characteristics device1 device2 address_bytes memory.
  PROOF_OBLIGATION_REGISTER_READ_MEMORY_READ_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_REGISTER_READ_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  INVARIANT_L2 device_characteristics memory device1
  ==>
  (device_transition_l2 device_characteristics device1 (memory, device_register_read address_bytes) device2 =
   device_transition_l1 device_characteristics device1 (memory, device_register_read address_bytes) device2)
Proof
INTRO_TAC THEN
REWRITE_TAC [device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [device_transitions_l1_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
EQ_TAC THEN
 INTRO_TAC THEN
 AXTAC THEN
 PAXTAC THEN
 ALL_RLTAC THEN
 ASM_REWRITE_TAC [] THEN
 PTAC INVARIANT_L2 THEN
 IRTAC invariant_l2_lemmasTheory.INVARIANT_SCRATCHPAD_R_W_L2_IMPLIES_SCRATCHPAD_R_W_LEMMA THEN
 IRTAC device_register_read_l2_lemmasTheory.DEVICE_REGISTER_READ_L1_EQ_L2_LEMMA THEN
 STAC
QED

Theorem DEVICE_BSIM_L1_L2_DEVICE_REGISTER_WRITE_LEMMA:
!device_characteristics device1 device2 address_bytes memory.
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_READ_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  INVARIANT_L2 device_characteristics memory device1
  ==>
  (device_transition_l2 device_characteristics device1 (memory, device_register_write address_bytes) device2 =
   device_transition_l1 device_characteristics device1 (memory, device_register_write address_bytes) device2)
Proof
INTRO_TAC THEN
REWRITE_TAC [device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [device_transitions_l1_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
EQ_TAC THEN
 INTRO_TAC THEN
 AXTAC THEN
 PAXTAC THEN
 ALL_RLTAC THEN
 ASM_REWRITE_TAC [] THEN
 PTAC INVARIANT_L2 THEN
 IRTAC invariant_l2_lemmasTheory.INVARIANT_SCRATCHPAD_R_W_L2_IMPLIES_SCRATCHPAD_R_W_LEMMA THEN
 IRTAC device_register_write_l2_lemmasTheory.DEVICE_REGISTER_WRITE_L1_EQ_L2_LEMMA THEN
 STAC
QED



(***********************************SYSTEM**************************************)





Theorem SYSTEM_BSIM_L1_L2_CPU_INTERNAL_OPERATION_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_transition.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  INVARIANT_L2 device_characteristics memory1 device1
  ==>
  (system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device1) cpu_internal_operation (cpu2, memory2, device2)
   =
   system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1, memory1, device1) cpu_internal_operation (cpu2, memory2, device2))
Proof
INTRO_TAC THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct]
QED

Theorem SYSTEM_BSIM_L1_L2_CPU_MEMORY_READ_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_transition address_bytes.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  INVARIANT_L2 device_characteristics memory1 device1
  ==>
  (system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device1) (cpu_memory_read address_bytes) (cpu2, memory2, device2)
   =
   system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1, memory1, device1) (cpu_memory_read address_bytes) (cpu2, memory2, device2))
Proof
INTRO_TAC THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct]
QED

Theorem SYSTEM_BSIM_L1_L2_CPU_MEMORY_WRITE_LEMMA:
!cpu_transition device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 address_bytes.
  INVARIANT_L2 device_characteristics memory1 device1
  ==>
  (system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device1) (cpu_memory_write address_bytes) (cpu2, memory2, device2)
   =
   system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1, memory1, device1) (cpu_memory_write address_bytes) (cpu2, memory2, device2))
Proof
INTRO_TAC THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
EQ_TAC THEN
 DISCH_TAC THEN
 AXTAC THEN
 EQ_PAIR_ASM_TAC THEN
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN
 EXISTS_EQ_TAC THEN
 PAXTAC THEN
 ETAC operationsTheory.system_transition_labels_type_11 THEN
 NRLTAC 7 THEN
 CONJS_TAC THEN TRY STAC THEN
 ETAC DEVICE_BSIM_L1_L2_EXTERNAL_BDS_APPENDED_LEMMA THEN
 STAC
QED

Theorem SYSTEM_BSIM_L1_L2_CPU_REGISTER_READ_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_transition cpu_dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_MEMORY_READ_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_REGISTER_READ_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  INVARIANT_L2 device_characteristics memory1 device1
  ==>
  (system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device1) (cpu_register_read_memory_write cpu_dma_address_bytes) (cpu2, memory2, device2)
   =
   system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1, memory1, device1) (cpu_register_read_memory_write cpu_dma_address_bytes) (cpu2, memory2, device2))
Proof
INTRO_TAC THEN
EXPAND_TERM_TAC "cpu_dma_address_bytes" THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
EQ_TAC THEN
 DISCH_TAC THEN
 AXTAC THEN
 ALL_RLTAC THEN
 EXISTS_EQ_TAC THEN
 ETAC DEVICE_BSIM_L1_L2_EXTERNAL_BDS_APPENDED_LEMMA THEN
 FIRTAC DEVICE_BSIM_L1_L2_DEVICE_REGISTER_READ_LEMMA THEN
 QLRTAC THEN
 PAXTAC THEN
 STAC
QED

Theorem SYSTEM_BSIM_L1_L2_CPU_REGISTER_WRITE_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_transition cpu_dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_READ_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  INVARIANT_L2 device_characteristics memory1 device1
  ==>
  (system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device1) (cpu_register_write_memory_write cpu_dma_address_bytes) (cpu2, memory2, device2)
   =
   system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1, memory1, device1) (cpu_register_write_memory_write cpu_dma_address_bytes) (cpu2, memory2, device2))
Proof
INTRO_TAC THEN
EXPAND_TERM_TAC "cpu_dma_address_bytes" THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
EQ_TAC THEN
 DISCH_TAC THEN
 AXTAC THEN
 ALL_RLTAC THEN
 EXISTS_EQ_TAC THEN
 FITAC DEVICE_BSIM_L1_L2_DEVICE_REGISTER_WRITE_LEMMA THEN
 QLRTAC THEN
 STAC
QED

Theorem SYSTEM_BSIM_L1_L2_DEVICE_INTERNAL_OPERATION_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_transition.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  INVARIANT_L2 device_characteristics memory1 device1
  ==>
  (system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device1) device_internal_operation (cpu2, memory2, device2)
   =
   system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1, memory1, device1) device_internal_operation (cpu2, memory2, device2))
Proof
INTRO_TAC THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
EQ_TAC THEN
 DISCH_TAC THEN
 AXTAC THEN
 EQ_PAIR_ASM_TAC THEN
 ALL_RLTAC THEN
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN
 EXISTS_EQ_TAC THEN
 IRTAC DEVICE_BSIM_L1_L2_DEVICE_INTERNAL_OPERATION_LEMMA THEN
 QLRTAC THEN
 PAXTAC THEN
 STAC
QED

Theorem SYSTEM_BSIM_L1_L2_DEVICE_MEMORY_READ_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_transition address_bytes.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  INVARIANT_L2 device_characteristics memory1 device1
  ==>
  (system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device1) (device_memory_read address_bytes) (cpu2, memory2, device2)
   =
   system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1, memory1, device1) (device_memory_read address_bytes) (cpu2, memory2, device2))
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
 ALL_RLTAC THEN
 REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN
 EXISTS_EQ_TAC THEN
 PTAC PROOF_OBLIGATIONS_DMA_L2 THEN
 ETAC DEVICE_BSIM_L1_L2_DEVICE_MEMORY_READ_LEMMA THEN
 STAC
QED

Theorem SYSTEM_BSIM_L1_L2_DEVICE_MEMORY_WRITE_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_transition address_bytes.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  INVARIANT_L2 device_characteristics memory1 device1
  ==>
  (system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device1) (device_memory_write address_bytes) (cpu2, memory2, device2)
   =
   system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1, memory1, device1) (device_memory_write address_bytes) (cpu2, memory2, device2))
Proof
INTRO_TAC THEN
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
EQ_TAC THEN
 DISCH_TAC THEN
 AXTAC THEN
 EQ_PAIR_ASM_TAC THEN
 ETAC operationsTheory.system_transition_labels_type_11 THEN
 ALL_RLTAC THEN
 REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN
 EXISTS_EQ_TAC THEN
 ETAC DEVICE_BSIM_L1_L2_DEVICE_MEMORY_WRITE_LEMMA THEN
 STAC
QED

Theorem SYSTEM_BSIM_L1_L2_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (memory1 : 'interconnect_address_width memory_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  PROOF_OBLIGATION_REGISTER_READ_MEMORY_READ_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_REGISTER_READ_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_READ_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  INVARIANT_L2 device_characteristics memory1 device1
  ==>
  !cpu_transition cpu1 cpu2 operation memory2 device2.
    (system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device1) operation (cpu2, memory2, device2)
     =
     system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1, memory1, device1) operation (cpu2, memory2, device2))
Proof
INTRO_TAC THEN
REPEAT GEN_TAC THEN
EXPAND_TERM_TAC "operation" THENL
[
 ITAC SYSTEM_BSIM_L1_L2_CPU_INTERNAL_OPERATION_LEMMA THEN STAC
 ,
 ITAC SYSTEM_BSIM_L1_L2_CPU_MEMORY_READ_LEMMA THEN STAC
 ,
 PTAC PROOF_OBLIGATIONS_DMA_L2 THEN ITAC SYSTEM_BSIM_L1_L2_CPU_MEMORY_WRITE_LEMMA THEN STAC
 ,
 MATCH_MP_TAC SYSTEM_BSIM_L1_L2_CPU_REGISTER_READ_LEMMA THEN STAC
 ,
 ITAC SYSTEM_BSIM_L1_L2_CPU_REGISTER_WRITE_LEMMA THEN STAC
 ,
 ITAC SYSTEM_BSIM_L1_L2_DEVICE_INTERNAL_OPERATION_LEMMA THEN STAC
 ,
 ITAC SYSTEM_BSIM_L1_L2_DEVICE_MEMORY_READ_LEMMA THEN STAC
 ,
 ITAC SYSTEM_BSIM_L1_L2_DEVICE_MEMORY_WRITE_LEMMA THEN STAC
]
QED

val _ = export_theory();

