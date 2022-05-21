open HolKernel Parse boolLib bossLib helper_tactics;
open proof_obligationsTheory l2Theory l3Theory L23EQTheory;

val _ = new_theory "l2_eq_l3";

Theorem SYSTEM_SIM_L2_L3_CPU_INTERNAL_OPERATION_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device31 device21 device22 cpu_transition.
  L23EQ device_characteristics memory1 device21 device31 /\
  system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device21) cpu_internal_operation (cpu2, memory2, device22)
  ==>
  ?device32.
    system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device31) cpu_internal_operation (cpu2, memory2, device32) /\
    L23EQ device_characteristics memory2 device22 device32
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
EQ_PAIR_ASM_TAC THEN
ALL_RLTAC THEN
PAXTAC THEN
ASM_REWRITE_TAC [] THEN
EXISTS_EQ_TAC THEN
STAC
QED

Theorem SYSTEM_SIM_L3_L2_CPU_INTERNAL_OPERATION_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device21 device31 device32 cpu_transition.
  L23EQ device_characteristics memory1 device21 device31 /\
  system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device31) cpu_internal_operation (cpu2, memory2, device32)
  ==>
  ?device22.
    system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device21) cpu_internal_operation (cpu2, memory2, device22) /\
    L23EQ device_characteristics memory2 device22 device32
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
EQ_PAIR_ASM_TAC THEN
ALL_RLTAC THEN
PAXTAC THEN
ASM_REWRITE_TAC [] THEN
EXISTS_EQ_TAC THEN
STAC
QED



Theorem SYSTEM_SIM_L2_L3_CPU_MEMORY_READ_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device31 device21 device22 cpu_transition l.
  L23EQ device_characteristics memory1 device21 device31 /\
  system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device21) (cpu_memory_read l) (cpu2, memory2, device22)
  ==>
  ?device32.
    system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device31) (cpu_memory_read l) (cpu2, memory2, device32) /\
    L23EQ device_characteristics memory2 device22 device32
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
EQ_PAIR_ASM_TAC THEN
ETAC operationsTheory.system_transition_labels_type_11 THEN
ALL_RLTAC THEN
PAXTAC THEN
ASM_REWRITE_TAC [] THEN
EXISTS_EQ_TAC THEN
PAXTAC THEN
STAC
QED

Theorem SYSTEM_SIM_L3_L2_CPU_MEMORY_READ_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device21 device31 device32 cpu_transition l.
  L23EQ device_characteristics memory1 device21 device31 /\
  system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device31) (cpu_memory_read l) (cpu2, memory2, device32)
  ==>
  ?device22.
    system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device21) (cpu_memory_read l) (cpu2, memory2, device22) /\
    L23EQ device_characteristics memory2 device22 device32
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
EQ_PAIR_ASM_TAC THEN
ETAC operationsTheory.system_transition_labels_type_11 THEN
ALL_RLTAC THEN
PAXTAC THEN
ASM_REWRITE_TAC [] THEN
EXISTS_EQ_TAC THEN
PAXTAC THEN
STAC
QED

Theorem SYSTEM_SIM_L2_L3_CPU_MEMORY_WRITE_LEMMA:
!device_characteristics INVARIANT_CPU cpu1 cpu2 memory1 memory2 device31 device21 device22 cpu_transition l.
  PROOF_OBLIGATION_CPU_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_L2 device_characteristics memory1 device21 /\
  INVARIANT_L3 device_characteristics memory1 device31 /\
  L23EQ device_characteristics memory1 device21 device31 /\
  system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device21) (cpu_memory_write l) (cpu2, memory2, device22)
  ==>
  ?device32.
    system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device31) (cpu_memory_write l) (cpu2, memory2, device32) /\
    L23EQ device_characteristics memory2 device22 device32
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [l3Theory.device_transitions_l3_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
AXTAC THEN
ETAC operationsTheory.system_transition_labels_type_11 THEN
ALL_RLTAC THEN
ITAC append_external_abstract_bds_l2_l3Theory.DEVICE_SIM_L2_L3_EXTERNAL_BDS_APPENDED_LEMMA THEN
INST_EXISTS_NAMES_TAC ["device31"] THEN
ASM_REWRITE_TAC [] THEN
EXISTS_EQ_TAC THEN
PAXTAC THEN
ASM_REWRITE_TAC [] THEN
ALL_RLTAC THEN
EXISTS_EQ_TAC
QED

Theorem SYSTEM_SIM_L3_L2_CPU_MEMORY_WRITE_LEMMA:
!device_characteristics INVARIANT_CPU cpu1 cpu2 memory1 memory2 device21 device31 device32 cpu_transition l.
  PROOF_OBLIGATION_CPU_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_L2 device_characteristics memory1 device21 /\
  INVARIANT_L3 device_characteristics memory1 device31 /\
  L23EQ device_characteristics memory1 device21 device31 /\
  system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device31) (cpu_memory_write l) (cpu2, memory2, device32)
  ==>
  ?device22.
    system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device21) (cpu_memory_write l) (cpu2, memory2, device22) /\
    L23EQ device_characteristics memory2 device22 device32
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [l3Theory.device_transitions_l3_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
AXTAC THEN
ETAC operationsTheory.system_transition_labels_type_11 THEN
ALL_RLTAC THEN
LRTAC THEN
ITAC append_external_abstract_bds_l2_l3Theory.DEVICE_SIM_L3_L2_EXTERNAL_BDS_APPENDED_LEMMA THEN
AXTAC THEN
PAXTAC THEN
ASM_REWRITE_TAC [] THEN
EXISTS_EQ_TAC THEN
PAXTAC THEN
ASM_REWRITE_TAC [] THEN
EXISTS_EQ_TAC
QED




Theorem DEVICE_REGISTER_L2_L3_APPEND_EXTERNAL_ABSTRACT_BDS_L2_DMA_MEMORY_WRITE_PRESERVES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics memory1 memory2 device21 device device22 device31 device32 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  INTERNAL_STATES_EQ device device32 /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory1 device device32 /\
  (device, dma_address_bytes, MAP SND cpu_address_bytes) = device_register_read_l2 device_characteristics memory1 device21 (MAP FST cpu_address_bytes) /\
  (device32, dma_address_bytes, MAP SND cpu_address_bytes) = device_register_read_l3 device_characteristics device31 (MAP FST cpu_address_bytes) /\
  device22 = append_external_abstract_bds_l2 device_characteristics memory2 device /\
  memory2 = update_memory memory1 dma_address_bytes /\
  MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W device_characteristics device.dma_state.internal_state memory1 memory2
  ==>
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory2 device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
PTAC l2Theory.append_external_abstract_bds_l2 THENL
[
 AITAC THEN
 ETAC proof_obligationsTheory.MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W THEN
 ITAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
 ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH THEN
  ETAC operationsTheory.APPENDED_BDS THEN
  LRTAC THEN
  RECORD_TAC THEN
  ETAC stateTheory.INTERNAL_STATES_EQ THEN
  STAC
  ,
  ETAC operationsTheory.NOT_EXTENDED_ABSTRACT_BDS_TO_FETCH_AND_UNCHANGED_CHANNEL THEN
  LRTAC THEN
  PTAC stateTheory.INTERNAL_STATES_EQ THEN
  RLTAC THEN
  ETAC operationsTheory.EXTENDED_BDS THEN
  AIRTAC THEN
  AXTAC THEN
  LRTAC THEN
  ASM_NOT_EXISTS_TO_FORALL_NOT_TAC THEN
  PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (Q.SPEC ‘bd_ras_was_us’ thm)) THEN
  CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
 ]
 ,
 LRTAC THEN
 AITAC THEN
 LRTAC THEN
 IRTAC state_lemmasTheory.NOT_EXTERNAL_BDS_IMPLIES_INTERNAL_BDS_LEMMA THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY THEN
 INST_IMP_ASM_GOAL_TAC THEN
 STAC
]
QED

Theorem INTERNAL_STATES_EQ_LEMMA:
!device2 device3.
  INTERNAL_STATES_EQ device2 device3
  ==>
  device2.dma_state.internal_state = device3.dma_state.internal_state
Proof
INTRO_TAC THEN
ETAC stateTheory.INTERNAL_STATES_EQ THEN
STAC
QED

Theorem DEVICE_REGISTER_L2_L3_DMA_APPEND_EXTERNAL_ABSTRACT_BDS_DMA_MEMORY_WRITE_PRESERVES_L23EQ_LEMMA:
!device_characteristics memory1 memory2 device21 device device22 device31 device32 cpu_address_bytes dma_address_bytes.
  DEFINED_CHANNELS device_characteristics device /\
  L23EQ device_characteristics memory1 device device32 /\
  (device, dma_address_bytes, MAP SND cpu_address_bytes) = device_register_read_l2 device_characteristics memory1 device21 (MAP FST cpu_address_bytes) /\
  (device32, dma_address_bytes, MAP SND cpu_address_bytes) = device_register_read_l3 device_characteristics device31 (MAP FST cpu_address_bytes) /\
  device22 = dma_append_external_abstract_bds device_characteristics memory2 device /\
  memory2 = update_memory memory1 dma_address_bytes /\
  MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W device_characteristics device.dma_state.internal_state memory1 memory2
  ==>
  L23EQ device_characteristics memory2 device22 device32
Proof
INTRO_TAC THEN
ETAC L23EQ THEN
CONJS_TAC THENL
[
 ITAC INTERNAL_STATES_EQ_LEMMA THEN
 FIRTAC append_external_abstract_bds_l2_l3Theory.MEMORY_WRITE_APPENDS_EXTERNAL_BDS_AND_DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_BDS_TO_FETCH_EQ_LEMMA THEN
 STAC
 ,
 ETAC stateTheory.BDS_TO_UPDATE_EQ THEN
 INTRO_TAC THEN
 AITAC THEN
 IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_UPDATE_LEMMA THEN
 STAC
 ,
 ETAC stateTheory.BDS_TO_PROCESS_EQ THEN
 INTRO_TAC THEN
 AITAC THEN
 IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_PROCESS_LEMMA THEN
 STAC
 ,
 ETAC stateTheory.BDS_TO_WRITE_BACK_EQ THEN
 INTRO_TAC THEN
 AITAC THEN
 IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_WRITE_BACK_LEMMA THEN
 STAC
 ,
 ETAC stateTheory.MEMORY_REQUESTS_REPLIES_EQ THEN
 CONJS_TAC THENL
 [
  IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA THEN STAC
  ,
  IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REPLIES_LEMMA THEN STAC
  ,
  INTRO_TAC THEN
  AITAC THEN
  RLTAC THEN
  IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
  IRTAC internal_operation_lemmasTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_PENDING_ACCESSES_LEMMA THEN
  STAC
 ]
 ,
 ETAC stateTheory.FUNCTION_STATES_EQ THEN
 IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_FUNCTION_STATE_LEMMA THEN
 STAC
 ,
 ETAC stateTheory.INTERNAL_STATES_EQ THEN
 IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
 STAC
 ,
 ETAC stateTheory.DEFINED_CHANNELS_EQ THEN
 GEN_TAC THEN
 QRLTAC THEN
 EQ_TAC THENL
 [
  INTRO_TAC THEN
  Cases_on ‘VALID_CHANNEL_ID device_characteristics channel_id’ THENL
  [
   FIRTAC state_lemmasTheory.DEFINED_VALID_CHANNEL_IS_SOME_LEMMA THEN STAC
   ,
   IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_SOME_PRESERVED_LEMMA THEN RLTAC THEN STAC
  ]
  ,
  INTRO_TAC THEN
  Cases_on ‘VALID_CHANNEL_ID device_characteristics channel_id’ THENL
  [
   IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_SOME_LEMMA THEN STAC
   ,
   IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_SOME_PRESERVED_LEMMA THEN STAC
  ]
 ]
]
QED

Theorem DEVICE_REGISTER_READ_L2_PRESERVES_MEMORY_OR_APPENDS_EXTERNAL_CONCCRETE_BDS_R_W_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics cpu1 cpu2 memory1 memory2 device21 device cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_CPU_REGISTER_READ_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  EXTERNAL_BDS device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_read cpu_address_bytes) cpu2 /\
  (device, dma_address_bytes, MAP SND cpu_address_bytes) = device_register_read_l2 device_characteristics memory1 device21 (MAP FST cpu_address_bytes) /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  memory2 = memory1 \/
  MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W device_characteristics device.dma_state.internal_state memory1 memory2
Proof
INTRO_TAC THEN
PTAC l2Theory.device_register_read_l2 THEN
PTAC operationsTheory.device_register_read THENL
[
 PTAC operationsTheory.dma_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 3 THEN
 ETAC device_register_read_invariant_l2_preservation_lemmasTheory.FILTER_IS_VALID_L2_ID_LEMMA THEN
 PTAC proof_obligations_cpu_l2Theory.PROOF_OBLIGATION_CPU_REGISTER_READ_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W THEN
 AIRTAC THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 PTAC operationsTheory.function_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN STAC
]
QED

Theorem INTERNAL_BDS_PRESERVES_L23EQ_LEMMA:
!device_characteristics memory device2 device3.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  INTERNAL_BDS device_characteristics /\
  L23EQ device_characteristics memory device2 device3
  ==>
  !memory.
    L23EQ device_characteristics memory device2 device3
Proof
INTRO_TAC THEN
GEN_TAC THEN
ETAC L23EQ THEN
CONJS_TAC THEN TRY STAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
AITAC THEN
LRTAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY THEN
INST_IMP_ASM_GOAL_TAC THEN
STAC
QED

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_MEMORY_EQ_PRESERVE_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics memory device device22 device32.
  INTERNAL_STATES_EQ device device32 /\
  device22 = dma_append_external_abstract_bds device_characteristics memory device /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device device32
  ==>
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
AITAC THEN
ITAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL THEN
SPLIT_ASM_DISJS_TAC THENL
[
 ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH THEN
 ETAC operationsTheory.APPENDED_BDS THEN
 LRTAC THEN
 RECORD_TAC THEN
 IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
 ETAC stateTheory.INTERNAL_STATES_EQ THEN
 STAC
 ,
 ETAC operationsTheory.NOT_EXTENDED_ABSTRACT_BDS_TO_FETCH_AND_UNCHANGED_CHANNEL THEN
 STAC
]
QED

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_MEMORY_EQ_PRESERVES_L23EQ_LEMMA:
!device_characteristics memory device device22 device32.
  DEFINED_CHANNELS device_characteristics device /\
  L23EQ device_characteristics memory device device32 /\
  device22 = dma_append_external_abstract_bds device_characteristics memory device
  ==>
  L23EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
ETAC L23EQ THEN
CONJS_TAC THENL
[
 IRTAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_MEMORY_EQ_PRESERVE_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA THEN STAC
 ,
 ETAC stateTheory.BDS_TO_UPDATE_EQ THEN
 INTRO_TAC THEN
 AITAC THEN
 IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_UPDATE_LEMMA THEN
 STAC
 ,
 ETAC stateTheory.BDS_TO_PROCESS_EQ THEN
 INTRO_TAC THEN
 AITAC THEN
 IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_PROCESS_LEMMA THEN
 STAC
 ,
 ETAC stateTheory.BDS_TO_WRITE_BACK_EQ THEN
 INTRO_TAC THEN
 AITAC THEN
 IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_WRITE_BACK_LEMMA THEN
 STAC
 ,
 ETAC stateTheory.MEMORY_REQUESTS_REPLIES_EQ THEN
 CONJS_TAC THENL
 [
  IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA THEN STAC
  ,
  IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REPLIES_LEMMA THEN STAC
  ,
  IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
  INTRO_TAC THEN
  AITAC THEN
  IRTAC internal_operation_lemmasTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_PENDING_ACCESSES_LEMMA THEN
  AIRTAC THEN
  AIRTAC THEN
  STAC
 ]
 ,
 IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_FUNCTION_STATE_LEMMA THEN
 ETAC stateTheory.FUNCTION_STATES_EQ THEN
 STAC
 ,
 IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
 ETAC stateTheory.INTERNAL_STATES_EQ THEN
 STAC
 ,
 ETAC stateTheory.DEFINED_CHANNELS_EQ THEN
 GEN_TAC THEN
 QRLTAC THEN
 EQ_TAC THENL
 [
  INTRO_TAC THEN
  Cases_on ‘VALID_CHANNEL_ID device_characteristics channel_id’ THENL
  [
   IRTAC state_lemmasTheory.DEFINED_VALID_CHANNEL_IS_SOME_LEMMA THEN STAC
   ,
   IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_SOME_PRESERVED_LEMMA THEN STAC
  ]
  ,
  INTRO_TAC THEN
  Cases_on ‘VALID_CHANNEL_ID device_characteristics channel_id’ THENL
  [
   ITAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_SOME_LEMMA THEN STAC
   ,
   IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_SOME_PRESERVED_LEMMA THEN STAC
  ]
 ]
]
QED

Theorem DEVICE_REGISTER_READ_L2_IMPLIES_DEVICE_REGISTER_READ_IS_VALID_L2_LEMMA:
!device_characteristics memory1 device1 device2 cpu_address_bytes dma_address_bytes.
  (device2, dma_address_bytes, MAP SND cpu_address_bytes) = device_register_read_l2 device_characteristics memory1 device1 (MAP FST cpu_address_bytes)        
  ==>
  (device2, dma_address_bytes, MAP SND cpu_address_bytes) = device_register_read device_characteristics is_valid_l2 device1 (MAP FST cpu_address_bytes)
Proof
INTRO_TAC THEN
PTAC l2Theory.device_register_read_l2 THEN
STAC
QED

Theorem SYSTEM_SIM_L2_L3_CPU_REGISTER_READ_LEMMA:
!INVARIANT_CPU device_characteristics cpu1 cpu2 memory1 memory2 device31 device21 device22 cpu_transition cpu_dma_address_bytes.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_CPU_REGISTER_READ_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  DEFINED_CHANNELS device_characteristics device21 /\
  L23EQ device_characteristics memory1 device21 device31 /\
  INVARIANT_CPU memory1 cpu1 /\
  system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device21) (cpu_register_read_memory_write cpu_dma_address_bytes) (cpu2, memory2, device22)
  ==>
  ?device32.
    system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device31) (cpu_register_read_memory_write cpu_dma_address_bytes) (cpu2, memory2, device32) /\
    L23EQ device_characteristics memory2 device22 device32
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [l3Theory.device_transitions_l3_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
INTRO_TAC THEN
AXTAC THEN
PAT_X_ASSUM “x = (y, z)” (fn thm => ASSUME_TAC (GSYM thm)) THEN
NRLTAC 7 THEN
AXTAC THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 3 THEN
RLTAC THEN
ITAC register_read_l2_l3Theory.DEVICE_SIM_L2_L3_REGISTER_READ_LEMMA THEN
AXTAC THEN
INST_EXISTS_TAC THEN
CONJS_TAC THEN TRY (EXISTS_EQ_TAC THEN CONJS_TAC THEN TRY STAC THEN EXISTS_EQ_TAC THEN STAC) THEN
WEAKEN_TAC is_disj THEN
Cases_on ‘EXTERNAL_BDS device_characteristics’ THENL
[
 PTAC l2Theory.append_external_abstract_bds_l2 THEN
 ITAC DEVICE_REGISTER_READ_L2_PRESERVES_MEMORY_OR_APPENDS_EXTERNAL_CONCCRETE_BDS_R_W_LEMMA THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  RLTAC THEN
  PTAC l2Theory.device_register_read_l2 THEN
  IRTAC device_register_read_invariant_l2_preservation_lemmasTheory.DEVICE_REGISTER_READ_PRESERVES_DEFINED_CHANNELS_LEMMA THEN
  IRTAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_MEMORY_EQ_PRESERVES_L23EQ_LEMMA THEN
  STAC
  ,
  ITAC DEVICE_REGISTER_READ_L2_IMPLIES_DEVICE_REGISTER_READ_IS_VALID_L2_LEMMA THEN
  IRTAC device_register_read_invariant_l2_preservation_lemmasTheory.DEVICE_REGISTER_READ_PRESERVES_DEFINED_CHANNELS_LEMMA THEN
  IRTAC DEVICE_REGISTER_L2_L3_DMA_APPEND_EXTERNAL_ABSTRACT_BDS_DMA_MEMORY_WRITE_PRESERVES_L23EQ_LEMMA THEN
  STAC
 ]
 ,
 PTAC l2Theory.append_external_abstract_bds_l2 THEN
 RLTAC THEN
 IRTAC state_lemmasTheory.NOT_EXTERNAL_BDS_IMPLIES_INTERNAL_BDS_LEMMA THEN
 IRTAC INTERNAL_BDS_PRESERVES_L23EQ_LEMMA THEN
 STAC
]
QED

Theorem DEVICE_REGISTER_READ_L2_UPDATE_MEMORY_IMPLIES_APPEND_EXTERNAL_ABSTRACT_BDS_L2_LEMMA:
!device_characteristics memory1 memory2 device21 device22 cpu_address_bytes dma_address_bytes.
  (device22, dma_address_bytes, MAP SND cpu_address_bytes) = device_register_read_l2 device_characteristics memory1 device21 (MAP FST cpu_address_bytes) /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  ?device23.
    device23 = append_external_abstract_bds_l2 device_characteristics memory2 device22
Proof
INTRO_TAC THEN
EXISTS_EQ_TAC
QED

Theorem SYSTEM_SIM_L3_L2_CPU_REGISTER_READ_LEMMA:
!INVARIANT_CPU device_characteristics cpu1 cpu2 memory1 memory2 device21 device31 device32 cpu_transition cpu_dma_address_bytes.
  PROOF_OBLIGATION_CPU_REGISTER_READ_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  DEFINED_CHANNELS device_characteristics device21 /\
  L23EQ device_characteristics memory1 device21 device31 /\
  INVARIANT_CPU memory1 cpu1 /\
  system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device31) (cpu_register_read_memory_write cpu_dma_address_bytes) (cpu2, memory2, device32)
  ==>
  ?device22.
    system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device21) (cpu_register_read_memory_write cpu_dma_address_bytes) (cpu2, memory2, device22) /\
    L23EQ device_characteristics memory2 device22 device32
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [l3Theory.device_transitions_l3_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
INTRO_TAC THEN
AXTAC THEN
PAT_X_ASSUM “x = (y, z)” (fn thm => ASSUME_TAC (GSYM thm)) THEN
NRLTAC 7 THEN
AXTAC THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 3 THEN
RLTAC THEN
LRTAC THEN
ITAC register_read_l2_l3Theory.DEVICE_SIM_L3_L2_REGISTER_READ_LEMMA THEN
AXTAC THEN
ITAC DEVICE_REGISTER_READ_L2_UPDATE_MEMORY_IMPLIES_APPEND_EXTERNAL_ABSTRACT_BDS_L2_LEMMA THEN
AXTAC THEN
Q.EXISTS_TAC ‘device23’ THEN
CONJS_TAC THEN TRY (EXISTS_EQ_TAC THEN PAXTAC THEN CONJS_TAC THEN TRY STAC THEN EXISTS_EQ_TAC THEN STAC) THEN
WEAKEN_TAC is_disj THEN
Cases_on ‘EXTERNAL_BDS device_characteristics’ THENL
[
 PTAC l2Theory.append_external_abstract_bds_l2 THEN
 ITAC DEVICE_REGISTER_READ_L2_PRESERVES_MEMORY_OR_APPENDS_EXTERNAL_CONCCRETE_BDS_R_W_LEMMA THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  RLTAC THEN
  PTAC l2Theory.device_register_read_l2 THEN
  IRTAC device_register_read_invariant_l2_preservation_lemmasTheory.DEVICE_REGISTER_READ_PRESERVES_DEFINED_CHANNELS_LEMMA THEN
  IRTAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_MEMORY_EQ_PRESERVES_L23EQ_LEMMA THEN
  STAC
  ,
  ITAC DEVICE_REGISTER_READ_L2_IMPLIES_DEVICE_REGISTER_READ_IS_VALID_L2_LEMMA THEN
  IRTAC device_register_read_invariant_l2_preservation_lemmasTheory.DEVICE_REGISTER_READ_PRESERVES_DEFINED_CHANNELS_LEMMA THEN
  IRTAC DEVICE_REGISTER_L2_L3_DMA_APPEND_EXTERNAL_ABSTRACT_BDS_DMA_MEMORY_WRITE_PRESERVES_L23EQ_LEMMA THEN
  STAC
 ]
 ,
 PTAC l2Theory.append_external_abstract_bds_l2 THEN
 LRTAC THEN
 IRTAC state_lemmasTheory.NOT_EXTERNAL_BDS_IMPLIES_INTERNAL_BDS_LEMMA THEN
 IRTAC INTERNAL_BDS_PRESERVES_L23EQ_LEMMA THEN
 STAC
]
QED



Theorem SYSTEM_SIM_L2_L3_CPU_REGISTER_WRITE_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device21 device31 device22 cpu_transition cpu_dma_addresses INVARIANT_CPU.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_L2 device_characteristics memory1 device21 /\
  INVARIANT_L3 device_characteristics memory1 device31 /\
  L23EQ device_characteristics memory1 device21 device31 /\
  system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device21) (cpu_register_write_memory_write cpu_dma_addresses) (cpu2, memory2, device22)
  ==>
  ?device32.
    system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device31) (cpu_register_write_memory_write cpu_dma_addresses) (cpu2, memory2, device32) /\
    L23EQ device_characteristics memory2 device22 device32
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [l3Theory.device_transitions_l3_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
INTRO_TAC THEN
AXTAC THEN
PAT_X_ASSUM “x = (y, z)” (fn thm => ASSUME_TAC (GSYM thm)) THEN
NRLTAC 7 THEN
AXTAC THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 3 THEN
ITAC register_write_l2_l3Theory.DEVICE_SIM_L2_L3_REGISTER_WRITE_LEMMA THEN
AXTAC THEN
PAXTAC THEN
CONJS_TAC THEN TRY STAC THEN
EXISTS_EQ_TAC THEN
CONJS_TAC THEN TRY STAC THEN
EXISTS_EQ_TAC THEN
STAC
QED

Theorem SYSTEM_SIM_L3_L2_CPU_REGISTER_WRITE_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device21 device31 device32 cpu_transition cpu_dma_address_bytes INVARIANT_CPU.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_L2 device_characteristics memory1 device21 /\
  INVARIANT_L3 device_characteristics memory1 device31 /\
  L23EQ device_characteristics memory1 device21 device31 /\
  system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device31) (cpu_register_write_memory_write cpu_dma_address_bytes) (cpu2, memory2, device32)
  ==>
  ?device22.
    system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device21) (cpu_register_write_memory_write cpu_dma_address_bytes) (cpu2, memory2, device22) /\
    L23EQ device_characteristics memory2 device22 device32
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [l3Theory.device_transitions_l3_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
INTRO_TAC THEN
AXTAC THEN
PAT_X_ASSUM “x = (y, z)” (fn thm => ASSUME_TAC (GSYM thm)) THEN
NRLTAC 7 THEN
AXTAC THEN
NRLTAC 3 THEN
ITAC register_write_l2_l3Theory.DEVICE_SIM_L3_L2_REGISTER_WRITE_LEMMA THEN
AXTAC THEN
PAXTAC THEN
CONJS_TAC THEN TRY STAC THEN
EXISTS_EQ_TAC THEN
CONJS_TAC THEN TRY STAC THEN
EXISTS_EQ_TAC THEN
STAC
QED



Theorem SYSTEM_SIM_L2_L3_DEVICE_INTERNAL_OPERATION_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device31 device21 device22 cpu_transition.
  PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 device_characteristics /\
  INVARIANT_L3 device_characteristics memory1 device31 /\
  L23EQ device_characteristics memory1 device21 device31 /\
  system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device21) device_internal_operation (cpu2, memory2, device22)
  ==>
  ?device32.
    system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device31) device_internal_operation (cpu2, memory2, device32) /\
    L23EQ device_characteristics memory2 device22 device32
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [l3Theory.device_transitions_l3_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
INTRO_TAC THEN
AXTAC THEN
AXTAC THEN
ALL_RLTAC THEN
ITAC internal_device_operation_l2_l3Theory.DEVICE_SIM_L2_L3_INTERNAL_DEVICE_OPERATION_LEMMA THEN
AXTAC THEN
PAXTAC THEN
ASM_REWRITE_TAC [] THEN
INST_EXISTS_NAMES_TAC ["environment"] THEN
EXISTS_EQ_TAC THEN
EXISTS_EQ_TAC
QED

Theorem SYSTEM_SIM_L3_L2_DEVICE_INTERNAL_OPERATION_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device21 device31 device32 cpu_transition.
  PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 device_characteristics /\
  INVARIANT_L3 device_characteristics memory1 device31 /\
  L23EQ device_characteristics memory1 device21 device31 /\
  system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device31) device_internal_operation (cpu2, memory2, device32)
  ==>
  ?device22.
    system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device21) device_internal_operation (cpu2, memory2, device22) /\
    L23EQ device_characteristics memory2 device22 device32
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [l3Theory.device_transitions_l3_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
INTRO_TAC THEN
AXTAC THEN
AXTAC THEN
ALL_RLTAC THEN
ITAC internal_device_operation_l2_l3Theory.DEVICE_SIM_L3_L2_INTERNAL_DEVICE_OPERATION_LEMMA THEN
AXTAC THEN
PAXTAC THEN
ASM_REWRITE_TAC [] THEN
INST_EXISTS_NAMES_TAC ["environment"] THEN
EXISTS_EQ_TAC THEN
EXISTS_EQ_TAC
QED



Theorem SYSTEM_SIM_L2_L3_DEVICE_MEMORY_READ_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device31 device21 device22 cpu_transition l.
  L23EQ device_characteristics memory1 device21 device31 /\
  system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device21) (device_memory_read l) (cpu2, memory2, device22)
  ==>
  ?device32.
    system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device31) (device_memory_read l) (cpu2, memory2, device32) /\
    L23EQ device_characteristics memory2 device22 device32
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [l3Theory.device_transitions_l3_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
INTRO_TAC THEN
AXTAC THEN
ALL_LRTAC THEN
AXTAC THEN
LRTAC THEN
RLTAC THEN
IRTAC dma_request_served_l2_l3Theory.DEVICE_SIM_L2_L3_DMA_READ_REQUEST_SERVED_LEMMA THEN
AXTAC THEN
PAXTAC THEN
CONJ_TAC THENL
[
 EXISTS_EQ_TAC THEN
 ASM_REWRITE_TAC [] THEN
 EXISTS_EQ_TAC THEN
 STAC
 ,
 STAC
]
QED

Theorem SYSTEM_SIM_L3_L2_DEVICE_MEMORY_READ_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device21 device31 device32 cpu_transition l.
  L23EQ device_characteristics memory1 device21 device31 /\
  system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device31) (device_memory_read l) (cpu2, memory2, device32)
  ==>
  ?device22.
    system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device21) (device_memory_read l) (cpu2, memory2, device22) /\
    L23EQ device_characteristics memory2 device22 device32
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [l3Theory.device_transitions_l3_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
INTRO_TAC THEN
AXTAC THEN
ALL_LRTAC THEN
AXTAC THEN
LRTAC THEN
RLTAC THEN
IRTAC dma_request_served_l2_l3Theory.DEVICE_SIM_L3_L2_DMA_READ_REQUEST_SERVED_LEMMA THEN
AXTAC THEN
PAXTAC THEN
CONJ_TAC THENL
[
 EXISTS_EQ_TAC THEN
 ASM_REWRITE_TAC [] THEN
 EXISTS_EQ_TAC THEN
 STAC
 ,
 STAC
]
QED





Theorem SYSTEM_SIM_L2_L3_DEVICE_MEMORY_WRITE_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device31 device21 device22 cpu_transition l.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics /\
  INVARIANT_L3 device_characteristics memory1 device31 /\
  L23EQ device_characteristics memory1 device21 device31 /\
  system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device21) (device_memory_write l) (cpu2, memory2, device22)
  ==>
  ?device32.
    system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device31) (device_memory_write l) (cpu2, memory2, device32) /\
    L23EQ device_characteristics memory2 device22 device32
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [l3Theory.device_transitions_l3_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
INTRO_TAC THEN
AXTAC THEN
ALL_RLTAC THEN
AXTAC THEN
RLTAC THEN
LRTAC THEN
ITAC dma_request_served_l2_l3Theory.DEVICE_SIM_L2_L3_DMA_WRITE_REQUEST_SERVED_LEMMA_LEMMA THEN
AXTAC THEN
PAXTAC THEN
CONJ_TAC THENL
[
 EXISTS_EQ_TAC THEN
 ASM_REWRITE_TAC [] THEN
 EXISTS_EQ_TAC THEN
 STAC
 ,
 STAC
]
QED

Theorem SYSTEM_SIM_L3_L2_DEVICE_MEMORY_WRITE_LEMMA:
!device_characteristics cpu1 cpu2 memory1 memory2 device21 device31 device32 cpu_transition l.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics /\
  INVARIANT_L3 device_characteristics memory1 device31 /\
  L23EQ device_characteristics memory1 device21 device31 /\
  system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device31) (device_memory_write l) (cpu2, memory2, device32)
  ==>
  ?device22.
    system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device21) (device_memory_write l) (cpu2, memory2, device22) /\
    L23EQ device_characteristics memory2 device22 device32
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [l3Theory.device_transitions_l3_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
INTRO_TAC THEN
AXTAC THEN
ALL_RLTAC THEN
AXTAC THEN
RLTAC THEN
LRTAC THEN
ITAC dma_request_served_l2_l3Theory.DEVICE_SIM_L3_L2_DMA_WRITE_REQUEST_SERVED_LEMMA_LEMMA THEN
AXTAC THEN
PAXTAC THEN
CONJ_TAC THENL
[
 EXISTS_EQ_TAC THEN
 ASM_REWRITE_TAC [] THEN
 EXISTS_EQ_TAC THEN
 STAC
 ,
 STAC
]
QED



Theorem SYSTEM_SIM_L2_L3_LEMMA:
!device_characteristics INVARIANT_CPU cpu_transition cpu1 cpu2 memory1 memory2 device21 device22 device31 operation.
  PROOF_OBLIGATION_CPU_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_REGISTER_READ_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATIONS_DMA_L3 device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_L2 device_characteristics memory1 device21 /\
  INVARIANT_L3 device_characteristics memory1 device31 /\
  L23EQ device_characteristics memory1 device21 device31 /\
  system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device21) operation (cpu2, memory2, device22)
  ==>
  ?device32.
    system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device31) operation (cpu2, memory2, device32) /\
    L23EQ device_characteristics memory2 device22 device32
Proof
INTRO_TAC THEN
EXPAND_TERM_TAC "operation" THENL
[
 ITAC SYSTEM_SIM_L2_L3_CPU_INTERNAL_OPERATION_LEMMA THEN STAC
 ,
 ITAC SYSTEM_SIM_L2_L3_CPU_MEMORY_READ_LEMMA THEN STAC
 ,
 PTAC proof_obligations_dma_l3Theory.PROOF_OBLIGATIONS_DMA_L3 THEN
 PTAC proof_obligations_dma_l3Theory.PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 THEN
 ITAC SYSTEM_SIM_L2_L3_CPU_MEMORY_WRITE_LEMMA THEN STAC
 ,
 PTAC proof_obligations_dma_l3Theory.PROOF_OBLIGATIONS_DMA_L3 THEN
 ITAC invariant_l2_lemmasTheory.INVARIANT_L2_IMPLIES_DEFINED_CHANNELS_LEMMA THEN
 ITAC SYSTEM_SIM_L2_L3_CPU_REGISTER_READ_LEMMA THEN STAC
 ,
 PTAC proof_obligations_dma_l3Theory.PROOF_OBLIGATIONS_DMA_L3 THEN
 ITAC SYSTEM_SIM_L2_L3_CPU_REGISTER_WRITE_LEMMA THEN STAC
 ,
 PTAC proof_obligations_dma_l3Theory.PROOF_OBLIGATIONS_DMA_L3 THEN
 ITAC SYSTEM_SIM_L2_L3_DEVICE_INTERNAL_OPERATION_LEMMA THEN STAC
 ,
 ITAC SYSTEM_SIM_L2_L3_DEVICE_MEMORY_READ_LEMMA THEN STAC
 ,
 PTAC proof_obligations_dma_l3Theory.PROOF_OBLIGATIONS_DMA_L3 THEN
 PTAC proof_obligations_dma_l3Theory.PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 THEN
 ITAC SYSTEM_SIM_L2_L3_DEVICE_MEMORY_WRITE_LEMMA THEN STAC
]
QED

Theorem SYSTEM_SIM_L3_L2_LEMMA:
!device_characteristics INVARIANT_CPU cpu_transition cpu1 cpu2 memory1 memory2 device31 device32 device21 operation.
  PROOF_OBLIGATION_CPU_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_REGISTER_READ_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATIONS_DMA_L3 device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_L2 device_characteristics memory1 device21 /\
  INVARIANT_L3 device_characteristics memory1 device31 /\
  L23EQ device_characteristics memory1 device21 device31 /\
  system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device31) operation (cpu2, memory2, device32)
  ==>
  ?device22.
    system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device21) operation (cpu2, memory2, device22) /\
    L23EQ device_characteristics memory2 device22 device32
Proof
INTRO_TAC THEN
EXPAND_TERM_TAC "operation" THENL
[
 ITAC SYSTEM_SIM_L3_L2_CPU_INTERNAL_OPERATION_LEMMA THEN STAC
 ,
 ITAC SYSTEM_SIM_L3_L2_CPU_MEMORY_READ_LEMMA THEN STAC
 ,
 PTAC proof_obligations_dma_l3Theory.PROOF_OBLIGATIONS_DMA_L3 THEN
 PTAC proof_obligations_dma_l3Theory.PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 THEN
 ITAC SYSTEM_SIM_L3_L2_CPU_MEMORY_WRITE_LEMMA THEN STAC
 ,
 PTAC proof_obligations_dma_l3Theory.PROOF_OBLIGATIONS_DMA_L3 THEN
 PTAC proof_obligations_dma_l3Theory.PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 THEN
 ITAC invariant_l2_lemmasTheory.INVARIANT_L2_IMPLIES_DEFINED_CHANNELS_LEMMA THEN
 ITAC SYSTEM_SIM_L3_L2_CPU_REGISTER_READ_LEMMA THEN STAC
 ,
 PTAC proof_obligations_dma_l3Theory.PROOF_OBLIGATIONS_DMA_L3 THEN
 ITAC SYSTEM_SIM_L3_L2_CPU_REGISTER_WRITE_LEMMA THEN STAC
 ,
 PTAC proof_obligations_dma_l3Theory.PROOF_OBLIGATIONS_DMA_L3 THEN
 ITAC SYSTEM_SIM_L3_L2_DEVICE_INTERNAL_OPERATION_LEMMA THEN STAC
 ,
 ITAC SYSTEM_SIM_L3_L2_DEVICE_MEMORY_READ_LEMMA THEN STAC
 ,
 PTAC proof_obligations_dma_l3Theory.PROOF_OBLIGATIONS_DMA_L3 THEN
 PTAC proof_obligations_dma_l3Theory.PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 THEN
 ITAC SYSTEM_SIM_L3_L2_DEVICE_MEMORY_WRITE_LEMMA THEN STAC
]
QED

Theorem SYSTEM_BSIM_L2_L3_LEMMA:
!device_characteristics INVARIANT_CPU cpu_transition memory1 device21 device31.
  PROOF_OBLIGATION_CPU_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_REGISTER_READ_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATIONS_DMA_L3 device_characteristics /\
  INVARIANT_L2 device_characteristics memory1 device21 /\
  INVARIANT_L3 device_characteristics memory1 device31 /\
  L23EQ device_characteristics memory1 device21 device31
  ==>
  (!cpu1 cpu2 memory2 device22 operation.
     INVARIANT_CPU memory1 cpu1 /\
     system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device21) operation (cpu2, memory2, device22)
     ==>
     ?device32.
     system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device31) operation (cpu2, memory2, device32) /\
     L23EQ device_characteristics memory2 device22 device32)
  /\
  (!cpu1 cpu2 memory2 device32 operation.
     INVARIANT_CPU memory1 cpu1 /\
     system_transition cpu_transition (device_transition_l3 device_characteristics) (cpu1, memory1, device31) operation (cpu2, memory2, device32)
     ==>
     ?device22. 
     system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device21) operation (cpu2, memory2, device22) /\
     L23EQ device_characteristics memory2 device22 device32)
Proof
INTRO_TAC THEN
CONJ_TAC THENL
[
 INTRO_TAC THEN
 IRTAC SYSTEM_SIM_L2_L3_LEMMA THEN
 STAC
 ,
 INTRO_TAC THEN
 IRTAC SYSTEM_SIM_L3_L2_LEMMA THEN
 STAC
]
QED

val _ = export_theory();

