open HolKernel Parse boolLib bossLib helper_tactics;
open l1Theory l2Theory l3Theory l4Theory invariant_l4Theory;
open proof_obligations_cpu_l4Theory proof_obligations_dma_l4Theory;

val _ = new_theory "l4_eq_l1";

Theorem INVARIANT_L4_IMPLIES_INVARIANT_CONCRETE_L4_LEMMA:
!device_characteristics memory device.
  INVARIANT_L4 device_characteristics memory device
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory device
Proof
REWRITE_TAC [INVARIANT_L4, INVARIANT_CONCRETE_L4] THEN
INTRO_TAC THEN
STAC
QED

Theorem PROOF_OBLIGATIONS_CPU_L4_IMPLIES_PROOF_OBLIGATION_CPU_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics.
  PROOF_OBLIGATIONS_CPU_L4 INVARIANT_CPU cpu_transition device_characteristics
  ==>
  PROOF_OBLIGATION_CPU_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4 INVARIANT_CPU cpu_transition device_characteristics
Proof
REWRITE_TAC [PROOF_OBLIGATIONS_CPU_L4] THEN
INTRO_TAC THEN
STAC
QED

Theorem PROOF_OBLIGATIONS_DMA_L4_IMPLIES_PROOF_OBLIGATIONS_DMA_L3_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics
  ==>
  PROOF_OBLIGATIONS_DMA_L3 device_characteristics
Proof
INTRO_TAC THEN
ETAC proof_obligations_dma_l4Theory.PROOF_OBLIGATIONS_DMA_L4 THEN
ETAC proof_obligations_dma_l3Theory.PROOF_OBLIGATIONS_DMA_L3 THEN
ETAC proof_obligations_dma_l3Theory.PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 THEN
ETAC proof_obligations_dma_l3Theory.PROOF_OBLIGATIONS_FETCH_UPDATE_PROCESS_WRITE_BACK_L2_L3 THEN
STAC
QED

Theorem PROOF_OBLIGATIONS_CPU_L4_IMPLIES_PROOF_OBLIGATIONS_APPENDS_CONCRETE_BDS_R_W_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics.
  PROOF_OBLIGATIONS_CPU_L4 INVARIANT_CPU cpu_transition device_characteristics
  ==>
  PROOF_OBLIGATION_CPU_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_REGISTER_READ_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics
Proof
REWRITE_TAC [PROOF_OBLIGATIONS_CPU_L4] THEN
INTRO_TAC THEN
STAC
QED

Theorem INVARIANT_L4_IMPLIES_DEFINED_CHANNELS_LEMMA:
!device_characteristics memory device.
  INVARIANT_L4 device_characteristics memory device
  ==>
  DEFINED_CHANNELS device_characteristics device
Proof
INTRO_TAC THEN
ETAC INVARIANT_L4 THEN
STAC
QED

Theorem INVARIANT_L4_IMPLIES_INVARIANT_L3_LEMMA:
!device_characteristics memory device.
  INVARIANT_L4 device_characteristics memory device
  ==>
  INVARIANT_L3 device_characteristics memory device
Proof
REWRITE_TAC [INVARIANT_L4, invariant_l3Theory.INVARIANT_L3] THEN
INTRO_TAC THEN
STAC
QED

Theorem PROOF_OBLIGATIONS_DMA_L4_IMPLIES_PROOF_OBLIGATIONS_DMA_L2_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics
  ==>
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics
Proof
INTRO_TAC THEN
ETAC proof_obligations_dma_l4Theory.PROOF_OBLIGATIONS_DMA_L4 THEN
ETAC proof_obligations_dma_l2Theory.PROOF_OBLIGATIONS_DMA_L2 THEN
STAC
QED

Theorem PROOF_OBLIGATIONS_DMA_L4_IMPLIES_PROOF_OBLIGATIONS_REGISTER_REQUESTS_ADDRESS_SCRATCHPAD_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics
  ==>
  PROOF_OBLIGATION_REGISTER_READ_MEMORY_READ_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_REGISTER_READ_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_READ_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics
Proof
INTRO_TAC THEN
ETAC proof_obligations_dma_l4Theory.PROOF_OBLIGATIONS_DMA_L4 THEN
STAC
QED

Theorem SYSTEM_SIM_L4_L1_LEMMA:
!device_characteristics INVARIANT_CPU cpu_transition cpu1 cpu2 memory1 memory2 device41 device42 device11 operation.
  PROOF_OBLIGATIONS_CPU_L4 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_L4 device_characteristics memory1 device41 /\
  L23EQ device_characteristics memory1 device11 device41 /\
  system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device41) operation (cpu2, memory2, device42)
  ==>
  ?device12.
    system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1, memory1, device11) operation (cpu2, memory2, device12) /\
    L23EQ device_characteristics memory2 device12 device42
Proof
INTRO_TAC THEN
ITAC INVARIANT_L4_IMPLIES_INVARIANT_CONCRETE_L4_LEMMA THEN
ITAC PROOF_OBLIGATIONS_CPU_L4_IMPLIES_PROOF_OBLIGATION_CPU_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN
ITAC l3_eq_l4Theory.SYSTEM_BSIM_L3_L4_LEMMA THEN
QLRTAC THEN
ITAC PROOF_OBLIGATIONS_DMA_L4_IMPLIES_PROOF_OBLIGATIONS_DMA_L3_LEMMA THEN
ITAC PROOF_OBLIGATIONS_CPU_L4_IMPLIES_PROOF_OBLIGATIONS_APPENDS_CONCRETE_BDS_R_W_LEMMA THEN
ITAC INVARIANT_L4_IMPLIES_INVARIANT_L3_LEMMA THEN
ITAC L23EQ_lemmasTheory.L23EQ_INVARIANT_L3_IMPLIES_INVARIANT_L2_LEMMA THEN
ITAC l2_eq_l3Theory.SYSTEM_BSIM_L2_L3_LEMMA THEN
WEAKEN_TAC is_forall THEN
AITAC THEN
AXTAC THEN
ITAC PROOF_OBLIGATIONS_DMA_L4_IMPLIES_PROOF_OBLIGATIONS_DMA_L2_LEMMA THEN
IRTAC PROOF_OBLIGATIONS_DMA_L4_IMPLIES_PROOF_OBLIGATIONS_REGISTER_REQUESTS_ADDRESS_SCRATCHPAD_LEMMA THEN
IRTAC l1_eq_l2Theory.SYSTEM_BSIM_L1_L2_LEMMA THEN
QLRTAC THEN
PAXTAC THEN
STAC
QED

Theorem SYSTEM_SIM_L1_L4_LEMMA:
!device_characteristics INVARIANT_CPU cpu_transition cpu1 cpu2 memory1 memory2 device11 device12 device41 operation.
  PROOF_OBLIGATIONS_CPU_L4 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_L4 device_characteristics memory1 device41 /\
  L23EQ device_characteristics memory1 device11 device41 /\
  system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1, memory1, device11) operation (cpu2, memory2, device12)
  ==>
  ?device42.
    system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device41) operation (cpu2, memory2, device42) /\
    L23EQ device_characteristics memory2 device12 device42
Proof
INTRO_TAC THEN
ITAC PROOF_OBLIGATIONS_DMA_L4_IMPLIES_PROOF_OBLIGATIONS_DMA_L2_LEMMA THEN
ITAC INVARIANT_L4_IMPLIES_INVARIANT_L3_LEMMA THEN
ITAC L23EQ_lemmasTheory.L23EQ_INVARIANT_L3_IMPLIES_INVARIANT_L2_LEMMA THEN
ITAC PROOF_OBLIGATIONS_DMA_L4_IMPLIES_PROOF_OBLIGATIONS_REGISTER_REQUESTS_ADDRESS_SCRATCHPAD_LEMMA THEN
ITAC l1_eq_l2Theory.SYSTEM_BSIM_L1_L2_LEMMA THEN
QRLTAC THEN
ITAC PROOF_OBLIGATIONS_DMA_L4_IMPLIES_PROOF_OBLIGATIONS_DMA_L3_LEMMA THEN
ITAC PROOF_OBLIGATIONS_CPU_L4_IMPLIES_PROOF_OBLIGATIONS_APPENDS_CONCRETE_BDS_R_W_LEMMA THEN
ITAC l2_eq_l3Theory.SYSTEM_BSIM_L2_L3_LEMMA THEN
AITAC THEN
WEAKEN_TAC is_forall THEN
AXTAC THEN
IRTAC INVARIANT_L4_IMPLIES_INVARIANT_CONCRETE_L4_LEMMA THEN
IRTAC PROOF_OBLIGATIONS_CPU_L4_IMPLIES_PROOF_OBLIGATION_CPU_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN
IRTAC l3_eq_l4Theory.SYSTEM_BSIM_L3_L4_LEMMA THEN
QRLTAC THEN
PAXTAC THEN
STAC
QED

Theorem SYSTEM_BSIM_L4_L1_LEMMA:
!device_characteristics INVARIANT_CPU cpu_transition memory1 device11 device41.
  PROOF_OBLIGATIONS_CPU_L4 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INVARIANT_L4 device_characteristics memory1 device41 /\
  L23EQ device_characteristics memory1 device11 device41
  ==>
  (!cpu1 cpu2 memory2 device42 operation.
     INVARIANT_CPU memory1 cpu1 /\
     system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device41) operation (cpu2, memory2, device42)
     ==>
     ?device12.
       system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1, memory1, device11) operation (cpu2, memory2, device12) /\
       L23EQ device_characteristics memory2 device12 device42)
  /\
  (!cpu1 cpu2 memory2 device12 operation.
     INVARIANT_CPU memory1 cpu1 /\
     system_transition cpu_transition (device_transition_l1 device_characteristics) (cpu1, memory1, device11) operation (cpu2, memory2, device12)
     ==>
     ?device42. 
       system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device41) operation (cpu2, memory2, device42) /\
       L23EQ device_characteristics memory2 device12 device42)
Proof
INTRO_TAC THEN
CONJ_TAC THENL
[
 INTRO_TAC THEN
 IRTAC SYSTEM_SIM_L4_L1_LEMMA THEN
 STAC
 ,
 INTRO_TAC THEN
 IRTAC SYSTEM_SIM_L1_L4_LEMMA THEN
 STAC
]
QED

val _ = export_theory();

