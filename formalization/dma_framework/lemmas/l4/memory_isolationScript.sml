open HolKernel Parse boolLib bossLib helper_tactics;
open l4Theory invariant_l4Theory;

val _ = new_theory "memory_isolation";


(*******************************************************************************)
(* Reading only readable memory. ***********************************************)
(*******************************************************************************)

Theorem DMA_READ_LEMMA:
!cpu_transition device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 address_bytes.
  INVARIANT_L4 device_characteristics memory1 device1 /\
  system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) (device_memory_read address_bytes) (cpu2, memory2, device2)
  ==>
  EVERY (device_characteristics.dma_characteristics.R memory1) (MAP FST address_bytes)
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [l4Theory.device_transitions_l4_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
INTRO_TAC THEN
AXTAC THEN
NRLTAC 7 THEN
AXTAC THEN
NRLTAC 2 THEN
REPEAT (WEAKEN_TAC is_eq) THEN
ETAC l4Theory.dma_pending_requests_l4 THEN
ETAC INVARIANT_L4 THEN
IRTAC dma_pending_requests_properties_lemmasTheory.DEVICE_REQUESTING_READ_ADDRESSES_IMPLIES_READABLE_REQUEST_LEMMA THEN
STAC
QED

(*******************************************************************************)
(* Writing only writable memory. ***********************************************)
(*******************************************************************************)

Theorem DMA_WRITE_LEMMA:
!cpu_transition device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 address_bytes.
  INVARIANT_L4 device_characteristics memory1 device1 /\
  system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) (device_memory_write address_bytes) (cpu2, memory2, device2)
  ==>
  EVERY (device_characteristics.dma_characteristics.W memory1) (MAP FST address_bytes)
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [l4Theory.device_transitions_l4_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
INTRO_TAC THEN
AXTAC THEN
NRLTAC 7 THEN
AXTAC THEN
NRLTAC 2 THEN
REPEAT (WEAKEN_TAC is_eq) THEN
ETAC l4Theory.dma_pending_requests_l4 THEN
ETAC INVARIANT_L4 THEN
ITAC dma_pending_requests_properties_lemmasTheory.DEVICE_REQUESTING_WRITE_ADDRESSES_IMPLIES_WRITABLE_REQUEST_LEMMA THEN
STAC
QED

(*******************************************************************************)
(* DMA device performs only allowed memory accesses. ***************************)
(*******************************************************************************)

Theorem DMA_READ_WRITE_LEMMA:
!cpu_transition INVARIANT_CPU device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 operation address_bytes.
  INVARIANT_L4 device_characteristics memory1 device1 /\
  INVARIANT_CPU memory1 cpu1 /\
  system_transition cpu_transition (device_transition_l4 device_characteristics) (cpu1, memory1, device1) operation (cpu2, memory2, device2)
  ==>
  (operation = device_memory_read  address_bytes ==> EVERY (device_characteristics.dma_characteristics.R memory1) (MAP FST address_bytes)) /\
  (operation = device_memory_write address_bytes ==> EVERY (device_characteristics.dma_characteristics.W memory1) (MAP FST address_bytes))
Proof
INTRO_TAC THEN
CONJ_TAC THEN DISCH_TAC THEN LRTAC THENL
[
 ITAC DMA_READ_LEMMA THEN STAC
 ,
 ITAC DMA_WRITE_LEMMA THEN STAC
]
QED



val _ = export_theory();

