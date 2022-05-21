open HolKernel Parse boolLib bossLib helper_tactics;
open l4Theory invariant_l4_lemmasTheory proof_obligations_cpu_l4Theory;

val _ = new_theory "device_register_write_invariant_concrete_l4_preservation_lemmas";

Theorem FUNCTION_REGISTER_WRITE_L4_IMPLIES_BDS_TO_FETCH_NOT_EXPANDED_LEMMA:
!device_characteristics memory cpu_address_bytes device1 device2.
  device2 = function_register_write device_characteristics device1 cpu_address_bytes
  ==>
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC operationsTheory.function_register_write THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [BDS_TO_FETCH_NOT_EXPANDED_REFL_LEMMA]
QED

Theorem FUNCTION_REGISTER_WRITE_L4_IMPLIES_CHANNELS_EQ_LEMMA:
!device_characteristics cpu_address_bytes device1 device2.
  device2 = function_register_write device_characteristics device1 cpu_address_bytes
  ==>
  CHANNELS_EQ device1 device2
Proof
INTRO_TAC THEN
PTAC operationsTheory.function_register_write THEN
LRTAC THEN
ETAC stateTheory.CHANNELS_EQ THEN
RECORD_TAC THEN
STAC
QED

Theorem FUNCTION_REGISTER_WRITE_L4_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA:
!device_characteristics cpu_address_bytes device1 device2.
  device2 = function_register_write device_characteristics device1 cpu_address_bytes
  ==>
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC operationsTheory.function_register_write THEN
LRTAC THEN 
RECORD_TAC THEN
ETAC stateTheory.BD_TRANSFER_RAS_WAS_EQ THEN
STAC
QED

Theorem FILTER_IS_VALID_L4_ID_LEMMA:
!new_requests.
  FILTER is_valid_l4 new_requests = new_requests
Proof
Induct THEN REWRITE_TAC [listTheory.FILTER] THEN
GEN_TAC THEN
PTAC l4Theory.is_valid_l4 THEN
REWRITE_TAC [l4Theory.is_valid_l4] THEN
STAC
QED

Theorem DMA_REGISTER_WRITE_L4_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 INVARIANT_CPU cpu_transition  cpu1 cpu2 memory1 memory2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write cpu_address_bytes) cpu2 /\
  (device2, dma_address_bytes) = dma_register_write device_characteristics is_valid_l4 NONE device1 cpu_address_bytes /\
  memory2 = update_memory memory1 dma_address_bytes /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_register_write THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 2 THEN
ETAC FILTER_IS_VALID_L4_ID_LEMMA THEN
RLTAC THEN
PTAC proof_obligations_cpu_l4Theory.PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4 THEN
AIRTAC THEN
PTAC operationsTheory.update_memory_option THEN
LRTAC THEN
PTAC operationsTheory.dma_append_internal_abstract_bds THEN
STAC
QED

Theorem FUNCTION_REGISTER_WRITE_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!device_characteristics memory device1 device2 cpu_address_bytes.
  device2 = function_register_write device_characteristics device1 cpu_address_bytes /\
  INVARIANT_CONCRETE_L4 device_characteristics memory device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ITAC FUNCTION_REGISTER_WRITE_L4_IMPLIES_BDS_TO_FETCH_NOT_EXPANDED_LEMMA THEN
ITAC FUNCTION_REGISTER_WRITE_L4_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA THEN
ITAC FUNCTION_REGISTER_WRITE_L4_IMPLIES_CHANNELS_EQ_LEMMA THEN
ITAC CHANNELS_EQ_IMPLIES_BDS_TO_UPDATE_NOT_EXPANDED_LEMMA THEN
ITAC CHANNELS_EQ_IMPLIES_BDS_TO_PROCESS_NOT_EXPANDED_LEMMA THEN
IRTAC CHANNELS_EQ_IMPLIES_BDS_TO_WRITE_BACK_NOT_EXPANDED_LEMMA THEN
ETAC invariant_l4Theory.INVARIANT_CONCRETE_L4 THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4_LEMMA THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4_LEMMA THEN
ITAC BDS_TO_UPDATE_NOT_EXPANDED_PRESERVES_INVARIANT_UPDATE_BD_BD_WRITE_L4_LEMMA THEN
ITAC BDS_TO_PROCESS_NOT_EXPANDED_PRESERVES_INVARIANT_PROCESS_BD_BD_WRITE_L4_LEMMA THEN
ITAC BDS_TO_WRITE_BACK_NOT_EXPANDED_PRESERVES_INVARIANT_WRITE_BACK_BD_BD_WRITE_L4_LEMMA THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_INVARIANT_FETCH_BD_DMA_WRITE_L4_LEMMA THEN
ITAC BDS_TO_UPDATE_NOT_EXPANDED_PRESERVES_INVARIANT_UPDATE_BD_DMA_WRITE_L4_LEMMA THEN
IRTAC BDS_TO_PROCESS_NOT_EXPANDED_PRESERVES_INVARIANT_PROCESS_BD_DMA_WRITE_L4_LEMMA THEN
STAC
QED

Theorem DEVICE_REGISTER_WRITE_L4_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics cpu1 cpu2 memory1 memory2 cpu_address_bytes dma_address_bytes device1 device2.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L4 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write cpu_address_bytes) cpu2 /\
  (device2, dma_address_bytes) = device_register_write_l4 device_characteristics device1 cpu_address_bytes /\
  memory2 = update_memory memory1 dma_address_bytes /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
PTAC l4Theory.device_register_write_l4 THEN
PTAC operationsTheory.device_register_write THENL
[
 IRTAC DMA_REGISTER_WRITE_L4_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
 IRTAC FUNCTION_REGISTER_WRITE_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN STAC
]
QED

val _ = export_theory();

