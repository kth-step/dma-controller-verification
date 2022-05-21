open HolKernel Parse boolLib bossLib helper_tactics;
open l3Theory invariant_l3Theory proof_obligations_cpu_l3Theory;

val _ = new_theory "device_register_write_invariant_concrete_l3_preservation_lemmas";

Theorem FUNCTION_REGISTER_WRITE_PRESERVES_DMA_STATE_LEMMA:
!device_characteristics device1 device2 address_bytes.
  device2 = function_register_write device_characteristics device1 address_bytes
  ==>
  device2.dma_state = device1.dma_state
Proof
INTRO_TAC THEN
PTAC operationsTheory.function_register_write THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem FUNCTION_REGISTER_WRITE_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA:
!device_characteristics memory device1 device2 address_bytes.
  device2 = function_register_write device_characteristics device1 address_bytes /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device1
  ==>
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device2
Proof
INTRO_TAC THEN
IRTAC FUNCTION_REGISTER_WRITE_PRESERVES_DMA_STATE_LEMMA THEN
ETAC NO_MEMORY_WRITES_TO_BDS THEN
ETAC operationsTheory.channel_requests THEN
LRTAC THEN
STAC
QED

Theorem FUNCTION_REGISTER_WRITE_PRESERVES_NOT_DMA_BDS_LEMMA:
!device_characteristics memory device1 device2 address_bytes.
  device2 = function_register_write device_characteristics device1 address_bytes /\
  NOT_DMA_BDS device_characteristics memory device1
  ==>
  NOT_DMA_BDS device_characteristics memory device2
Proof
INTRO_TAC THEN
IRTAC FUNCTION_REGISTER_WRITE_PRESERVES_DMA_STATE_LEMMA THEN
ETAC NOT_DMA_BDS THEN
LRTAC THEN
STAC
QED

Theorem FUNCTION_REGISTER_WRITE_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics device1 device2 address_bytes.
  device2 = function_register_write device_characteristics device1 address_bytes /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device1
  ==>
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device2
Proof
INTRO_TAC THEN
IRTAC FUNCTION_REGISTER_WRITE_PRESERVES_DMA_STATE_LEMMA THEN
ETAC MEMORY_WRITES_PRESERVES_BDS_TO_FETCH THEN
RECORD_TAC THEN
STAC
QED

Theorem FUNCTION_REGISTER_WRITE_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA:
!device_characteristics memory device1 device2 address_bytes.
  device2 = function_register_write device_characteristics device1 address_bytes /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device1
  ==>
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device2
Proof
INTRO_TAC THEN
IRTAC FUNCTION_REGISTER_WRITE_PRESERVES_DMA_STATE_LEMMA THEN
ETAC INVARIANT_EXTERNAL_FETCH_BD_REPLY THEN
RW_HYPS_TAC stateTheory.schannel THEN
REWRITE_TAC [stateTheory.schannel] THEN
LRTAC THEN
STAC
QED

Theorem FUNCTION_REGISTER_WRITE_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA:
!device_characteristics memory device1 device2 address_bytes.
  device2 = function_register_write device_characteristics device1 address_bytes /\
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device1
  ==>
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
IRTAC FUNCTION_REGISTER_WRITE_PRESERVES_DMA_STATE_LEMMA THEN
ETAC FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES THEN
RW_HYPS_TAC stateTheory.schannel THEN
REWRITE_TAC [stateTheory.schannel] THEN
LRTAC THEN
STAC
QED

Theorem FUNCTION_REGISTER_WRITE_PRESERVES_INVARIANT_BDS_TO_FETCH_DISJOINT_LEMMA:
!device_characteristics memory device1 device2 address_bytes.
  device2 = function_register_write device_characteristics device1 address_bytes /\
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device1
  ==>
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device2
Proof
INTRO_TAC THEN
IRTAC FUNCTION_REGISTER_WRITE_PRESERVES_DMA_STATE_LEMMA THEN
ETAC invariant_l3Theory.INVARIANT_BDS_TO_FETCH_DISJOINT THEN
STAC
QED



Theorem FUNCTION_REGISTER_WRITE_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA:
!device_characteristics memory device1 device2 address_bytes.
  device2 = function_register_write device_characteristics device1 address_bytes /\
  INVARIANT_CONCRETE_L3 device_characteristics memory device1
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_CONCRETE_L3 THEN
ITAC FUNCTION_REGISTER_WRITE_PRESERVES_INVARIANT_BDS_TO_FETCH_DISJOINT_LEMMA THEN
ITAC FUNCTION_REGISTER_WRITE_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA THEN
ITAC FUNCTION_REGISTER_WRITE_PRESERVES_NOT_DMA_BDS_LEMMA THEN
ITAC FUNCTION_REGISTER_WRITE_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA THEN
ITAC FUNCTION_REGISTER_WRITE_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA THEN
ITAC FUNCTION_REGISTER_WRITE_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA THEN
STAC
QED

Theorem FILTER_IS_VALID_L3_ID_LEMMA:
!new_requests.
  FILTER is_valid_l3 new_requests = new_requests
Proof
Induct THEN REWRITE_TAC [listTheory.FILTER] THEN
GEN_TAC THEN
PTAC l3Theory.is_valid_l3 THEN
REWRITE_TAC [l3Theory.is_valid_l3] THEN
STAC
QED

Theorem DMA_REGISTER_WRITE_L3_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics cpu1 cpu2 memory1 memory2
 device1 device2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L3 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATIONS_DMA_L3 device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write cpu_address_bytes) cpu2 /\
  (device2, dma_address_bytes) = dma_register_write device_characteristics is_valid_l3 NONE device1 cpu_address_bytes /\
  memory2 = update_memory memory1 dma_address_bytes /\
  INVARIANT_CONCRETE_L3 device_characteristics memory1 device1
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_register_write THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 2 THEN
ETAC FILTER_IS_VALID_L3_ID_LEMMA THEN
RLTAC THEN
PTAC proof_obligations_cpu_l3Theory.PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L3 THEN
AIRTAC THEN
PTAC operationsTheory.update_memory_option THEN
LRTAC THEN
PTAC operationsTheory.dma_append_internal_abstract_bds THEN
RLTAC THEN
STAC
QED

Theorem DEVICE_REGISTER_WRITE_L3_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L3 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATIONS_DMA_L3 device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write cpu_address_bytes) cpu2 /\
  (device2, dma_address_bytes) = device_register_write_l3 device_characteristics device1 cpu_address_bytes /\
  memory2 = update_memory memory1 dma_address_bytes /\
  INVARIANT_CONCRETE_L3 device_characteristics memory1 device1
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
PTAC l3Theory.device_register_write_l3 THEN
PTAC operationsTheory.device_register_write THENL
[
 IRTAC DMA_REGISTER_WRITE_L3_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ITAC FUNCTION_REGISTER_WRITE_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA THEN
 IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN STAC
]
QED

val _ = export_theory();

