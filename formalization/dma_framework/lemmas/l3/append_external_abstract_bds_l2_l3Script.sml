open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory l2Theory L23EQTheory invariant_l3Theory proof_obligationsTheory;

val _ = new_theory "append_external_abstract_bds_l2_l3";

Theorem MEMORY_WRITE_APPENDS_EXTERNAL_BDS_AND_DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics device21 device22 device31 memory1 memory2.
  MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W device_characteristics device31.dma_state.internal_state memory1 memory2 /\
  device22 = dma_append_external_abstract_bds device_characteristics memory2 device21 /\
  INTERNAL_STATES_EQ device21 device31 /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory1 device21 device31
  ==>
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory2 device22 device31
Proof
INTRO_TAC THEN
ETAC ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
PTAC INTERNAL_STATES_EQ THEN
INTRO_TAC THEN
AITAC THEN
IRTAC dma_append_external_abstract_bds_lemmasTheory.MEMORY_WRITE_APPENDS_EXTERNAL_BDS_AND_DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_EQ_ABSTRACT_EXTERNAL_BDS_TO_FETCH_LEMMA THEN
STAC
QED

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_BDS_TO_FETCH_EQ_L2_L3_LEMMA:
!device_characteristics INVARIANT_CPU cpu_transition cpu1 cpu2 memory1 memory2 device21 device22 device31
 address_bytes.
  PROOF_OBLIGATION_CPU_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_L3 device_characteristics memory1 device31 /\
  EXTERNAL_BDS device_characteristics /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes /\
  device22 = dma_append_external_abstract_bds device_characteristics memory2 device21 /\
  INTERNAL_STATES_EQ device21 device31 /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory1 device21 device31
  ==>
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory2 device22 device31
Proof
INTRO_TAC THEN
ITAC invariant_l3_lemmasTheory.PROOF_OBLIGATION_CPU_APPENDS_EXTERNAL_CONCRETE_BDS_IMPlIES_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_LEMMA THEN
ITAC MEMORY_WRITE_APPENDS_EXTERNAL_BDS_AND_DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_BDS_TO_FETCH_EQ_LEMMA THEN
STAC
QED

Theorem DEVICE_SIM_L2_L3_EXTERNAL_BDS_APPENDED_BDS_TO_FETCH_LEMMA:
!device_characteristics INVARIANT_CPU MEMORY_ADDRESSES cpu_transition cpu1 cpu2
 device21 device22 device31 memory1 memory2 address_bytes.
  PROOF_OBLIGATION_CPU_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_L3 device_characteristics memory1 device31 /\
  EVERY MEMORY_ADDRESSES (MAP FST address_bytes) /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes /\
  device22 = append_external_abstract_bds_l2 device_characteristics memory2 device21 /\
  INTERNAL_STATES_EQ device21 device31 /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory1 device21 device31
  ==>
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory2 device22 device31
Proof
INTRO_TAC THEN
PTAC append_external_abstract_bds_l2 THENL
[
 FITAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_BDS_TO_FETCH_EQ_L2_L3_LEMMA THEN STAC
 ,
 LRTAC THEN
 ETAC ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
 INTRO_TAC THEN
 AITAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY THEN
 IRTAC state_lemmasTheory.NOT_EXTERNAL_BDS_IMPLIES_INTERNAL_BDS_LEMMA THEN
 AIRTAC THEN
 LRTAC THEN
 ONCE_ASM_REWRITE_TAC [] THEN
 REWRITE_TAC []
]
QED

Theorem APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_BDS_TO_UPDATE_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device3  : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id channel1 channel2 channel3.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  device22 = append_external_abstract_bds_l2 device_characteristics memory device21 /\
  channel1 = schannel device21 channel_id /\
  channel2 = schannel device22 channel_id /\
  channel3 = schannel device3 channel_id /\
  channel1.queue.bds_to_update = channel3.queue.bds_to_update
  ==>
  channel2.queue.bds_to_update = channel3.queue.bds_to_update
Proof
INTRO_TAC THEN
PTAC append_external_abstract_bds_l2 THENL
[
 IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_UPDATE_LEMMA THEN
 STAC
 ,
 STAC
]
QED

Theorem APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_BDS_TO_PROCESS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device3  : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id channel1 channel2 channel3.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  device22 = append_external_abstract_bds_l2 device_characteristics memory device21 /\
  channel1 = schannel device21 channel_id /\
  channel2 = schannel device22 channel_id /\
  channel3 = schannel device3 channel_id /\
  channel1.queue.bds_to_process = channel3.queue.bds_to_process
  ==>
  channel2.queue.bds_to_process = channel3.queue.bds_to_process
Proof
INTRO_TAC THEN
PTAC append_external_abstract_bds_l2 THENL
[
 IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_PROCESS_LEMMA THEN
 STAC
 ,
 STAC
]
QED

Theorem APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_BDS_TO_WRITE_BACK_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device3  : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id channel1 channel2 channel3.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  device22 = append_external_abstract_bds_l2 device_characteristics memory device21 /\
  channel1 = schannel device21 channel_id /\
  channel2 = schannel device22 channel_id /\
  channel3 = schannel device3 channel_id /\
  channel1.queue.bds_to_write_back = channel3.queue.bds_to_write_back
  ==>
  channel2.queue.bds_to_write_back = channel3.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC append_external_abstract_bds_l2 THENL
[
 IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_WRITE_BACK_LEMMA THEN
 STAC
 ,
 STAC
]
QED

Theorem APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_PENDING_ACCESSES_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device3  : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id channel1 channel2 channel3.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  device22 = append_external_abstract_bds_l2 device_characteristics memory device21 /\
  channel1 = schannel device21 channel_id /\
  channel2 = schannel device22 channel_id /\
  channel3 = schannel device3 channel_id /\
  channel1.pending_accesses = channel3.pending_accesses
  ==>
  channel2.pending_accesses = channel3.pending_accesses
Proof
INTRO_TAC THEN
PTAC append_external_abstract_bds_l2 THENL
[
 IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_PENDING_ACCESSES_LEMMA THEN
 STAC
 ,
 STAC
]
QED

Theorem APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_DEFINED_CHANNEL_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id.
  DEFINED_CHANNELS device_characteristics device1 /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  device2 = append_external_abstract_bds_l2 device_characteristics memory device1
  ==>
  IS_SOME (device2.dma_state.channels channel_id)
Proof
INTRO_TAC THEN
PTAC append_external_abstract_bds_l2 THENL
[
 IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_SOME_LEMMA THEN
 STAC
 ,
 IRTAC state_lemmasTheory.DEFINED_VALID_CHANNEL_IS_SOME_LEMMA THEN
 STAC
]
QED

Theorem APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_DEFINED_CHANNELS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id.
  DEFINED_CHANNELS device_characteristics device1 /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  device2 = append_external_abstract_bds_l2 device_characteristics memory device1
  ==>
  IS_SOME (device2.dma_state.channels channel_id) = IS_SOME (device1.dma_state.channels channel_id)
Proof
INTRO_TAC THEN
ITAC state_lemmasTheory.DEFINED_VALID_CHANNEL_IS_SOME_LEMMA THEN
ITAC APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_DEFINED_CHANNEL_LEMMA THEN
STAC
QED

Theorem APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA:
!device_characteristics memory device21 device22 device3.
  device22 = append_external_abstract_bds_l2 device_characteristics memory device21 /\
  device21.dma_state.pending_register_related_memory_requests = device3.dma_state.pending_register_related_memory_requests
  ==>
  device22.dma_state.pending_register_related_memory_requests = device3.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
PTAC append_external_abstract_bds_l2 THENL
[
 ITAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA THEN
 STAC
 ,
 STAC
]
QED

Theorem APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_FUNCTION_STATE_LEMMA:
!device_characteristics memory device21 device22 device3.
  device22 = append_external_abstract_bds_l2 device_characteristics memory device21 /\
  device21.function_state = device3.function_state
  ==>
  device22.function_state = device3.function_state
Proof
INTRO_TAC THEN
PTAC append_external_abstract_bds_l2 THENL
[
 ITAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_FUNCTION_STATE_LEMMA THEN
 STAC
 ,
 STAC
]
QED

Theorem APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_INTERNAL_STATE_LEMMA:
!device_characteristics memory device21 device22 device3.
  device22 = append_external_abstract_bds_l2 device_characteristics memory device21 /\
  device21.dma_state.internal_state = device3.dma_state.internal_state
  ==>
  device22.dma_state.internal_state = device3.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC append_external_abstract_bds_l2 THENL
[
 ITAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
 STAC
 ,
 STAC
]
QED







Theorem DEVICE_SIM_L2_L3_EXTERNAL_BDS_APPENDED_BDS_TO_UPDATE_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device3  : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  device22 = append_external_abstract_bds_l2 device_characteristics memory device21 /\
  BDS_TO_UPDATE_EQ device_characteristics device21 device3
  ==>
  BDS_TO_UPDATE_EQ device_characteristics device22 device3
Proof
INTRO_TAC THEN
ETAC BDS_TO_UPDATE_EQ THEN
INTRO_TAC THEN
AITAC THEN
IRTAC APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_BDS_TO_UPDATE_LEMMA THEN
STAC
QED

Theorem DEVICE_SIM_L2_L3_EXTERNAL_BDS_APPENDED_BDS_TO_PROCESS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device3  : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  device22 = append_external_abstract_bds_l2 device_characteristics memory device21 /\
  BDS_TO_PROCESS_EQ device_characteristics device21 device3
  ==>
  BDS_TO_PROCESS_EQ device_characteristics device22 device3
Proof
INTRO_TAC THEN
ETAC BDS_TO_PROCESS_EQ THEN
INTRO_TAC THEN
AITAC THEN
IRTAC APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_BDS_TO_PROCESS_LEMMA THEN
STAC
QED

Theorem DEVICE_SIM_L2_L3_EXTERNAL_BDS_APPENDED_BDS_TO_WRITE_BACK_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device3  : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  device22 = append_external_abstract_bds_l2 device_characteristics memory device21 /\
  BDS_TO_WRITE_BACK_EQ device_characteristics device21 device3
  ==>
  BDS_TO_WRITE_BACK_EQ device_characteristics device22 device3
Proof
INTRO_TAC THEN
ETAC BDS_TO_WRITE_BACK_EQ THEN
INTRO_TAC THEN
AITAC THEN
IRTAC APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_BDS_TO_WRITE_BACK_LEMMA THEN
STAC
QED

Theorem DEVICE_SIM_L2_L3_EXTERNAL_BDS_APPENDED_MEMORY_REQUESTS_REPLIES_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device3  : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  device22 = append_external_abstract_bds_l2 device_characteristics memory device21 /\
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device21 device3
  ==>
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device22 device3
Proof
INTRO_TAC THEN
ETAC MEMORY_REQUESTS_REPLIES_EQ THEN
REPEAT CONJ_TAC THENL
[
 IRTAC APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA THEN
 STAC
 ,
 PTAC l2Theory.append_external_abstract_bds_l2 THENL
 [
  IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REPLIES_LEMMA THEN
  STAC
  ,
  IRTAC append_bds_lemmasTheory.DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REPLIES_LEMMA THEN
  STAC
 ]
 ,
 INTRO_TAC THEN
 AITAC THEN
 IRTAC APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_PENDING_ACCESSES_LEMMA THEN
 STAC
]
QED

Theorem DEVICE_SIM_L2_L3_EXTERNAL_BDS_APPENDED_FUNCTION_STATE_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device3  : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  device22 = append_external_abstract_bds_l2 device_characteristics memory device21 /\
  FUNCTION_STATES_EQ device21 device3
  ==>
  FUNCTION_STATES_EQ device22 device3
Proof
INTRO_TAC THEN
ETAC FUNCTION_STATES_EQ THEN
IRTAC APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_FUNCTION_STATE_LEMMA THEN
STAC
QED

Theorem DEVICE_SIM_L2_L3_EXTERNAL_BDS_APPENDED_INTERNAL_STATE_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device3  : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  device22 = append_external_abstract_bds_l2 device_characteristics memory device21 /\
  INTERNAL_STATES_EQ device21 device3
  ==>
  INTERNAL_STATES_EQ device22 device3
Proof
INTRO_TAC THEN
ETAC INTERNAL_STATES_EQ THEN
IRTAC APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_INTERNAL_STATE_LEMMA THEN
STAC
QED

Theorem DEVICE_SIM_L2_L3_EXTERNAL_BDS_APPENDED_DEFINED_CHANNELS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory1 memory2
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device3  : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  INVARIANT_L2 device_characteristics memory1 device21 /\
  device22 = append_external_abstract_bds_l2 device_characteristics memory2 device21 /\
  DEFINED_CHANNELS_EQ device_characteristics device21 device3
  ==>
  DEFINED_CHANNELS_EQ device_characteristics device22 device3
Proof
INTRO_TAC THEN
IRTAC invariant_l2_lemmasTheory.INVARIANT_L2_IMPLIES_DEFINED_CHANNELS_LEMMA THEN
ETAC DEFINED_CHANNELS_EQ THEN
GEN_TAC THEN
EQ_TAC THENL
[
 INTRO_TAC THEN
 Cases_on ‘VALID_CHANNEL_ID device_characteristics channel_id’ THENL
 [
  IRTAC state_lemmasTheory.DEFINED_VALID_CHANNEL_IS_SOME_LEMMA THEN
  QLRTAC THEN
  QLRTAC THEN
  STAC
  ,
  PTAC append_external_abstract_bds_l2 THEN (TRY STAC) THEN
  IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_SOME_PRESERVED_LEMMA THEN
  QLRTAC THEN
  QLRTAC THEN
  STAC
 ]
 ,
 INTRO_TAC THEN
 Cases_on ‘VALID_CHANNEL_ID device_characteristics channel_id’ THENL
 [
  QRLTAC THEN
  IRTAC APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_DEFINED_CHANNELS_LEMMA THEN
  STAC
  ,
  PTAC append_external_abstract_bds_l2 THEN (TRY STAC) THEN
  IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_SOME_PRESERVED_LEMMA THEN
  STAC
 ]
]
QED

Theorem DEVICE_SIM_L2_L3_EXTERNAL_BDS_APPENDED_LEMMA:
!device_characteristics INVARIANT_CPU MEMORY_ADDRESSES cpu_transition cpu1 cpu2
 device21 device22 device31 memory1 memory2 address_bytes.
  PROOF_OBLIGATION_CPU_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_L2 device_characteristics memory1 device21 /\
  INVARIANT_L3 device_characteristics memory1 device31 /\
  EVERY MEMORY_ADDRESSES (MAP FST address_bytes) /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes /\
  device22 = append_external_abstract_bds_l2 device_characteristics memory2 device21 /\
  L23EQ device_characteristics memory1 device21 device31
  ==>
  L23EQ device_characteristics memory2 device22 device31
Proof
REWRITE_TAC [L23EQ] THEN
INTRO_TAC THEN
REPEAT CONJ_TAC THENL
[
 IRTAC DEVICE_SIM_L2_L3_EXTERNAL_BDS_APPENDED_BDS_TO_FETCH_LEMMA THEN STAC
 ,
 IRTAC DEVICE_SIM_L2_L3_EXTERNAL_BDS_APPENDED_BDS_TO_UPDATE_LEMMA THEN STAC
 ,
 IRTAC DEVICE_SIM_L2_L3_EXTERNAL_BDS_APPENDED_BDS_TO_PROCESS_LEMMA THEN STAC
 ,
 IRTAC DEVICE_SIM_L2_L3_EXTERNAL_BDS_APPENDED_BDS_TO_WRITE_BACK_LEMMA THEN STAC
 ,
 IRTAC DEVICE_SIM_L2_L3_EXTERNAL_BDS_APPENDED_MEMORY_REQUESTS_REPLIES_LEMMA THEN STAC
 ,
 IRTAC DEVICE_SIM_L2_L3_EXTERNAL_BDS_APPENDED_FUNCTION_STATE_LEMMA THEN STAC
 ,
 IRTAC DEVICE_SIM_L2_L3_EXTERNAL_BDS_APPENDED_INTERNAL_STATE_LEMMA THEN STAC
 ,
 IRTAC DEVICE_SIM_L2_L3_EXTERNAL_BDS_APPENDED_DEFINED_CHANNELS_LEMMA THEN STAC
]
QED








(*******************************************************************************)
(*******************************************************************************)
(*******************************************************************************)
(*******************************************************************************)
(*******************************************************************************)
(*******************************************************************************)
(*******************************************************************************)
(*******************************************************************************)
(*******************************************************************************)
(*******************************************************************************)
(*******************************************************************************)
(*******************************************************************************)


Theorem DEVICE_SIM_L3_L2_EXTERNAL_BDS_APPENDED_LEMMA:
!device_characteristics INVARIANT_CPU MEMORY_ADDRESSES cpu_transition cpu1 cpu2
 device21 device31 memory1 memory2 address_bytes.
  PROOF_OBLIGATION_CPU_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_L2 device_characteristics memory1 device21 /\
  INVARIANT_L3 device_characteristics memory1 device31 /\
  EVERY MEMORY_ADDRESSES (MAP FST address_bytes) /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes /\
  L23EQ device_characteristics memory1 device21 device31
  ==>
  ?device22.
    device22 = append_external_abstract_bds_l2 device_characteristics memory2 device21 /\
    L23EQ device_characteristics memory2 device22 device31
Proof
INTRO_TAC THEN
EXISTS_EQ_TAC THEN
IRTAC DEVICE_SIM_L2_L3_EXTERNAL_BDS_APPENDED_LEMMA THEN
STAC
QED

val _ = export_theory();

