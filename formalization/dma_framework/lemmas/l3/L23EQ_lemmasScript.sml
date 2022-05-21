open HolKernel Parse boolLib bossLib helper_tactics;
open L23EQTheory stateTheory invariant_l1Theory invariant_l2Theory invariant_l3Theory;

val _ = new_theory "L23EQ_lemmas";

Theorem L23EQ_IMPLIES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_EQ_LEMMA:
!device_characteristics memory device21 device31.
  L23EQ device_characteristics memory device21 device31
  ==>
  device31.dma_state.pending_register_related_memory_requests =
  device21.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
ETAC L23EQ THEN
ETAC stateTheory.MEMORY_REQUESTS_REPLIES_EQ THEN
STAC
QED

Theorem L23EQ_IMPLIES_PENDING_REGISTER_RELATED_MEMORY_REPLIES_EQ_LEMMA:
!device_characteristics memory device21 device31.
  L23EQ device_characteristics memory device21 device31
  ==>
  device31.dma_state.pending_register_related_memory_replies =
  device21.dma_state.pending_register_related_memory_replies
Proof
INTRO_TAC THEN
ETAC L23EQ THEN
ETAC stateTheory.MEMORY_REQUESTS_REPLIES_EQ THEN
STAC
QED

Theorem ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_PRESERVED_LEMMA:
!device_characteristics memory device21 device22 device31 device32.
  ABSTRACT_BDS_TO_FETCH_EQ device_characteristics device21 device22 /\
  CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device31 device32 /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device21 device31
  ==>
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
ETAC stateTheory.CONCRETE_BDS_TO_FETCH_EQ THEN
ETAC ABSTRACT_BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
REPEAT AITAC THEN
RLTAC THEN
RLTAC THEN
STAC
QED

Theorem BDS_TO_UPDATE_EQ_PRESERVED_LEMMA:
!device_characteristics device21 device22 device31 device32.
  BDS_TO_UPDATE_EQ device_characteristics device21 device22 /\
  BDS_TO_UPDATE_EQ device_characteristics device31 device32 /\
  BDS_TO_UPDATE_EQ device_characteristics device21 device31
  ==>
  BDS_TO_UPDATE_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_UPDATE_EQ THEN
INTRO_TAC THEN
REPEAT AITAC THEN
STAC
QED

Theorem BDS_TO_PROCESS_EQ_PRESERVED_LEMMA:
!device_characteristics device21 device22 device31 device32.
  BDS_TO_PROCESS_EQ device_characteristics device21 device22 /\
  BDS_TO_PROCESS_EQ device_characteristics device31 device32 /\
  BDS_TO_PROCESS_EQ device_characteristics device21 device31
  ==>
  BDS_TO_PROCESS_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_PROCESS_EQ THEN
INTRO_TAC THEN
REPEAT AITAC THEN
STAC
QED

Theorem BDS_TO_WRITE_BACK_EQ_PRESERVED_LEMMA:
!device_characteristics device21 device22 device31 device32.
  BDS_TO_WRITE_BACK_EQ device_characteristics device21 device22 /\
  BDS_TO_WRITE_BACK_EQ device_characteristics device31 device32 /\
  BDS_TO_WRITE_BACK_EQ device_characteristics device21 device31
  ==>
  BDS_TO_WRITE_BACK_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_WRITE_BACK_EQ THEN
INTRO_TAC THEN
REPEAT AITAC THEN
STAC
QED

Theorem MEMORY_REQUESTS_REPLIES_EQ_PRESERVED_LEMMA:
!device_characteristics device21 device22 device31 device32.
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device21 device22 /\
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device31 device32 /\
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device21 device31
  ==>
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.MEMORY_REQUESTS_REPLIES_EQ THEN
REPEAT CONJ_TAC THEN
 (STAC ORELSE (INTRO_TAC THEN REPEAT AITAC THEN STAC))
QED

Theorem FUNCTION_STATES_EQ_PRESERVED_LEMMA:
!device21 device22 device31 device32.
  FUNCTION_STATES_EQ device21 device22 /\
  FUNCTION_STATES_EQ device31 device32 /\
  FUNCTION_STATES_EQ device21 device31
  ==>
  FUNCTION_STATES_EQ device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.FUNCTION_STATES_EQ THEN
STAC
QED

Theorem DEFINED_CHANNELS_EQ_PRESERVED_LEMMA:
!device_characteristics device21 device22 device31 device32.
  DEFINED_CHANNELS_EQ device_characteristics device21 device22 /\
  DEFINED_CHANNELS_EQ device_characteristics device31 device32 /\
  DEFINED_CHANNELS_EQ device_characteristics device21 device31
  ==>
  DEFINED_CHANNELS_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.DEFINED_CHANNELS_EQ THEN
GEN_TAC THEN
QRLTAC THEN
QRLTAC THEN
STAC
QED

Theorem L23EQ_IMPLIES_FUNCTION_STATE_EQ_LEMMA:
!device_characteristics memory device21 device31.
  L23EQ device_characteristics memory device21 device31
  ==>
  device21.function_state = device31.function_state
Proof
INTRO_TAC THEN
PTAC L23EQ THEN
PTAC stateTheory.FUNCTION_STATES_EQ THEN
STAC
QED

Theorem L23EQ_IMPLIES_INTERNAL_STATE_EQ_LEMMA:
!device_characteristics memory device21 device31.
  L23EQ device_characteristics memory device21 device31
  ==>
  device21.dma_state.internal_state = device31.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC L23EQ THEN
PTAC stateTheory.INTERNAL_STATES_EQ THEN
STAC
QED

Theorem FUNCTION_STATES_EQ_UPDATE_DEVICE_STATE_PRESERVES_FUNCTION_STATES_EQ_LEMMA:
!channel_id internal_state2 channel22 channel32
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device31 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device32 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  device22 = update_device_state device21 channel_id internal_state2 channel22 /\
  device32 = update_device_state device31 channel_id internal_state2 channel32 /\
  FUNCTION_STATES_EQ device21 device31
  ==>
  FUNCTION_STATES_EQ device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.FUNCTION_STATES_EQ THEN
ETAC operationsTheory.update_device_state THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem INTERNAL_STATES_EQ_UPDATE_DEVICE_STATE_PRESERVES_INTERNAL_STATES_EQ_LEMMA:
!channel_id internal_state2 channel22 channel32
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device31 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device32 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  device22 = update_device_state device21 channel_id internal_state2 channel22 /\
  device32 = update_device_state device31 channel_id internal_state2 channel32 /\
  INTERNAL_STATES_EQ device21 device31
  ==>
  INTERNAL_STATES_EQ device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.INTERNAL_STATES_EQ THEN
ETAC operationsTheory.update_device_state THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem DEFINED_CHANNELS_EQ_UPDATE_DEVICE_STATE_PRESERVES_DEFINED_CHANNELS_EQ_LEMMA:
!device_characteristics channel_id internal_state2 channel22 channel32 
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device31 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device32 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  device22 = update_device_state device21 channel_id internal_state2 channel22 /\
  device32 = update_device_state device31 channel_id internal_state2 channel32 /\
  DEFINED_CHANNELS_EQ device_characteristics device21 device31
  ==>
  DEFINED_CHANNELS_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.DEFINED_CHANNELS_EQ THEN
GEN_TAC THEN
ETAC operationsTheory.update_device_state THEN
ALL_LRTAC THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 REWRITE_TAC [optionTheory.IS_SOME_DEF]
 ,
 STAC
]
QED

Theorem L23EQ_IMPLIES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA:
!device_characteristics memory device21 device31 channel_id channels21 channels31
 channel21 channel31 concrete_bds31.
  L23EQ device_characteristics memory device21 device31 /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channels21 = device21.dma_state.channels /\
  channels31 = device31.dma_state.channels /\
  channel21 = THE (channels21 channel_id) /\
  channel31 = THE (channels31 channel_id) /\
  concrete_bds31 = (cverification device_characteristics channel_id).bds_to_fetch memory device31.dma_state.internal_state
  ==>
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds31 channel21 channel31
Proof
INTRO_TAC THEN
PTAC L23EQ THEN
PTAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
PTAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
AITAC THEN
RLTAC THEN
LRTAC THEN
PTAC stateTheory.BDS_TO_UPDATE_EQ THEN AITAC THEN
PTAC stateTheory.BDS_TO_PROCESS_EQ THEN AITAC THEN
PTAC stateTheory.BDS_TO_WRITE_BACK_EQ THEN AITAC THEN
PTAC stateTheory.MEMORY_REQUESTS_REPLIES_EQ THEN AITAC THEN
ETAC stateTheory.schannel THEN
RLTAC THEN
RLTAC THEN
RLTAC THEN
RLTAC THEN
STAC
QED

Theorem ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_BDS_TO_UPDATE_EQ_LEMMA:
!concrete_bds channel2 channel3.
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds channel2 channel3
  ==>
  channel2.queue.bds_to_update = channel3.queue.bds_to_update
Proof
INTRO_TAC THEN
PTAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
STAC
QED

Theorem ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_BDS_TO_PROCESS_EQ_LEMMA:
!concrete_bds channel2 channel3.
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds channel2 channel3
  ==>
  channel2.queue.bds_to_process = channel3.queue.bds_to_process
Proof
INTRO_TAC THEN
PTAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
STAC
QED

Theorem ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_BDS_TO_WRITE_BACK_EQ_LEMMA:
!concrete_bds channel2 channel3.
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds channel2 channel3
  ==>
  channel2.queue.bds_to_write_back = channel3.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
STAC
QED

Theorem ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_MEMORY_REQUESTS_REPLIES_EQ_LEMMA:
!concrete_bds channel2 channel3.
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds channel2 channel3
  ==>
  channel2.pending_accesses = channel3.pending_accesses
Proof
INTRO_TAC THEN
PTAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
STAC
QED



Theorem L23EQ_IMPLIES_MEMORY_REQUESTS_REPLIES_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory device1 device2.
  L23EQ device_characteristics memory device1 device2
  ==>
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device1 device2
Proof
INTRO_TAC THEN
ETAC L23EQ THEN
STAC
QED

Theorem L23EQ_IMPLIES_DMA_REQUESTING_READ_ADDRESSES_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory device1 device2.
  L23EQ device_characteristics memory device1 device2
  ==>
  DMA_REQUESTING_READ_ADDRESSES device_characteristics memory device2 =
  DMA_REQUESTING_READ_ADDRESSES device_characteristics memory device1
Proof
INTRO_TAC THEN
ETAC read_propertiesTheory.DMA_REQUESTING_READ_ADDRESSES THEN
REWRITE_TAC [GSYM stateTheory.schannel] THEN
EQ_TAC THEN
 INTRO_TAC THEN
 INTRO_TAC THEN
 AITAC THEN
 ETAC read_propertiesTheory.CHANNEL_REQUESTING_READ_ADDRESSES THEN
 IRTAC L23EQ_IMPLIES_MEMORY_REQUESTS_REPLIES_EQ_LEMMA THEN
 IRTAC dma_pending_requests_lemmasTheory.MEMORY_REQUESTS_REPLIES_EQ_IMPLIES_CHANNEL_PENDING_REQUESTS_EQ_LEMMA THEN
 LRTAC THEN
 STAC
QED

Theorem L23EQ_IMPLIES_DMA_REQUESTING_WRITE_ADDRESSES_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory device1 device2.
  L23EQ device_characteristics memory device1 device2
  ==>
  DMA_REQUESTING_WRITE_ADDRESSES device_characteristics memory device2 =
  DMA_REQUESTING_WRITE_ADDRESSES device_characteristics memory device1
Proof
INTRO_TAC THEN
ETAC write_propertiesTheory.DMA_REQUESTING_WRITE_ADDRESSES THEN
REWRITE_TAC [GSYM stateTheory.schannel] THEN
EQ_TAC THEN
 INTRO_TAC THEN
 INTRO_TAC THEN
 AITAC THEN
 ETAC write_propertiesTheory.CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
 IRTAC L23EQ_IMPLIES_MEMORY_REQUESTS_REPLIES_EQ_LEMMA THEN
 IRTAC dma_pending_requests_lemmasTheory.MEMORY_REQUESTS_REPLIES_EQ_IMPLIES_CHANNEL_PENDING_REQUESTS_EQ_LEMMA THEN
 LRTAC THEN
 STAC
QED

Theorem L23EQ_IMPLIES_REGISTER_REQUESTING_READ_ADDRESSES_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory device1 device2.
  L23EQ device_characteristics memory device1 device2
  ==>
  REGISTER_REQUESTING_READ_ADDRESSES device_characteristics memory device2 =
  REGISTER_REQUESTING_READ_ADDRESSES device_characteristics memory device1
Proof
INTRO_TAC THEN
ETAC read_propertiesTheory.REGISTER_REQUESTING_READ_ADDRESSES THEN
EQ_TAC THEN
 INTRO_TAC THEN
 INTRO_TAC THEN
 IRTAC L23EQ_IMPLIES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_EQ_LEMMA THEN
 LRTAC THEN
 AIRTAC THEN
 STAC
QED

Theorem L23EQ_IMPLIES_REGISTER_REQUESTING_READ_ADDRESSES_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory device1 device2.
  L23EQ device_characteristics memory device1 device2
  ==>
  REGISTER_REQUESTING_READ_ADDRESSES device_characteristics memory device2 =
  REGISTER_REQUESTING_READ_ADDRESSES device_characteristics memory device1
Proof
INTRO_TAC THEN
ETAC read_propertiesTheory.REGISTER_REQUESTING_READ_ADDRESSES THEN
EQ_TAC THEN
 INTRO_TAC THEN
 INTRO_TAC THEN
 IRTAC L23EQ_IMPLIES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_EQ_LEMMA THEN
 LRTAC THEN
 AIRTAC THEN
 STAC
QED

Theorem L23EQ_IMPLIES_REGISTER_REQUESTING_WRITE_ADDRESSES_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory device1 device2.
  L23EQ device_characteristics memory device1 device2
  ==>
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device2 =
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device1
Proof
INTRO_TAC THEN
ETAC write_propertiesTheory.REGISTER_REQUESTING_WRITE_ADDRESSES THEN
EQ_TAC THEN
 INTRO_TAC THEN
 INTRO_TAC THEN
 IRTAC L23EQ_IMPLIES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_EQ_LEMMA THEN
 LRTAC THEN
 AIRTAC THEN
 STAC
QED

Theorem L23EQ_IMPLIES_INVARIANT_L1_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory device1 device2.
  L23EQ device_characteristics memory device1 device2
  ==>
  INVARIANT_L1 device_characteristics memory device2 = INVARIANT_L1 device_characteristics memory device1
Proof
INTRO_TAC THEN
ETAC INVARIANT_L1 THEN
ETAC read_propertiesTheory.DEVICE_REQUESTING_READ_ADDRESSES THEN
ETAC write_propertiesTheory.DEVICE_REQUESTING_WRITE_ADDRESSES THEN
ITAC L23EQ_IMPLIES_DMA_REQUESTING_READ_ADDRESSES_EQ_LEMMA THEN
ITAC L23EQ_IMPLIES_DMA_REQUESTING_WRITE_ADDRESSES_EQ_LEMMA THEN
ITAC L23EQ_IMPLIES_REGISTER_REQUESTING_READ_ADDRESSES_EQ_LEMMA THEN
ITAC L23EQ_IMPLIES_REGISTER_REQUESTING_WRITE_ADDRESSES_EQ_LEMMA THEN
STAC
QED






Theorem L23EQ_IMPLIES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory device2 device3.
  L23EQ device_characteristics memory device2 device3
  ==>
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device2 device3
Proof
INTRO_TAC THEN
PTAC L23EQ THEN
STAC
QED

Theorem L23EQ_IMPLIES_ABSTRACT_EQ_CONCRETE_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory device2 device3.
  L23EQ device_characteristics memory device2 device3
  ==>
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device2 device2
Proof
INTRO_TAC THEN
ITAC L23EQ_IMPLIES_INTERNAL_STATE_EQ_LEMMA THEN
IRTAC L23EQ_IMPLIES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
LRTAC THEN
INTRO_TAC THEN
AIRTAC THEN
STAC
QED

Theorem L23EQ_IMPLIES_DEFINED_CHANNELS_EQUIV_LEMMA:
!device_characteristics memory device1 device2.
  L23EQ device_characteristics memory device1 device2
  ==>
  DEFINED_CHANNELS_EQ device_characteristics device1 device2
Proof
INTRO_TAC THEN
ETAC L23EQ THEN
STAC
QED

Theorem L23EQ_IMPLIES_DEFINED_CHANNELS_EQ_LEMMA:
!device_characteristics memory device1 device2.
  L23EQ device_characteristics memory device1 device2
  ==>
  DEFINED_CHANNELS device_characteristics device2 =
  DEFINED_CHANNELS device_characteristics device1
Proof
INTRO_TAC THEN
IRTAC L23EQ_IMPLIES_DEFINED_CHANNELS_EQUIV_LEMMA THEN
ETAC stateTheory.DEFINED_CHANNELS_EQ THEN
ETAC stateTheory.DEFINED_CHANNELS THEN
ETAC stateTheory.VALID_CHANNELS THEN
EQ_TAC THEN
 INTRO_TAC THEN
 INTRO_TAC THEN
 AIRTAC THEN
 TRY QRLTAC THEN
 STAC
QED

Theorem L23EQ_IMPLIES_INVARIANT_FETCH_BD_L3_EQ_L2_LEMMA:
!device_characteristics memory device1 device2.
  L23EQ device_characteristics memory device1 device2
  ==>
  INVARIANT_FETCH_BD_L3 device_characteristics memory device2 =
  INVARIANT_FETCH_BD_L2 device_characteristics memory device1
Proof
INTRO_TAC THEN
ITAC L23EQ_IMPLIES_INTERNAL_STATE_EQ_LEMMA THEN
IRTAC L23EQ_IMPLIES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA THEN
EQ_TAC THENL
[
 INTRO_TAC THEN
 ETAC INVARIANT_FETCH_BD_L3 THEN
 ETAC INVARIANT_FETCH_BD_L2 THEN
 INTRO_TAC THEN
 PTAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
 AITAC THEN
 RLTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN
 AIRTAC THEN
 STAC
 ,
 INTRO_TAC THEN
 ETAC INVARIANT_FETCH_BD_L3 THEN
 ETAC INVARIANT_FETCH_BD_L2 THEN
 INTRO_TAC THEN
 PTAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
 AITAC THEN
 RLTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN LRTAC THEN RLTAC THEN LRTAC THEN
 AIRTAC THEN
 STAC
]
QED

Theorem L23EQ_IMPLIES_BDS_TO_UPDATE_EQ_LEMMA:
!device_characteristics memory device1 device2.
  L23EQ device_characteristics memory device1 device2
  ==>
  BDS_TO_UPDATE_EQ device_characteristics device1 device2
Proof
INTRO_TAC THEN
PTAC L23EQ THEN
STAC
QED

Theorem L23EQ_IMPLIES_INVARIANT_UPDATE_BD_L2_EQ_LEMMA:
!device_characteristics memory device1 device2.
  L23EQ device_characteristics memory device1 device2
  ==>
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device2 =
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device1
Proof
INTRO_TAC THEN
ITAC L23EQ_IMPLIES_INTERNAL_STATE_EQ_LEMMA THEN
IRTAC L23EQ_IMPLIES_BDS_TO_UPDATE_EQ_LEMMA THEN
EQ_TAC THEN
 INTRO_TAC THEN
 ETAC INVARIANT_UPDATE_BD_L2 THEN
 INTRO_TAC THEN
 PTAC stateTheory.BDS_TO_UPDATE_EQ THEN
 AITAC THEN
 AIRTAC THEN
 STAC
QED

Theorem L23EQ_IMPLIES_BDS_TO_PROCESS_EQ_LEMMA:
!device_characteristics memory device1 device2.
  L23EQ device_characteristics memory device1 device2
  ==>
  BDS_TO_PROCESS_EQ device_characteristics device1 device2
Proof
INTRO_TAC THEN
PTAC L23EQ THEN
STAC
QED

Theorem L23EQ_IMPLIES_INVARIANT_TRANSFER_DATA_L2_EQ_LEMMA:
!device_characteristics memory device1 device2.
  L23EQ device_characteristics memory device1 device2
  ==>
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device2 =
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device1
Proof
INTRO_TAC THEN
ITAC L23EQ_IMPLIES_INTERNAL_STATE_EQ_LEMMA THEN
IRTAC L23EQ_IMPLIES_BDS_TO_PROCESS_EQ_LEMMA THEN
EQ_TAC THEN
 INTRO_TAC THEN
 ETAC INVARIANT_TRANSFER_DATA_L2 THEN
 INTRO_TAC THEN
 PTAC stateTheory.BDS_TO_PROCESS_EQ THEN
 AITAC THEN
 AIRTAC THEN
 STAC
QED

Theorem L23EQ_IMPLIES_BDS_TO_WRITE_BACK_EQ_LEMMA:
!device_characteristics memory device1 device2.
  L23EQ device_characteristics memory device1 device2
  ==>
  BDS_TO_WRITE_BACK_EQ device_characteristics device1 device2
Proof
INTRO_TAC THEN
PTAC L23EQ THEN
STAC
QED

Theorem L23EQ_IMPLIES_INVARIANT_WRITE_BACK_BD_L2_EQ_LEMMA:
!device_characteristics memory device1 device2.
  L23EQ device_characteristics memory device1 device2
  ==>
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device2 =
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device1
Proof
INTRO_TAC THEN
IRTAC L23EQ_IMPLIES_BDS_TO_WRITE_BACK_EQ_LEMMA THEN
EQ_TAC THEN
 INTRO_TAC THEN
 ETAC INVARIANT_WRITE_BACK_BD_L2 THEN
 INTRO_TAC THEN
 PTAC stateTheory.BDS_TO_WRITE_BACK_EQ THEN
 AITAC THEN
 AIRTAC THEN
 STAC
QED

Theorem L23EQ_IMPLIES_INVARIANT_SCRATCHPAD_R_L2_EQ_LEMMA:
!device_characteristics memory device1 device2.
  L23EQ device_characteristics memory device1 device2
  ==>
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device2 =
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device1
Proof
INTRO_TAC THEN
IRTAC L23EQ_IMPLIES_INTERNAL_STATE_EQ_LEMMA THEN
EQ_TAC THEN
 INTRO_TAC THEN
 ETAC INVARIANT_SCRATCHPAD_R_L2 THEN
 LRTAC THEN
 STAC
QED

Theorem L23EQ_IMPLIES_INVARIANT_SCRATCHPAD_W_L2_EQ_LEMMA:
!device_characteristics memory device1 device2.
  L23EQ device_characteristics memory device1 device2
  ==>
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device2 =
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device1
Proof
INTRO_TAC THEN
IRTAC L23EQ_IMPLIES_INTERNAL_STATE_EQ_LEMMA THEN
EQ_TAC THEN
 INTRO_TAC THEN
 ETAC INVARIANT_SCRATCHPAD_W_L2 THEN
 LRTAC THEN
 STAC
QED

Theorem L23EQ_IMPLIES_INVARIANT_L2_EQ_LEMMA:
!device_characteristics memory device1 device2.
  L23EQ device_characteristics memory device1 device2
  ==>
  (DEFINED_CHANNELS device_characteristics device2 /\
   INVARIANT_FETCH_BD_L3 device_characteristics memory device2 /\
   INVARIANT_UPDATE_BD_L2 device_characteristics memory device2 /\
   INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device2 /\
   INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device2 /\
   INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device2 /\
   INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device2) =
  INVARIANT_L2 device_characteristics memory device1
Proof
INTRO_TAC THEN
ETAC INVARIANT_L2 THEN
ITAC L23EQ_IMPLIES_DEFINED_CHANNELS_EQ_LEMMA THEN
ITAC L23EQ_IMPLIES_INVARIANT_FETCH_BD_L3_EQ_L2_LEMMA THEN
ITAC L23EQ_IMPLIES_INVARIANT_UPDATE_BD_L2_EQ_LEMMA THEN
ITAC L23EQ_IMPLIES_INVARIANT_TRANSFER_DATA_L2_EQ_LEMMA THEN
ITAC L23EQ_IMPLIES_INVARIANT_WRITE_BACK_BD_L2_EQ_LEMMA THEN
ITAC L23EQ_IMPLIES_INVARIANT_SCRATCHPAD_R_L2_EQ_LEMMA THEN
ITAC L23EQ_IMPLIES_INVARIANT_SCRATCHPAD_W_L2_EQ_LEMMA THEN
STAC
QED

Theorem L23EQ_INVARIANT_L3_IMPLIES_INVARIANT_L2_LEMMA:
!device_characteristics memory device1 device2.
  L23EQ device_characteristics memory device1 device2 /\
  INVARIANT_L3 device_characteristics memory device2
  ==>
  INVARIANT_L2 device_characteristics memory device1
Proof
INTRO_TAC THEN
ETAC INVARIANT_L2 THEN
IRTAC invariant_l3_lemmasTheory.INVARIANT_L3_IMPLIES_INVARIANT_L2_LEMMA THEN
ITAC L23EQ_IMPLIES_DEFINED_CHANNELS_EQ_LEMMA THEN
ITAC L23EQ_IMPLIES_INVARIANT_FETCH_BD_L3_EQ_L2_LEMMA THEN
ITAC L23EQ_IMPLIES_INVARIANT_UPDATE_BD_L2_EQ_LEMMA THEN
ITAC L23EQ_IMPLIES_INVARIANT_TRANSFER_DATA_L2_EQ_LEMMA THEN
ITAC L23EQ_IMPLIES_INVARIANT_WRITE_BACK_BD_L2_EQ_LEMMA THEN
ITAC L23EQ_IMPLIES_INVARIANT_SCRATCHPAD_R_L2_EQ_LEMMA THEN
ITAC L23EQ_IMPLIES_INVARIANT_SCRATCHPAD_W_L2_EQ_LEMMA THEN
ALL_LRTAC THEN
STAC
QED

Theorem L23EQ_INVARIANT_L3_IMPLIES_INVARIANT_L1_LEMMA:
!device_characteristics memory device1 device2.
  L23EQ device_characteristics memory device1 device2 /\
  INVARIANT_L3 device_characteristics memory device2
  ==>
  INVARIANT_L1 device_characteristics memory device1
Proof
INTRO_TAC THEN
ETAC INVARIANT_L3 THEN
IRTAC L23EQ_IMPLIES_INVARIANT_L1_EQ_LEMMA THEN
RLTAC THEN
ETAC INVARIANT_L1 THEN
STAC
QED

val _ = export_theory();

