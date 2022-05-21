open HolKernel Parse boolLib bossLib helper_tactics;
open L23EQTheory l2Theory l3Theory proof_obligationsTheory invariant_l3Theory;

val _ = new_theory "dma_request_served_l2_l3";

Theorem DMA_REQUEST_SERVED_L3_PRESERVES_FUNCTION_STATE_LEMMA:
!device_characteristics device1 device2 serviced_request.
  device2 = dma_request_served_l3 device_characteristics device1 serviced_request
  ==>
  device2.function_state = device1.function_state
Proof
INTRO_TAC THEN
PTAC dma_request_served_l3 THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_FUNCTION_STATES_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_L2_PRESERVES_FUNCTION_STATE_LEMMA:
!device_characteristics device1 device2 serviced_request.
  device2 = dma_request_served_l2 device_characteristics device1 serviced_request
  ==>
  device2.function_state = device1.function_state
Proof
INTRO_TAC THEN
PTAC dma_request_served_l2 THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_FUNCTION_STATES_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_L3_PRESERVES_INTERNAL_STATE_LEMMA:
!device_characteristics device1 device2 serviced_request.
  device2 = dma_request_served_l3 device_characteristics device1 serviced_request
  ==>
  device2.dma_state.internal_state = device1.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC dma_request_served_l3 THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_L2_PRESERVES_INTERNAL_STATE_LEMMA:
!device_characteristics device1 device2 serviced_request.
  device2 = dma_request_served_l2 device_characteristics device1 serviced_request
  ==>
  device2.dma_state.internal_state = device1.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC dma_request_served_l2 THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN
STAC
QED















Theorem DMA_REQUEST_SERVED_PRESERVES_FUNCTION_STATE_LEMMA:
!device_characteristics device21 device31 device22 device32 serviced_request.
  device22 = dma_request_served device_characteristics device21 serviced_request /\
  device32 = dma_request_served device_characteristics device31 serviced_request /\
  FUNCTION_STATES_EQ device21 device31
  ==>
  FUNCTION_STATES_EQ device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.FUNCTION_STATES_EQ THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_FUNCTION_STATES_LEMMA THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_FUNCTION_STATES_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATE_LEMMA:
!device_characteristics device21 device31 device22 device32 serviced_request.
  device22 = dma_request_served device_characteristics device21 serviced_request /\
  device32 = dma_request_served device_characteristics device31 serviced_request /\
  INTERNAL_STATES_EQ device21 device31
  ==>
  INTERNAL_STATES_EQ device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.INTERNAL_STATES_EQ THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_PRESERVES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device11 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device12 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory serviced_request.
  device12 = dma_request_served device_characteristics device11 serviced_request /\
  device22 = dma_request_served device_characteristics device21 serviced_request /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device11 device21
  ==>
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device12 device22
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
AITAC THEN
ITAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
AITAC THEN
ITAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
AITAC THEN
ETAC (GSYM stateTheory.schannel) THEN
IRTAC internal_operation_lemmasTheory.APPENDED_REPLY_REMOVED_REQUEST_CHANNEL_TRANSFERS_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_PRESERVES_BDS_TO_UPDATE_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device11 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device12 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 serviced_request.
  device12 = dma_request_served device_characteristics device11 serviced_request /\
  device22 = dma_request_served device_characteristics device21 serviced_request /\
  BDS_TO_UPDATE_EQ device_characteristics device11 device21
  ==>
  BDS_TO_UPDATE_EQ device_characteristics device12 device22
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_UPDATE_EQ THEN
INTRO_TAC THEN
AITAC THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
AITAC THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
AITAC THEN
ETAC (GSYM stateTheory.schannel) THEN
IRTAC internal_operation_lemmasTheory.APPENDED_REPLY_REMOVED_REQUEST_CHANNEL_TRANSFERS_BDS_TO_UPDATE_EQ_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_PRESERVES_BDS_TO_PROCESS_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device11 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device12 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 serviced_request.
  device12 = dma_request_served device_characteristics device11 serviced_request /\
  device22 = dma_request_served device_characteristics device21 serviced_request /\
  BDS_TO_PROCESS_EQ device_characteristics device11 device21
  ==>
  BDS_TO_PROCESS_EQ device_characteristics device12 device22
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_PROCESS_EQ THEN
INTRO_TAC THEN
AITAC THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
AITAC THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
AITAC THEN
ETAC (GSYM stateTheory.schannel) THEN
IRTAC internal_operation_lemmasTheory.APPENDED_REPLY_REMOVED_REQUEST_CHANNEL_TRANSFERS_BDS_TO_PROCESS_EQ_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_PRESERVES_BDS_TO_WRITE_BACK_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device11 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device12 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 serviced_request.
  device12 = dma_request_served device_characteristics device11 serviced_request /\
  device22 = dma_request_served device_characteristics device21 serviced_request /\
  BDS_TO_WRITE_BACK_EQ device_characteristics device11 device21
  ==>
  BDS_TO_WRITE_BACK_EQ device_characteristics device12 device22
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_WRITE_BACK_EQ THEN
INTRO_TAC THEN
AITAC THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
AITAC THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
AITAC THEN
ETAC (GSYM stateTheory.schannel) THEN
IRTAC internal_operation_lemmasTheory.APPENDED_REPLY_REMOVED_REQUEST_CHANNEL_TRANSFERS_BDS_TO_WRITE_BACK_EQ_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_PRESERVES_DEFINED_CHANNELS_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device11 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device12 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 serviced_request.
  device12 = dma_request_served device_characteristics device11 serviced_request /\
  device22 = dma_request_served device_characteristics device21 serviced_request /\
  DEFINED_CHANNELS_EQ device_characteristics device11 device21
  ==>
  DEFINED_CHANNELS_EQ device_characteristics device12 device22
Proof
INTRO_TAC THEN
ETAC stateTheory.DEFINED_CHANNELS_EQ THEN
GEN_TAC THEN
EQ_TAC THENL
[
 INTRO_TAC THEN
 Cases_on ‘VALID_CHANNEL_ID device_characteristics channel_id’ THENL
 [
  WEAKEN_TAC is_eq THEN
  IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_IS_SOME_LEMMA THEN
  AITAC THEN
  STAC
  ,
  IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_CHANNELS_SOME_PRESERVED_LEMMA THEN
  AITAC THEN
  IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_CHANNELS_SOME_PRESERVED_LEMMA THEN
  AIRTAC THEN
  LRTAC THEN
  QRLTAC THEN
  STAC
 ]
 ,
 INTRO_TAC THEN
 Cases_on ‘VALID_CHANNEL_ID device_characteristics channel_id’ THENL
 [
  IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_IS_SOME_LEMMA THEN
  AIRTAC THEN
  STAC
  ,
  IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_CHANNELS_SOME_PRESERVED_LEMMA THEN
  AITAC THEN
  LRTAC THEN
  IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_CHANNELS_SOME_PRESERVED_LEMMA THEN
  AIRTAC THEN
  LRTAC THEN
  STAC
 ] 
]
QED

Theorem DEVICE_SIM_L2_L3_DMA_REQUEST_SERVED_PRESERVES_L23EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device31 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device32 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory replied_bytes request.
  device22 = dma_request_served_l2 device_characteristics device21 (replied_bytes, request) /\
  device32 = dma_request_served_l3 device_characteristics device31 (replied_bytes, request) /\
  MEM request (dma_pending_requests_l2 device_characteristics device21) /\
  L23EQ device_characteristics memory device21 device31
  ==>
  MEM request (dma_pending_requests_l3 device_characteristics device31) /\
  L23EQ device_characteristics memory device22 device32
Proof
REWRITE_TAC [L23EQ, dma_request_served_l2, dma_request_served_l3, dma_pending_requests_l2, dma_pending_requests_l3] THEN
INTRO_TAC THEN
CONJS_TAC THENL
[
 IRTAC dma_pending_requests_lemmasTheory.MEMORY_REQUESTS_REPLIES_EQ_IMPLIES_DMA_PENDING_REQUESTS_EQ_LEMMA THEN STAC
 ,
 FIRTAC DMA_REQUEST_SERVED_PRESERVES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA THEN STAC
 ,
 FIRTAC DMA_REQUEST_SERVED_PRESERVES_BDS_TO_UPDATE_EQ_LEMMA THEN STAC
 ,
 FIRTAC DMA_REQUEST_SERVED_PRESERVES_BDS_TO_PROCESS_EQ_LEMMA THEN STAC
 ,
 FIRTAC DMA_REQUEST_SERVED_PRESERVES_BDS_TO_WRITE_BACK_EQ_LEMMA THEN STAC
 ,
 FIRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_MEMORY_REQUESTS_REPLIES_EQ_LEMMA THEN STAC
 ,
 FIRTAC DMA_REQUEST_SERVED_PRESERVES_FUNCTION_STATE_LEMMA THEN STAC
 ,
 FIRTAC DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATE_LEMMA THEN STAC
 ,
 FIRTAC DMA_REQUEST_SERVED_PRESERVES_DEFINED_CHANNELS_EQ_LEMMA THEN STAC
]
QED

Theorem DEVICE_SIM_L3_L2_DMA_REQUEST_SERVED_PRESERVES_L23EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device31 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device32 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory replied_bytes request.
  device22 = dma_request_served_l2 device_characteristics device21 (replied_bytes, request) /\
  device32 = dma_request_served_l3 device_characteristics device31 (replied_bytes, request) /\
  MEM request (dma_pending_requests_l3 device_characteristics device31) /\
  L23EQ device_characteristics memory device21 device31
  ==>
  MEM request (dma_pending_requests_l2 device_characteristics device21) /\
  L23EQ device_characteristics memory device22 device32
Proof
REWRITE_TAC [L23EQ, dma_request_served_l2, dma_request_served_l3, dma_pending_requests_l2, dma_pending_requests_l3] THEN
INTRO_TAC THEN
REPEAT CONJ_TAC THENL
[
 IRTAC dma_pending_requests_lemmasTheory.MEMORY_REQUESTS_REPLIES_EQ_IMPLIES_DMA_PENDING_REQUESTS_EQ_LEMMA THEN STAC
 ,
 FIRTAC DMA_REQUEST_SERVED_PRESERVES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA THEN STAC
 ,
 FIRTAC DMA_REQUEST_SERVED_PRESERVES_BDS_TO_UPDATE_EQ_LEMMA THEN STAC
 ,
 FIRTAC DMA_REQUEST_SERVED_PRESERVES_BDS_TO_PROCESS_EQ_LEMMA THEN STAC
 ,
 FIRTAC DMA_REQUEST_SERVED_PRESERVES_BDS_TO_WRITE_BACK_EQ_LEMMA THEN STAC
 ,
 FIRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_MEMORY_REQUESTS_REPLIES_EQ_LEMMA THEN STAC
 ,
 FIRTAC DMA_REQUEST_SERVED_PRESERVES_FUNCTION_STATE_LEMMA THEN STAC
 ,
 FIRTAC DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATE_LEMMA THEN STAC
 ,
 FIRTAC DMA_REQUEST_SERVED_PRESERVES_DEFINED_CHANNELS_EQ_LEMMA THEN STAC
]
QED

Theorem DEVICE_SIM_L2_L3_DMA_READ_REQUEST_SERVED_LEMMA:
!device_characteristics memory device21 device22 device31 addresses tag.
  MEM (request_read addresses tag) (dma_pending_requests_l2 device_characteristics device21) /\
  device22 = dma_request_served_l2 device_characteristics device21 (MAP memory addresses, request_read addresses tag) /\
  L23EQ device_characteristics memory device21 device31
  ==>
  ?device32.
    MEM (request_read addresses tag) (dma_pending_requests_l3 device_characteristics device31) /\
    device32 = dma_request_served_l3 device_characteristics device31 (MAP memory addresses, request_read addresses tag) /\
    L23EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
IRTAC DEVICE_SIM_L2_L3_DMA_REQUEST_SERVED_PRESERVES_L23EQ_LEMMA THEN
PAXTAC THEN
STAC
QED

Theorem DEVICE_SIM_L3_L2_DMA_READ_REQUEST_SERVED_LEMMA:
!device_characteristics memory device21 device31 device32 addresses tag.
  MEM (request_read addresses tag) (dma_pending_requests_l3 device_characteristics device31) /\
  device32 = dma_request_served_l3 device_characteristics device31 (MAP memory addresses, request_read addresses tag) /\
  L23EQ device_characteristics memory device21 device31
  ==>
  ?device22.
    MEM (request_read addresses tag) (dma_pending_requests_l2 device_characteristics device21) /\
    device22 = dma_request_served_l2 device_characteristics device21 (MAP memory addresses, request_read addresses tag) /\
    L23EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
FIRTAC DEVICE_SIM_L3_L2_DMA_REQUEST_SERVED_PRESERVES_L23EQ_LEMMA THEN
PAXTAC THEN
STAC
QED

Theorem MEMORY_WRITE_PRESERVING_BDS_TO_FETCH_PRESERVES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics memory1 memory2 device1 device2 device3 address_bytes tag.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device3 /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device3 /\
  device3.dma_state.internal_state = device2.dma_state.internal_state /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l3 device_characteristics device3) /\
  memory2 = update_memory memory1 address_bytes /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory1 device1 device2
  ==>
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory2 device1 device2
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
AITAC THEN
LRTAC THEN
ITAC invariant_l3_lemmasTheory.NO_MEMORY_WRITES_BDS_TO_FETCH_PRESERVES_BDS_TO_FETCH_LEMMA THEN
AIRTAC THEN
STAC
QED

Theorem L3_MEMORY_WRITE_PRESERVING_BDS_TO_FETCH_PRESERVES_L23EQ_LEMMA:
!device_characteristics memory1 memory2 device1 device2 device3 address_bytes tag.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device3 /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device3 /\
  device3.dma_state.internal_state = device2.dma_state.internal_state /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l3 device_characteristics device3) /\
  memory2 = update_memory memory1 address_bytes /\
  L23EQ device_characteristics memory1 device1 device2
  ==>
  L23EQ device_characteristics memory2 device1 device2
Proof
INTRO_TAC THEN
ETAC L23EQ THEN
IRTAC MEMORY_WRITE_PRESERVING_BDS_TO_FETCH_PRESERVES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA THEN
STAC
QED

Theorem DEVICE_SIM_L2_L3_DMA_WRITE_REQUEST_SERVED_LEMMA_LEMMA:
!device_characteristics device21 device22 device31 address_bytes tag memory1 memory2.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics /\
  INVARIANT_L3 device_characteristics memory1 device31 /\
  memory2 = update_memory memory1 address_bytes /\
  device22 = dma_request_served_l2 device_characteristics device21 ([], request_write address_bytes tag) /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l2 device_characteristics device21) /\
  L23EQ device_characteristics memory1 device21 device31
  ==>
  ?device32.
    device32 = dma_request_served_l3 device_characteristics device31 ([], request_write address_bytes tag) /\
    MEM (request_write address_bytes tag) (dma_pending_requests_l3 device_characteristics device31) /\
    L23EQ device_characteristics memory2 device22 device32
Proof
INTRO_TAC THEN
ETAC invariant_l3Theory.INVARIANT_L3 THEN
FIRTAC DEVICE_SIM_L2_L3_DMA_REQUEST_SERVED_PRESERVES_L23EQ_LEMMA THEN
PAXTAC THEN
ITAC DMA_REQUEST_SERVED_L3_PRESERVES_INTERNAL_STATE_LEMMA THEN
ITAC L3_MEMORY_WRITE_PRESERVING_BDS_TO_FETCH_PRESERVES_L23EQ_LEMMA THEN
STAC
QED

Theorem L23EQ_IMPLIES_DMA_PENDING_REQUESTS_L2_L3_EQ_LEMMA:
!device_characteristics memory device21 device31.
  L23EQ device_characteristics memory device21 device31
  ==>
  (dma_pending_requests_l2 device_characteristics device21) = (dma_pending_requests_l3 device_characteristics device31)
Proof
INTRO_TAC THEN
ETAC L23EQ THEN
IRTAC dma_pending_requests_lemmasTheory.MEMORY_REQUESTS_REPLIES_EQ_IMPLIES_DMA_PENDING_REQUESTS_EQ_LEMMA THEN
ASM_REWRITE_TAC [l2Theory.dma_pending_requests_l2, l3Theory.dma_pending_requests_l3]
QED

Theorem DEVICE_SIM_L3_L2_DMA_WRITE_REQUEST_SERVED_LEMMA_LEMMA:
!device_characteristics device21 device31 device32 address_bytes tag memory1 memory2.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics /\
  INVARIANT_L3 device_characteristics memory1 device31 /\
  memory2 = update_memory memory1 address_bytes /\
  device32 = dma_request_served_l3 device_characteristics device31 ([], request_write address_bytes tag) /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l3 device_characteristics device31) /\
  L23EQ device_characteristics memory1 device21 device31
  ==>
  ?device22.
    device22 = dma_request_served_l2 device_characteristics device21 ([], request_write address_bytes tag) /\
    MEM (request_write address_bytes tag) (dma_pending_requests_l2 device_characteristics device21) /\
    L23EQ device_characteristics memory2 device22 device32
Proof
INTRO_TAC THEN
ETAC invariant_l3Theory.INVARIANT_L3 THEN
ITAC L23EQ_IMPLIES_DMA_PENDING_REQUESTS_L2_L3_EQ_LEMMA THEN
ITAC DMA_REQUEST_SERVED_L3_PRESERVES_INTERNAL_STATE_LEMMA THEN
FIRTAC DEVICE_SIM_L3_L2_DMA_REQUEST_SERVED_PRESERVES_L23EQ_LEMMA THEN
PAXTAC THEN
FITAC L3_MEMORY_WRITE_PRESERVING_BDS_TO_FETCH_PRESERVES_L23EQ_LEMMA THEN
STAC
QED

val _ = export_theory();

