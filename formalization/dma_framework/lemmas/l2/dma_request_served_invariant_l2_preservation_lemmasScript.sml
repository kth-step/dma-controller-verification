open HolKernel Parse boolLib bossLib helper_tactics;
open invariant_l2Theory;

val _ = new_theory "dma_request_served_invariant_l2_preservation_lemmas";

Theorem DMA_REQUEST_SERVED_L2_PRESERVES_DEFINED_CHANNELS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 serviced_request.
  device2 = dma_request_served_l2 device_characteristics device1 serviced_request /\
  DEFINED_CHANNELS device_characteristics device1
  ==>
  DEFINED_CHANNELS device_characteristics device2
Proof
INTRO_TAC THEN
PTAC l2Theory.dma_request_served_l2 THEN
ETAC stateTheory.DEFINED_CHANNELS THEN
ETAC stateTheory.VALID_CHANNELS THEN
INTRO_TAC THEN
ITAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_IS_SOME_LEMMA THEN
AIRTAC THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_L2_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory serviced_request.
  device2 = dma_request_served_l2 device_characteristics device1 serviced_request /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_FETCH_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC l2Theory.dma_request_served_l2 THEN
ITAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN
ETAC INVARIANT_FETCH_BD_L2 THEN
RW_HYPS_TAC stateTheory.schannel THEN
REWRITE_TAC [stateTheory.schannel] THEN
LRTAC THEN
INTRO_TAC THEN
AITAC THEN
IRTAC internal_operation_lemmasTheory.APPEND_REPLY_REMOVED_REQUEST_CHANNEL_PRESERVES_QUEUE_LEMMA THEN
RLTAC THEN
AIRTAC THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_L2_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory serviced_request.
  device2 = dma_request_served_l2 device_characteristics device1 serviced_request /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC l2Theory.dma_request_served_l2 THEN
ITAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN
ETAC INVARIANT_UPDATE_BD_L2 THEN
RW_HYPS_TAC stateTheory.schannel THEN
REWRITE_TAC [stateTheory.schannel] THEN
LRTAC THEN
INTRO_TAC THEN
AITAC THEN
IRTAC internal_operation_lemmasTheory.APPEND_REPLY_REMOVED_REQUEST_CHANNEL_PRESERVES_QUEUE_LEMMA THEN
RLTAC THEN
AIRTAC THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_L2_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory serviced_request.
  device2 = dma_request_served_l2 device_characteristics device1 serviced_request /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device1
  ==>
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC l2Theory.dma_request_served_l2 THEN
ITAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN
ETAC INVARIANT_TRANSFER_DATA_L2 THEN
RW_HYPS_TAC stateTheory.schannel THEN
REWRITE_TAC [stateTheory.schannel] THEN
LRTAC THEN
INTRO_TAC THEN
AITAC THEN
IRTAC internal_operation_lemmasTheory.APPEND_REPLY_REMOVED_REQUEST_CHANNEL_PRESERVES_QUEUE_LEMMA THEN
RLTAC THEN
AIRTAC THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_L2_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory serviced_request.
  device2 = dma_request_served_l2 device_characteristics device1 serviced_request /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC l2Theory.dma_request_served_l2 THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
ETAC INVARIANT_WRITE_BACK_BD_L2 THEN
RW_HYPS_TAC stateTheory.schannel THEN
REWRITE_TAC [stateTheory.schannel] THEN
INTRO_TAC THEN
AITAC THEN
IRTAC internal_operation_lemmasTheory.APPEND_REPLY_REMOVED_REQUEST_CHANNEL_PRESERVES_QUEUE_LEMMA THEN
RLTAC THEN
AIRTAC THEN
STAC
QED







Theorem DMA_REQUEST_SERVED_L2_NOT_ADDING_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA:
!device_characteristics device1 device2 serviced_request.
  device2 = dma_request_served_l2 device_characteristics device1 serviced_request
  ==>
  LIST1_IN_LIST2 device2.dma_state.pending_register_related_memory_requests device1.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
PTAC l2Theory.dma_request_served_l2 THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_NOT_ADDING_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_L2_PRESERVES_INTERNAL_STATE_LEMMA:
!device_characteristics device1 device2 serviced_request.
  device2 = dma_request_served_l2 device_characteristics device1 serviced_request
  ==>
  device2.dma_state.internal_state = device1.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC l2Theory.dma_request_served_l2 THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_L2_PRESERVES_SCRATCHPAD_R_L2_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory serviced_request.
  device2 = dma_request_served_l2 device_characteristics device1 serviced_request /\
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device1
  ==>
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ITAC DMA_REQUEST_SERVED_L2_NOT_ADDING_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA THEN
IRTAC DMA_REQUEST_SERVED_L2_PRESERVES_INTERNAL_STATE_LEMMA THEN
IRTAC internal_operation_lemmasTheory.INTERNAL_STATE_EQ_IMPLIES_SCRATCHPAD_ADDRESSES_EQ_LEMMA THEN
IRTAC invariant_l2_lemmasTheory.SCRATCHPAD_ADDRESSES_EQ_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_L2_PRESERVES_SCRATCHPAD_W_L2_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory serviced_request.
  device2 = dma_request_served_l2 device_characteristics device1 serviced_request /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device1
  ==>
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ITAC DMA_REQUEST_SERVED_L2_NOT_ADDING_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA THEN
IRTAC DMA_REQUEST_SERVED_L2_PRESERVES_INTERNAL_STATE_LEMMA THEN
IRTAC internal_operation_lemmasTheory.INTERNAL_STATE_EQ_IMPLIES_SCRATCHPAD_ADDRESSES_EQ_LEMMA THEN
IRTAC invariant_l2_lemmasTheory.SCRATCHPAD_ADDRESSES_EQ_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_L2_PRESERVES_INVARIANT_L2_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory serviced_request.
  device2 = dma_request_served_l2 device_characteristics device1 serviced_request /\
  INVARIANT_L2 device_characteristics memory device1
  ==>
  INVARIANT_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_L2 THEN
ITAC DMA_REQUEST_SERVED_L2_PRESERVES_DEFINED_CHANNELS_LEMMA THEN
ITAC DMA_REQUEST_SERVED_L2_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA THEN
ITAC DMA_REQUEST_SERVED_L2_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA THEN
ITAC DMA_REQUEST_SERVED_L2_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA THEN
ITAC DMA_REQUEST_SERVED_L2_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA THEN
ITAC DMA_REQUEST_SERVED_L2_PRESERVES_SCRATCHPAD_R_L2_LEMMA THEN
ITAC DMA_REQUEST_SERVED_L2_PRESERVES_SCRATCHPAD_W_L2_LEMMA THEN
STAC
QED

val _ = export_theory();

