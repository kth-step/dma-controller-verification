open HolKernel Parse boolLib bossLib helper_tactics;
open l4Theory invariant_l4Theory invariant_l4_lemmasTheory;

val _ = new_theory "dma_request_served_invariant_concrete_l4_preservation_lemmas";

Theorem DMA_REQUEST_SERVED_L4_PRESERVES_CHANNEL_QUEUES_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) addresses_request channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  device2 = dma_request_served_l4 device_characteristics device1 addresses_request
  ==>
  (schannel device2 channel_id).queue = (schannel device1 channel_id).queue
Proof
INTRO_TAC THEN
ETAC dma_request_served_l4 THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_PIPELINES_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_L4_PRESERVES_INTERNAL_STATE_LEMMA:
!device_characteristics device1 device2 addresses_request.
  device2 = dma_request_served_l4 device_characteristics device1 addresses_request
  ==>
  device2.dma_state.internal_state = device1.dma_state.internal_state
Proof
INTRO_TAC THEN
ETAC dma_request_served_l4 THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_L4_IMPLIES_BDS_TO_FETCH_NOT_EXPANDED_LEMMA:
!device_characteristics device1 device2 addresses_request.
  device2 = dma_request_served_l4 device_characteristics device1 addresses_request
  ==>
  !memory.
    BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
GEN_TAC THEN
ETAC BDS_TO_FETCH_NOT_EXPANDED THEN
IRTAC DMA_REQUEST_SERVED_L4_PRESERVES_INTERNAL_STATE_LEMMA THEN
INTRO_TAC THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_L4_IMPLIES_BDS_TO_UPDATE_NOT_EXPANDED_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 addresses_request.
  device2 = dma_request_served_l4 device_characteristics device1 addresses_request
  ==>
  BDS_TO_UPDATE_NOT_EXPANDED device_characteristics device1 device2
Proof
INTRO_TAC THEN
ETAC BDS_TO_UPDATE_NOT_EXPANDED THEN
ETAC BDS_TO_OPERATE_ON_NOT_EXPANDED THEN
INTRO_TAC THEN
IRTAC DMA_REQUEST_SERVED_L4_PRESERVES_CHANNEL_QUEUES_LEMMA THEN
ASM_REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
QED

Theorem DMA_REQUEST_SERVED_L4_IMPLIES_BDS_TO_PROCESS_NOT_EXPANDED_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 addresses_request.
  device2 = dma_request_served_l4 device_characteristics device1 addresses_request
  ==>
  BDS_TO_PROCESS_NOT_EXPANDED device_characteristics device1 device2
Proof
INTRO_TAC THEN
ETAC BDS_TO_PROCESS_NOT_EXPANDED THEN
ETAC BDS_TO_OPERATE_ON_NOT_EXPANDED THEN
INTRO_TAC THEN
IRTAC DMA_REQUEST_SERVED_L4_PRESERVES_CHANNEL_QUEUES_LEMMA THEN
ASM_REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
QED

Theorem DMA_REQUEST_SERVED_L4_IMPLIES_BDS_TO_WRITE_BACK_NOT_EXPANDED_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 addresses_request.
  device2 = dma_request_served_l4 device_characteristics device1 addresses_request
  ==>
  BDS_TO_WRITE_BACK_NOT_EXPANDED device_characteristics device1 device2
Proof
INTRO_TAC THEN
ETAC BDS_TO_WRITE_BACK_NOT_EXPANDED THEN
ETAC BDS_TO_OPERATE_ON_NOT_EXPANDED THEN
INTRO_TAC THEN
IRTAC DMA_REQUEST_SERVED_L4_PRESERVES_CHANNEL_QUEUES_LEMMA THEN
ASM_REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
QED

Theorem DMA_REQUEST_SERVED_L4_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA:
!device_characteristics device1 device2 addresses_request.
  device2 = dma_request_served_l4 device_characteristics device1 addresses_request
  ==>
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
IRTAC DMA_REQUEST_SERVED_L4_PRESERVES_INTERNAL_STATE_LEMMA THEN
ETAC stateTheory.BD_TRANSFER_RAS_WAS_EQ THEN
STAC
QED


Theorem DMA_REQUEST_SERVED_L4_READ_REQUEST_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory addresses_request.
  device2 = dma_request_served_l4 device_characteristics device1 addresses_request /\
  INVARIANT_CONCRETE_L4 device_characteristics memory device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_CONCRETE_L4 THEN
ITAC DMA_REQUEST_SERVED_L4_IMPLIES_BDS_TO_FETCH_NOT_EXPANDED_LEMMA THEN
ITAC DMA_REQUEST_SERVED_L4_IMPLIES_BDS_TO_UPDATE_NOT_EXPANDED_LEMMA THEN
ITAC DMA_REQUEST_SERVED_L4_IMPLIES_BDS_TO_PROCESS_NOT_EXPANDED_LEMMA THEN
ITAC DMA_REQUEST_SERVED_L4_IMPLIES_BDS_TO_WRITE_BACK_NOT_EXPANDED_LEMMA THEN
IRTAC DMA_REQUEST_SERVED_L4_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4_LEMMA THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4_LEMMA THEN
ITAC BDS_TO_UPDATE_NOT_EXPANDED_PRESERVES_INVARIANT_UPDATE_BD_BD_WRITE_L4_LEMMA THEN
ITAC BDS_TO_PROCESS_NOT_EXPANDED_PRESERVES_INVARIANT_PROCESS_BD_BD_WRITE_L4_LEMMA THEN
ITAC BDS_TO_WRITE_BACK_NOT_EXPANDED_PRESERVES_INVARIANT_WRITE_BACK_BD_BD_WRITE_L4_LEMMA THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_INVARIANT_FETCH_BD_DMA_WRITE_L4_LEMMA THEN
ITAC BDS_TO_UPDATE_NOT_EXPANDED_PRESERVES_INVARIANT_UPDATE_BD_DMA_WRITE_L4_LEMMA THEN
ITAC BDS_TO_PROCESS_NOT_EXPANDED_PRESERVES_INVARIANT_PROCESS_BD_DMA_WRITE_L4_LEMMA THEN
STAC
QED







(*******************************************************************************)

Theorem MEM_DMA_PENDING_REQUESTS_IMPLIES_CHANNEL_REQUESTS_OR_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA:
!device_characteristics device request.
  MEM request (dma_pending_requests device_characteristics device)
  ==>
  MEM request (channel_requests device_characteristics device) \/
  MEM request device.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
ETAC operationsTheory.dma_pending_requests THEN
ETAC listTheory.MEM_APPEND THEN
STAC
QED

Theorem DMA_PENDING_REQUESTS_L4_NO_MEMORY_WRITES_BDS_TO_FETCH_PRESERVES_EXTERNAL_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id memory1 memory2 device address_bytes tag.
  PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics /\
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l4 device_characteristics device) /\
  memory2 = update_memory memory1 address_bytes
  ==>
  (cverification device_characteristics channel_id).bds_to_fetch memory2 device.dma_state.internal_state =
  (cverification device_characteristics channel_id).bds_to_fetch memory1 device.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC dma_pending_requests_l4 THEN 
PTAC operationsTheory.dma_pending_requests THEN
ETAC listTheory.MEM_APPEND THEN
SPLIT_ASM_DISJS_TAC THENL
[
 PTAC invariant_l3Theory.NO_MEMORY_WRITES_TO_BDS THEN
 IRTAC internal_operation_lemmasTheory.REQUEST_WAS_IN_REQUESTS_WAS_LEMMA THEN
 AIRTAC THEN
 PTAC bd_queuesTheory.CONSISTENT_DMA_WRITE THEN
 AIRTAC THEN
 ITAC invariant_l3_lemmasTheory.MEMORY_WRITE_REQUEST_NOT_BD_TO_FETCH_PRESERVES_BDS_LEMMA THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE THEN
 AIRTAC THEN
 STAC
 ,
 PTAC invariant_l3Theory.MEMORY_WRITES_PRESERVES_BDS_TO_FETCH THEN
 PTAC stateTheory.READ_REQUESTS THEN
 ETAC listTheory.EVERY_MEM THEN
 AIRTAC THEN
 PTAC stateTheory.READ_REQUEST THEN
 SOLVE_F_ASM_TAC
]
QED

Theorem DMA_PENDING_REQUESTS_L4_NO_MEMORY_WRITES_BDS_TO_FETCH_PRESERVES_INTERNAL_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id memory1 memory2 device address_bytes tag.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  INTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l4 device_characteristics device) /\
  memory2 = update_memory memory1 address_bytes
  ==>
  (cverification device_characteristics channel_id).bds_to_fetch memory2 device.dma_state.internal_state =
  (cverification device_characteristics channel_id).bds_to_fetch memory1 device.dma_state.internal_state
Proof
INTRO_TAC THEN
IRTAC state_lemmasTheory.NOT_EXTERNAL_BDS_IMPLIES_INTERNAL_BDS_LEMMA THEN
ETAC proof_obligationsTheory.PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY THEN
INST_IMP_ASM_GOAL_TAC THEN
STAC
QED

Theorem DMA_PENDING_REQUESTS_L4_NO_MEMORY_WRITES_BDS_TO_FETCH_IMPLIES_BDS_TO_FETCH_EQ_INTERNAL_STATE_LEMMA:
!device_characteristics memory1 memory2 device address_bytes tag.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l4 device_characteristics device) /\
  memory2 = update_memory memory1 address_bytes
  ==>
  BDS_TO_FETCH_EQ_INTERNAL_STATE device_characteristics memory1 memory2 device.dma_state.internal_state
Proof
REWRITE_TAC [invariant_l3_lemmasTheory.BDS_TO_FETCH_EQ_INTERNAL_STATE] THEN
INTRO_TAC THEN
INTRO_TAC THEN
Cases_on ‘EXTERNAL_BDS device_characteristics’ THENL
[
 IRTAC DMA_PENDING_REQUESTS_L4_NO_MEMORY_WRITES_BDS_TO_FETCH_PRESERVES_EXTERNAL_BDS_TO_FETCH_LEMMA THEN STAC
 ,
 ITAC state_lemmasTheory.NOT_EXTERNAL_BDS_IMPLIES_INTERNAL_BDS_LEMMA THEN
 IRTAC DMA_PENDING_REQUESTS_L4_NO_MEMORY_WRITES_BDS_TO_FETCH_PRESERVES_INTERNAL_BDS_TO_FETCH_LEMMA THEN
 STAC
]
QED

Theorem BDS_TO_FETCH_EQ_INTERNAL_STATE_IMPLIES_LEMMA:
!device_characteristics memory1 memory2 device.
  BDS_TO_FETCH_EQ_INTERNAL_STATE device_characteristics memory1 memory2 device.dma_state.internal_state
  ==>
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (cverification device_characteristics channel_id).bds_to_fetch memory2 device.dma_state.internal_state =
    (cverification device_characteristics channel_id).bds_to_fetch memory1 device.dma_state.internal_state
Proof
REWRITE_TAC [invariant_l3_lemmasTheory.BDS_TO_FETCH_EQ_INTERNAL_STATE]
QED

Theorem BDS_TO_UPDATE_NOT_EXPANDED_REFL_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  BDS_TO_UPDATE_NOT_EXPANDED device_characteristics device device
Proof
REWRITE_TAC [BDS_TO_UPDATE_NOT_EXPANDED, BDS_TO_OPERATE_ON_NOT_EXPANDED] THEN
INTRO_TAC THEN
ASM_REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
QED

Theorem BDS_TO_PROCESS_NOT_EXPANDED_REFL_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  BDS_TO_PROCESS_NOT_EXPANDED device_characteristics device device
Proof
REWRITE_TAC [BDS_TO_PROCESS_NOT_EXPANDED, BDS_TO_OPERATE_ON_NOT_EXPANDED] THEN
INTRO_TAC THEN
ASM_REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
QED

Theorem BDS_TO_WRITE_BACK_NOT_EXPANDED_REFL_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  BDS_TO_WRITE_BACK_NOT_EXPANDED device_characteristics device device
Proof
REWRITE_TAC [BDS_TO_WRITE_BACK_NOT_EXPANDED, BDS_TO_OPERATE_ON_NOT_EXPANDED] THEN
INTRO_TAC THEN
ASM_REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
QED

Theorem BD_TRANSFER_RAS_WAS_EQ_REFL_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 internal_state.
  BD_TRANSFER_RAS_WAS_EQ device_characteristics internal_state internal_state
Proof
REWRITE_TAC [stateTheory.BD_TRANSFER_RAS_WAS_EQ]
QED

Theorem WRITE_REQUEST_PRESERVES_INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4_LEMMA:
!device_characteristics memory1 memory2 device address_bytes tag.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l4 device_characteristics device) /\
  memory2 = update_memory memory1 address_bytes /\
  INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4 device_characteristics memory1 device
  ==>
  INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4 device_characteristics memory2 device
Proof
INTRO_TAC THEN
IRTAC DMA_PENDING_REQUESTS_L4_NO_MEMORY_WRITES_BDS_TO_FETCH_IMPLIES_BDS_TO_FETCH_EQ_INTERNAL_STATE_LEMMA THEN
ETAC INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4 THEN
INTRO_TAC THEN
ETAC invariant_l3_lemmasTheory.BDS_TO_FETCH_EQ_INTERNAL_STATE THEN
AITAC THEN
RLTAC THEN
AIRTAC THEN
STAC
QED

Theorem BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_DISJOINT_FROM_OTHER_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id memory1 memory2 internal_state bd_was.
  BDS_TO_FETCH_EQ_INTERNAL_STATE device_characteristics memory1 memory2 internal_state /\
  DISJOINT_FROM_OTHER_BDS_TO_FETCH device_characteristics channel_id memory1 internal_state bd_was
  ==>
  DISJOINT_FROM_OTHER_BDS_TO_FETCH device_characteristics channel_id memory2 internal_state bd_was
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.DISJOINT_FROM_OTHER_BDS_TO_FETCH THEN
INTRO_TAC THEN
ETAC invariant_l3_lemmasTheory.BDS_TO_FETCH_EQ_INTERNAL_STATE THEN
AITAC THEN
AIRTAC THEN
STAC
QED

Theorem WRITE_REQUEST_PRESERVES_INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4_LEMMA:
!device_characteristics memory1 memory2 device address_bytes tag.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l4 device_characteristics device) /\
  memory2 = update_memory memory1 address_bytes /\
  INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4 device_characteristics memory1 device
  ==>
  INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4 device_characteristics memory2 device
Proof
INTRO_TAC THEN
IRTAC DMA_PENDING_REQUESTS_L4_NO_MEMORY_WRITES_BDS_TO_FETCH_IMPLIES_BDS_TO_FETCH_EQ_INTERNAL_STATE_LEMMA THEN
ETAC INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4 THEN
INTRO_TAC THEN
ITAC BDS_TO_FETCH_EQ_INTERNAL_STATE_IMPLIES_LEMMA THEN
AITAC THEN
AIRTAC THEN
IRTAC BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_DISJOINT_FROM_OTHER_BDS_TO_FETCH_LEMMA THEN
STAC
QED

Theorem BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_CONSISTENT_BD_WRITE_LEMMA:
!device_characteristics memory1 memory2 internal_state bd_was.
  BDS_TO_FETCH_EQ_INTERNAL_STATE device_characteristics memory1 memory2 internal_state /\
  CONSISTENT_BD_WRITE device_characteristics memory1 internal_state bd_was
  ==>
  CONSISTENT_BD_WRITE device_characteristics memory2 internal_state bd_was
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.CONSISTENT_BD_WRITE THEN
ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
INTRO_TAC THEN
ETAC invariant_l3_lemmasTheory.BDS_TO_FETCH_EQ_INTERNAL_STATE THEN
AITAC THEN
AIRTAC THEN
STAC
QED

Theorem BDS_TO_FETCH_EQ_INTERNAL_STATE_BDS_TO_UPDATE_NOT_EXPANDED_PRESERVES_INVARIANT_UPDATE_BD_BD_WRITE_L4_LEMMA:
!device_characteristics memory1 memory2 device.
  BDS_TO_FETCH_EQ_INTERNAL_STATE device_characteristics memory1 memory2 device.dma_state.internal_state /\
  BDS_TO_UPDATE_NOT_EXPANDED device_characteristics device device /\
  INVARIANT_UPDATE_BD_BD_WRITE_L4 device_characteristics memory1 device
  ==>
  INVARIANT_UPDATE_BD_BD_WRITE_L4 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC INVARIANT_UPDATE_BD_BD_WRITE_L4 THEN
ETAC BD_WRITE THEN
INTRO_TAC THEN
AIRTAC THEN
IRTAC BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_CONSISTENT_BD_WRITE_LEMMA THEN
STAC
QED

Theorem BDS_TO_FETCH_EQ_INTERNAL_STATE_BDS_TO_PROCESS_NOT_EXPANDED_PRESERVES_INVARIANT_PROCESS_BD_BD_WRITE_L4_LEMMA:
!device_characteristics memory1 memory2 device.
  BDS_TO_FETCH_EQ_INTERNAL_STATE device_characteristics memory1 memory2 device.dma_state.internal_state /\
  BDS_TO_PROCESS_NOT_EXPANDED device_characteristics device device /\
  INVARIANT_PROCESS_BD_BD_WRITE_L4 device_characteristics memory1 device
  ==>
  INVARIANT_PROCESS_BD_BD_WRITE_L4 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC INVARIANT_PROCESS_BD_BD_WRITE_L4 THEN
ETAC BD_WRITE THEN
INTRO_TAC THEN
AIRTAC THEN
IRTAC BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_CONSISTENT_BD_WRITE_LEMMA THEN
STAC
QED

Theorem BDS_TO_FETCH_EQ_INTERNAL_STATE_BDS_TO_WRITE_BACK_NOT_EXPANDED_PRESERVES_INVARIANT_WRITE_BACK_BD_BD_WRITE_L4_LEMMA:
!device_characteristics memory1 memory2 device.
  BDS_TO_FETCH_EQ_INTERNAL_STATE device_characteristics memory1 memory2 device.dma_state.internal_state /\
  BDS_TO_WRITE_BACK_NOT_EXPANDED device_characteristics device device /\
  INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 device_characteristics memory1 device
  ==>
  INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 THEN
ETAC BD_WRITE THEN
INTRO_TAC THEN
AIRTAC THEN
IRTAC BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_CONSISTENT_BD_WRITE_LEMMA THEN
STAC
QED

Theorem BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA:
!device_characteristics memory1 memory2 internal_state bd_was.
  BDS_TO_FETCH_EQ_INTERNAL_STATE device_characteristics memory1 memory2 internal_state /\
  CONSISTENT_DMA_WRITE device_characteristics memory1 internal_state bd_was
  ==>
  CONSISTENT_DMA_WRITE device_characteristics memory2 internal_state bd_was
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.CONSISTENT_DMA_WRITE THEN
INTRO_TAC THEN
AIRTAC THEN
ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
INTRO_TAC THEN
PTAC invariant_l3_lemmasTheory.BDS_TO_FETCH_EQ_INTERNAL_STATE THEN
AITAC THEN
AIRTAC THEN
STAC
QED

Theorem BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_INVARIANT_FETCH_BD_DMA_WRITE_L4_LEMMA:
!device_characteristics memory1 memory2 device.
  BDS_TO_FETCH_EQ_INTERNAL_STATE device_characteristics memory1 memory2 device.dma_state.internal_state /\
  INVARIANT_FETCH_BD_DMA_WRITE_L4 device_characteristics memory1 device
  ==>
  INVARIANT_FETCH_BD_DMA_WRITE_L4 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC INVARIANT_FETCH_BD_DMA_WRITE_L4 THEN
INTRO_TAC THEN
ITAC BDS_TO_FETCH_EQ_INTERNAL_STATE_IMPLIES_LEMMA THEN
AITAC THEN
AIRTAC THEN
IRTAC BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA THEN
STAC
QED

Theorem BDS_TO_FETCH_EQ_INTERNAL_STATE_BDS_TO_UPDATE_NOT_EXPANDED_PRESERVES_INVARIANT_UPDATE_BD_DMA_WRITE_L4_LEMMA:
!device_characteristics memory1 memory2 device.
  BDS_TO_FETCH_EQ_INTERNAL_STATE device_characteristics memory1 memory2 device.dma_state.internal_state /\
  BDS_TO_UPDATE_NOT_EXPANDED device_characteristics device device /\
  INVARIANT_UPDATE_BD_DMA_WRITE_L4 device_characteristics memory1 device
  ==>
  INVARIANT_UPDATE_BD_DMA_WRITE_L4 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC INVARIANT_UPDATE_BD_DMA_WRITE_L4 THEN
ETAC DMA_WRITE THEN
INTRO_TAC THEN
AIRTAC THEN
IRTAC BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA THEN
STAC
QED

Theorem BDS_TO_FETCH_EQ_INTERNAL_STATE_BDS_TO_PROCESS_NOT_EXPANDED_PRESERVES_INVARIANT_PROCESS_BD_DMA_WRITE_L4_LEMMA:
!device_characteristics memory1 memory2 device.
  BDS_TO_FETCH_EQ_INTERNAL_STATE device_characteristics memory1 memory2 device.dma_state.internal_state /\
  BDS_TO_PROCESS_NOT_EXPANDED device_characteristics device device /\
  INVARIANT_PROCESS_BD_DMA_WRITE_L4 device_characteristics memory1 device
  ==>
  INVARIANT_PROCESS_BD_DMA_WRITE_L4 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC INVARIANT_PROCESS_BD_DMA_WRITE_L4 THEN
ETAC DMA_WRITE THEN
INTRO_TAC THEN
AIRTAC THEN
IRTAC BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA THEN
STAC
QED

Theorem WRITE_REQUEST_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory1 memory2 address_bytes tag.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l4 device_characteristics device) /\
  memory2 = update_memory memory1 address_bytes /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ASSUME_TAC BDS_TO_UPDATE_NOT_EXPANDED_REFL_LEMMA THEN
ASSUME_TAC BDS_TO_PROCESS_NOT_EXPANDED_REFL_LEMMA THEN
ASSUME_TAC BDS_TO_WRITE_BACK_NOT_EXPANDED_REFL_LEMMA THEN
ASSUME_TAC BD_TRANSFER_RAS_WAS_EQ_REFL_LEMMA THEN
ETAC INVARIANT_CONCRETE_L4 THEN
ITAC WRITE_REQUEST_PRESERVES_INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4_LEMMA THEN
ITAC WRITE_REQUEST_PRESERVES_INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4_LEMMA THEN
ITAC DMA_PENDING_REQUESTS_L4_NO_MEMORY_WRITES_BDS_TO_FETCH_IMPLIES_BDS_TO_FETCH_EQ_INTERNAL_STATE_LEMMA THEN
ITAC BDS_TO_FETCH_EQ_INTERNAL_STATE_BDS_TO_UPDATE_NOT_EXPANDED_PRESERVES_INVARIANT_UPDATE_BD_BD_WRITE_L4_LEMMA THEN
ITAC BDS_TO_FETCH_EQ_INTERNAL_STATE_BDS_TO_PROCESS_NOT_EXPANDED_PRESERVES_INVARIANT_PROCESS_BD_BD_WRITE_L4_LEMMA THEN
ITAC BDS_TO_FETCH_EQ_INTERNAL_STATE_BDS_TO_WRITE_BACK_NOT_EXPANDED_PRESERVES_INVARIANT_WRITE_BACK_BD_BD_WRITE_L4_LEMMA THEN
ITAC BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_INVARIANT_FETCH_BD_DMA_WRITE_L4_LEMMA THEN
ITAC BDS_TO_FETCH_EQ_INTERNAL_STATE_BDS_TO_UPDATE_NOT_EXPANDED_PRESERVES_INVARIANT_UPDATE_BD_DMA_WRITE_L4_LEMMA THEN
ITAC BDS_TO_FETCH_EQ_INTERNAL_STATE_BDS_TO_PROCESS_NOT_EXPANDED_PRESERVES_INVARIANT_PROCESS_BD_DMA_WRITE_L4_LEMMA THEN
STAC
QED



(*******************************************************************************)



Theorem DMA_REQUEST_SERVED_L4_WRITE_REQUEST_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory1 memory2 address_bytes tag.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l4 device_characteristics device1) /\
  memory2 = update_memory memory1 address_bytes /\
  device2 = dma_request_served_l4 device_characteristics device1 ([], request_write address_bytes tag) /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device1 /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device1 /\
  INVARIANT_CONCRETE_L4 device_characteristics memory1 device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
IRTAC WRITE_REQUEST_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN
IRTAC DMA_REQUEST_SERVED_L4_READ_REQUEST_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA THEN
STAC
QED

val _ = export_theory();

