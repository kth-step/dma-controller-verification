open HolKernel Parse boolLib bossLib helper_tactics;
open l4Theory invariant_l4Theory invariant_l4_lemmasTheory;

val _ = new_theory "writing_back_bd_l4_preserves_invariant_concrete_l4_lemmas";

Theorem WRITING_BACK_BD_L4_NOT_ADDING_BDS_TO_PIPELINE_LEMMA:
!device_characteristics channel_id channel1 channel2 internal_state1 internal_state2 environment.
  (internal_state2, channel2) = writing_back_bd_l4 device_characteristics channel_id environment internal_state1 channel1
  ==>
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  LIST1_IN_LIST2 channel2.queue.bds_to_write_back channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC writing_back_bd_l4 THEN EQ_PAIR_ASM_TAC THEN RLTAC THENL
[
 IRTAC writing_back_bd_l3_preserves_invariant_concrete_l3_lemmasTheory.WRITING_BACK_BD_REMOVE_RELEASED_BDS_NOT_ADDING_BDS_TO_PIPELINE_LEMMA THEN STAC
 ,
 IRTAC writing_back_bd_l3_preserves_invariant_concrete_l3_lemmasTheory.WRITING_BACK_BD_REMOVE_RELEASED_BDS_NOT_ADDING_BDS_TO_PIPELINE_LEMMA THEN
 IRTAC writing_back_bd_l3_preserves_invariant_concrete_l3_lemmasTheory.WRITING_BACK_BD_APPEND_REQUEST_PRESERVES_BDS_LEMMA THEN
 NRLTAC 2 THEN
 STAC
]
QED

Theorem WRITING_BACK_BD_L4_INTERNAL_STATE_LEMMA:
!device_characteristics channel_id environment internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = writing_back_bd_l4 device_characteristics channel_id environment internal_state1 channel1
  ==>
  ?write_address_bytes tag released_bds.
    (internal_state2, write_address_bytes, tag, released_bds) = (coperation device_characteristics channel_id).write_back_bd environment internal_state1 channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC writing_back_bd_l4 THEN
 EQ_PAIR_ASM_TAC THEN NRLTAC 2 THEN LRTAC THEN EXISTS_EQ_TAC
QED

Theorem WRITE_BACK_BD_IMPLIES_WRITE_BACK_BD_ADDRESSES_LEMMA:
!device_characteristics channel_id internal_state1 internal_state2 write_address_bytes tag released_bds environment bds_to_write_back.
  (internal_state2, write_address_bytes, tag, released_bds) = (coperation device_characteristics channel_id).write_back_bd environment internal_state1 bds_to_write_back
  ==>
  ?write_addresses.
    write_addresses = (cverification device_characteristics channel_id).write_back_bd_addresses environment internal_state1 bds_to_write_back
Proof
INTRO_TAC THEN
EXISTS_EQ_TAC
QED

Theorem INVARIANT_WRITE_BACK_BD_BD_WRITE_L4_IMPLIES_WRITE_ADDRESS_NOT_BD_TO_FETCH_LEMMA:
!device_characteristics memory channel_id device1 channel1 internal_state1
 internal_state2 write_address_bytes tag released_bds environment write_addresses.
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_DECLARED_WRITE_BACK_WRITES_BD_WAS device_characteristics /\
  INTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 device_characteristics memory device1 /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  write_addresses = (cverification device_characteristics channel_id).write_back_bd_addresses environment internal_state1 channel1.queue.bds_to_write_back /\
  (internal_state2, write_address_bytes, tag, released_bds) = (coperation device_characteristics channel_id).write_back_bd environment internal_state1 channel1.queue.bds_to_write_back
  ==>
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory internal_state1 write_addresses
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
INTRO_TAC THEN
ETAC listsTheory.DISJOINT_LISTS THEN
ETAC listTheory.EVERY_MEM THEN
INTRO_TAC THEN
APP_SCALAR_TAC THEN
CCONTR_TAC THEN
ETAC boolTheory.NOT_CLAUSES THEN
ETAC proof_obligationsTheory.PROOF_OBLIGATION_DECLARED_WRITE_BACK_WRITES_BD_WAS THEN
FAITAC THEN
AXTAC THEN
ETAC INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 THEN
ETAC BD_WRITE THEN
FAITAC THEN
ETAC bd_queuesTheory.CONSISTENT_BD_WRITE THEN
ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
AIRTAC THEN
FIRTAC lists_lemmasTheory.MEM_DISJOINT_LISTS_IMPLIES_F_LEMMA THEN
SOLVE_F_ASM_TAC
QED

Theorem WRITING_BACK_BD_L4_IMPLIES_BDS_TO_FETCH_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
  (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
  (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id memory internal_state1 internal_state2 channel1 channel2 environment.
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  PROOF_OBLIGATION_DECLARED_WRITE_BACK_WRITES_BD_WAS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 device_characteristics memory device1 /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = (schannel device1 channel_id) /\
  (internal_state2, channel2) = writing_back_bd_l4 device_characteristics channel_id environment internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BDS_TO_FETCH_EQ device_characteristics memory device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
IRTAC WRITING_BACK_BD_L4_INTERNAL_STATE_LEMMA THEN
AXTAC THEN
Cases_on ‘EXTERNAL_BDS device_characteristics’ THENL
[
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST THEN
 FAIRTAC THEN
 ETAC stateTheory.BDS_TO_FETCH_EQ THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 LRTAC THEN
 RLTAC THEN
 ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
 STAC
 ,
 IRTAC state_lemmasTheory.NOT_EXTERNAL_BDS_IMPLIES_INTERNAL_BDS_LEMMA THEN
 ITAC WRITE_BACK_BD_IMPLIES_WRITE_BACK_BD_ADDRESSES_LEMMA THEN
 AXTAC THEN
 ITAC INVARIANT_WRITE_BACK_BD_BD_WRITE_L4_IMPLIES_WRITE_ADDRESS_NOT_BD_TO_FETCH_LEMMA THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL THEN
 AIRTAC THEN
 ETAC stateTheory.BDS_TO_FETCH_EQ THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 LRTAC THEN
 RLTAC THEN
 ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
 STAC
]
QED

Theorem WRITING_BACK_BD_L4_IMPLIES_BDS_TO_FETCH_NOT_EXPANDED_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
  (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
  (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id memory internal_state1 internal_state2 channel1 channel2 environment.
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  PROOF_OBLIGATION_DECLARED_WRITE_BACK_WRITES_BD_WAS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 device_characteristics memory device1 /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = (schannel device1 channel_id) /\
  (internal_state2, channel2) = writing_back_bd_l4 device_characteristics channel_id environment internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
IRTAC WRITING_BACK_BD_L4_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
IRTAC BDS_TO_FETCH_EQ_IMPLIES_BDS_TO_FETCH_NOT_EXPANDED_LEMMA THEN
STAC
QED

Theorem WRITING_BACK_BD_L4_IMPLIES_BDS_TO_UPDATE_NOT_EXPANDED_LEMMA:
!device_characteristics channel_id environment internal_state1 internal_state2 channel1 channel2 device1 device2.
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = (schannel device1 channel_id) /\
  (internal_state2, channel2) = writing_back_bd_l4 device_characteristics channel_id environment internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BDS_TO_UPDATE_NOT_EXPANDED device_characteristics device1 device2
Proof
INTRO_TAC THEN
IRTAC WRITING_BACK_BD_L4_NOT_ADDING_BDS_TO_PIPELINE_LEMMA THEN
ITAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
ETAC BDS_TO_UPDATE_NOT_EXPANDED THEN
ETAC BDS_TO_OPERATE_ON_NOT_EXPANDED THEN
INTRO_TAC THEN
Cases_on ‘channel_id' = channel_id’ THENL
[
 LRTAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN
 LRTAC THEN
 REPEAT RLTAC THEN
 REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
 ,
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN
 AIRTAC THEN
 ALL_LRTAC THEN 
 REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
]
QED

Theorem WRITING_BACK_BD_L4_IMPLIES_BDS_TO_PROCESS_NOT_EXPANDED_LEMMA:
!device_characteristics channel_id environment internal_state1 internal_state2 channel1 channel2 device1 device2.
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = (schannel device1 channel_id) /\
  (internal_state2, channel2) = writing_back_bd_l4 device_characteristics channel_id environment internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BDS_TO_PROCESS_NOT_EXPANDED device_characteristics device1 device2
Proof
INTRO_TAC THEN
IRTAC WRITING_BACK_BD_L4_NOT_ADDING_BDS_TO_PIPELINE_LEMMA THEN
ITAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
ETAC BDS_TO_PROCESS_NOT_EXPANDED THEN
ETAC BDS_TO_OPERATE_ON_NOT_EXPANDED THEN
INTRO_TAC THEN
Cases_on ‘channel_id' = channel_id’ THENL
[
 LRTAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN
 LRTAC THEN
 REPEAT RLTAC THEN
 REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
 ,
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN
 AIRTAC THEN
 ALL_LRTAC THEN 
 REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
]
QED

Theorem WRITING_BACK_BD_L4_IMPLIES_BDS_TO_WRITE_BACK_NOT_EXPANDED_LEMMA:
!device_characteristics channel_id environment internal_state1 internal_state2 channel1 channel2 device1 device2.
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = (schannel device1 channel_id) /\
  (internal_state2, channel2) = writing_back_bd_l4 device_characteristics channel_id environment internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BDS_TO_WRITE_BACK_NOT_EXPANDED device_characteristics device1 device2
Proof
INTRO_TAC THEN
IRTAC WRITING_BACK_BD_L4_NOT_ADDING_BDS_TO_PIPELINE_LEMMA THEN
ITAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
ETAC BDS_TO_WRITE_BACK_NOT_EXPANDED THEN
ETAC BDS_TO_OPERATE_ON_NOT_EXPANDED THEN
INTRO_TAC THEN
Cases_on ‘channel_id' = channel_id’ THENL
[
 LRTAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN
 ALL_LRTAC THEN
 REPEAT RLTAC THEN
 STAC
 ,
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN
 AIRTAC THEN
 ALL_LRTAC THEN 
 REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
]
QED

Theorem WRITING_BACK_BD_L4_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA:
!device_characteristics channel_id device1 device2 internal_state1 internal_state2 channel1 channel2 environment.
  PROOF_OBLIGATION_WRITE_BACK_PRESERVES_BD_INTERPRETATION device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = writing_back_bd_l4 device_characteristics channel_id environment internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
IRTAC WRITING_BACK_BD_L4_INTERNAL_STATE_LEMMA THEN
AXTAC THEN
ETAC stateTheory.BD_TRANSFER_RAS_WAS_EQ THEN
INTRO_TAC THEN
ETAC proof_obligationsTheory.PROOF_OBLIGATION_WRITE_BACK_PRESERVES_BD_INTERPRETATION THEN
FAIRTAC THEN
AIRTAC THEN
IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
STAC
QED

Theorem WRITING_BACK_BD_L4_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory internal_state1 internal_state2 channel1 channel2 channel_id environment.
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  PROOF_OBLIGATION_DECLARED_WRITE_BACK_WRITES_BD_WAS device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_PRESERVES_BD_INTERPRETATION device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = writing_back_bd_l4 device_characteristics channel_id environment internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  INVARIANT_CONCRETE_L4 device_characteristics memory device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_CONCRETE_L4 THEN
ITAC WRITING_BACK_BD_L4_IMPLIES_BDS_TO_FETCH_NOT_EXPANDED_LEMMA THEN
ITAC WRITING_BACK_BD_L4_IMPLIES_BDS_TO_UPDATE_NOT_EXPANDED_LEMMA THEN
ITAC WRITING_BACK_BD_L4_IMPLIES_BDS_TO_PROCESS_NOT_EXPANDED_LEMMA THEN
ITAC WRITING_BACK_BD_L4_IMPLIES_BDS_TO_WRITE_BACK_NOT_EXPANDED_LEMMA THEN
IRTAC WRITING_BACK_BD_L4_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA THEN
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

val _ = export_theory();

