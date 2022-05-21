open HolKernel Parse boolLib bossLib helper_tactics;
open invariant_l2Theory;

val _ = new_theory "device_register_write_invariant_l2_preservation_lemmas";

Definition ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS:
ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device1 device2 internal_state pending_requests = (
  device2 = device1 with dma_state := device1.dma_state with
            <|internal_state := internal_state;
              pending_register_related_memory_requests := pending_requests|>
)
End

Theorem ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_PRESERVES_DEFINED_CHANNELS_LEMMA:
!device_characteristics device1 device2 internal_state pending_requests.
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device1 device2 internal_state pending_requests /\
  DEFINED_CHANNELS device_characteristics device1
  ==>
  DEFINED_CHANNELS device_characteristics device2
Proof
INTRO_TAC THEN
PTAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
ETAC stateTheory.DEFINED_CHANNELS THEN
ETAC stateTheory.VALID_CHANNELS THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem REGISTER_WRITE_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA:
!device_characteristics memory device1 device2 internal_state address_bytes requests pending_requests.
  PROOF_OBLIGATION_REGISTER_WRITE_PRESERVES_BD_INTERPRETATION device_characteristics /\
  (internal_state, requests) = device_characteristics.dma_characteristics.register_write device1.dma_state.internal_state address_bytes /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device1 device2 internal_state pending_requests /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_FETCH_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_FETCH_BD_L2 THEN
INTRO_TAC THEN
PTAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
LRTAC THEN
RW_HYPS_TAC stateTheory.schannel THEN
RECORD_TAC THEN
LRTAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_WRITE_PRESERVES_BD_INTERPRETATION THEN
AIRTAC THEN
AITAC THEN
QRLTAC THEN
AIRTAC THEN
STAC
QED

Theorem REGISTER_WRITE_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA:
!device_characteristics memory device1 device2 internal_state address_bytes requests pending_requests.
  PROOF_OBLIGATION_REGISTER_WRITE_PRESERVES_BD_INTERPRETATION device_characteristics /\
  (internal_state, requests) = device_characteristics.dma_characteristics.register_write device1.dma_state.internal_state address_bytes /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device1 device2 internal_state pending_requests /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_UPDATE_BD_L2 THEN
INTRO_TAC THEN
PTAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
LRTAC THEN
RW_HYPS_TAC stateTheory.schannel THEN
RECORD_TAC THEN
LRTAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_WRITE_PRESERVES_BD_INTERPRETATION THEN
AIRTAC THEN
AITAC THEN
QRLTAC THEN
AIRTAC THEN
STAC
QED

Theorem REGISTER_WRITE_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA:
!device_characteristics memory device1 device2 internal_state address_bytes requests pending_requests.
  PROOF_OBLIGATION_REGISTER_WRITE_PRESERVES_BD_INTERPRETATION device_characteristics /\
  (internal_state, requests) = device_characteristics.dma_characteristics.register_write device1.dma_state.internal_state address_bytes /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device1 device2 internal_state pending_requests /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device1
  ==>
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_TRANSFER_DATA_L2 THEN
INTRO_TAC THEN
PTAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
LRTAC THEN
RW_HYPS_TAC stateTheory.schannel THEN
RECORD_TAC THEN
LRTAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_WRITE_PRESERVES_BD_INTERPRETATION THEN
AIRTAC THEN
AITAC THEN
QRLTAC THEN
AIRTAC THEN
STAC
QED

Theorem REGISTER_WRITE_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA:
!device_characteristics memory device1 device2 internal_state address_bytes requests pending_requests.
  (internal_state, requests) = device_characteristics.dma_characteristics.register_write device1.dma_state.internal_state address_bytes /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device1 device2 internal_state pending_requests /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_WRITE_BACK_BD_L2 THEN
INTRO_TAC THEN
PTAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
LRTAC THEN
RW_HYPS_TAC stateTheory.schannel THEN
RECORD_TAC THEN
AIRTAC THEN
STAC
QED

Theorem REGISTER_WRITE_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA:
!device_characteristics memory device1 device2 internal_state2 address_bytes requests pending_requests.
  SCRATCHPAD_R_W device_characteristics memory internal_state2 /\
  (internal_state2, requests) = device_characteristics.dma_characteristics.register_write device1.dma_state.internal_state address_bytes /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device1 device2 internal_state2 pending_requests
  ==>
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_SCRATCHPAD_R_L2 THEN
INTRO_TAC THEN
PTAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
LRTAC THEN
RECORD_TAC THEN
PTAC proof_obligationsTheory.SCRATCHPAD_R_W THEN
PTAC proof_obligationsTheory.SCRATCHPAD_R THEN
AIRTAC THEN
STAC
QED

Theorem REGISTER_WRITE_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA:
!device_characteristics memory device1 device2 internal_state2 address_bytes requests pending_requests.
  SCRATCHPAD_R_W device_characteristics memory internal_state2 /\
  (internal_state2, requests) = device_characteristics.dma_characteristics.register_write device1.dma_state.internal_state address_bytes /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device1 device2 internal_state2 pending_requests
  ==>
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_SCRATCHPAD_W_L2 THEN
INTRO_TAC THEN
PTAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
LRTAC THEN
RECORD_TAC THEN
PTAC proof_obligationsTheory.SCRATCHPAD_R_W THEN
PTAC proof_obligationsTheory.SCRATCHPAD_W THEN
AIRTAC THEN
STAC
QED

Theorem REGISTER_WRITE_PRESERVES_INVARIANT_L2_LEMMA:
!device_characteristics memory device1 device2 internal_state address_bytes requests pending_requests.
  PROOF_OBLIGATION_REGISTER_WRITE_PRESERVES_BD_INTERPRETATION device_characteristics /\
  SCRATCHPAD_R_W device_characteristics memory internal_state /\
  (internal_state, requests) = device_characteristics.dma_characteristics.register_write device1.dma_state.internal_state address_bytes /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device1 device2 internal_state pending_requests /\
  INVARIANT_L2 device_characteristics memory device1
  ==>
  INVARIANT_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_L2 THEN
ITAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_PRESERVES_DEFINED_CHANNELS_LEMMA THEN
ITAC REGISTER_WRITE_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA THEN
ITAC REGISTER_WRITE_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA THEN
ITAC REGISTER_WRITE_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA THEN
ITAC REGISTER_WRITE_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA THEN
ITAC REGISTER_WRITE_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA THEN
ITAC REGISTER_WRITE_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA THEN
STAC
QED

Definition REGISTER_WRITE_SCRATCHPAD_R_W_L2:
REGISTER_WRITE_SCRATCHPAD_R_W_L2 device_characteristics memory device1 internal_state requests address_bytes = (
  (internal_state, requests) = device_characteristics.dma_characteristics.register_write device1.dma_state.internal_state address_bytes /\
  SCRATCHPAD_R_W device_characteristics memory internal_state
)
End

Theorem REGISTER_WRITE_SCRATCHPAD_R_W_L2_IMPLIES_SCRATCHPAD_R_W_LEMMA:
!device_characteristics memory device1 internal_state1 internal_state2 requests1 requests2 address_bytes.
  REGISTER_WRITE_SCRATCHPAD_R_W_L2 device_characteristics memory device1 internal_state1 requests1 address_bytes /\
  (internal_state2, requests2) = device_characteristics.dma_characteristics.register_write device1.dma_state.internal_state address_bytes
  ==>
  internal_state2 = internal_state1 /\
  requests2 = requests1 /\
  SCRATCHPAD_R_W device_characteristics memory internal_state1
Proof
INTRO_TAC THEN
PTAC REGISTER_WRITE_SCRATCHPAD_R_W_L2 THEN
RLTAC THEN
EQ_PAIR_ASM_TAC THEN
STAC
QED





Theorem REGISTER_WRITE_APPEND_BDS_PRESERVES_DEFINED_CHANNELS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory.
  device2 = dma_append_external_abstract_bds device_characteristics memory device1 /\
  DEFINED_CHANNELS device_characteristics device1
  ==>
  DEFINED_CHANNELS device_characteristics device2
Proof
INTRO_TAC THEN
ETAC stateTheory.DEFINED_CHANNELS THEN
ETAC stateTheory.VALID_CHANNELS THEN
INTRO_TAC THEN
IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_SOME_LEMMA THEN
STAC
QED

Theorem ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_ASSIGNS_INTERNAL_STATE_LEMMA:
!device1 device2 internal_state pending_requests.
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device1 device2 internal_state pending_requests
  ==>
  device2.dma_state.internal_state = internal_state
Proof
INTRO_TAC THEN
PTAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id device1 device2 internal_state pending_requests.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device1 device2 internal_state pending_requests
  ==>
  (schannel device2 channel_id).queue.bds_to_fetch = (schannel device1 channel_id).queue.bds_to_fetch
Proof
INTRO_TAC THEN
PTAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
REWRITE_TAC [stateTheory.schannel] THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem APPENDING_BDS_TO_FETCH_LEMMA:
!channel1 channel channel2 appended_bds.
  channel2 = channel with queue := channel.queue with bds_to_fetch := channel1.queue.bds_to_fetch ++ appended_bds
  ==>
  channel2.queue.bds_to_fetch = channel1.queue.bds_to_fetch ++ appended_bds
Proof
INTRO_TAC THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

(*
Theorem REGISTER_WRITE_APPEND_BDS_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width_copy, 'channel_index_width_read, 'channel_index_width_write,
                            'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type,
                            'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width_copy, 'channel_index_width_read, 'channel_index_width_write, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device : ('bd_type, 'channel_index_width_copy, 'channel_index_width_read, 'channel_index_width_write, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width_copy, 'channel_index_width_read, 'channel_index_width_write, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory internal_state pending_requests.
  REGISTER_WRITE_APPENDS_ABSTRACT_BDS_EXTERNAL_R_W device_characteristics device1 memory internal_state /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device1 device internal_state pending_requests /\
  device2 = dma_append_external_abstract_bds device_characteristics memory device /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory device
  ==>
  INVARIANT_FETCH_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_FETCH_BD_L2 THEN
INTRO_TAC THEN
ITAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_IMPLIES_EXTENDED_ABSTRACT_BDS_OR_PRESERVED_CHANNEL_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AXTAC THEN
 ITAC internal_operation_lemmasTheory.MEM_APPENDED_CHANNEL2_BDS_TO_FETCH_IMPLIES_MEM_CHANNEL1_BDS_TO_FETCH_OR_APPENDED_BDS_LEMMA THEN
 SPLIT_ASM_DISJS_TAC THENL
 [ 
  IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
  LRTAC THEN
  AIRTAC THEN
  STAC
  ,
  WEAKEN_TAC is_forall THEN
  PTAC proof_obligationsTheory.REGISTER_WRITE_APPENDS_ABSTRACT_BDS_EXTERNAL_R_W THEN
  AITAC THEN
  AXTAC THEN
  ITAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_ASSIGNS_INTERNAL_STATE_LEMMA THEN
  RLTAC THEN
  ITAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_PRESERVES_BDS_TO_FETCH_LEMMA THEN
  LRTAC THEN
  IRTAC APPENDING_BDS_TO_FETCH_LEMMA THEN
  LRTAC THEN
  RLTAC THEN
  ETAC listTheory.APPEND_11 THEN
  LRTAC THEN
  IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
  AIRTAC THEN
  LRTAC THEN
  LRTAC THEN
  RLTAC THEN
  STAC
 ]
 ,
 AIRTAC THEN
 IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
 STAC
]
QED

Theorem REGISTER_WRITE_APPEND_BDS_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory internal_state pending_requests.
  REGISTER_WRITE_APPENDS_CONCRETE_BDS_EXTERNAL_R_W device_characteristics memory device1.dma_state.internal_state internal_state /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device1 device internal_state pending_requests /\
  device2 = dma_append_external_abstract_bds device_characteristics memory device /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device1 device1 /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory device
  ==>
  INVARIANT_FETCH_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_FETCH_BD_L2 THEN
INTRO_TAC THEN
ITAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_IMPLIES_EXTENDED_ABSTRACT_BDS_OR_PRESERVED_CHANNEL_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AXTAC THEN
 ITAC internal_operation_lemmasTheory.MEM_APPENDED_CHANNEL2_BDS_TO_FETCH_IMPLIES_MEM_CHANNEL1_BDS_TO_FETCH_OR_APPENDED_BDS_LEMMA THEN
 SPLIT_ASM_DISJS_TAC THENL
 [ 
  IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
  LRTAC THEN
  AIRTAC THEN
  STAC
  ,
  WEAKEN_TAC is_forall THEN
  PTAC proof_obligationsTheory.REGISTER_WRITE_APPENDS_CONCRETE_BDS_EXTERNAL_R_W THEN
  AITAC THEN
  AXTAC THEN
  ITAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_ASSIGNS_INTERNAL_STATE_LEMMA THEN
  RLTAC THEN
  ITAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_PRESERVES_BDS_TO_FETCH_LEMMA THEN
  LRTAC THEN
  IRTAC APPENDING_BDS_TO_FETCH_LEMMA THEN
  LRTAC THEN
  RLTAC THEN
  PTAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
  AITAC THEN
  LRTAC THEN
  ETAC listTheory.APPEND_11 THEN
  LRTAC THEN
  IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
  AIRTAC THEN
  LRTAC THEN
  LRTAC THEN
  RLTAC THEN
  STAC
 ]
 ,
 AIRTAC THEN
 IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
 STAC
]
QED

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA:
!device_characteristics memory device1 device2.
  device2 = dma_append_external_abstract_bds device_characteristics memory device1 /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_UPDATE_BD_L2 THEN
INTRO_TAC THEN
ITAC append_external_bds_invariant_l2_preservation_lemmasTheory.APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_BDS_TO_UPDATE_LEMMA THEN
IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
AIRTAC THEN
STAC
QED

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA:
!device_characteristics memory device1 device2.
  device2 = dma_append_external_abstract_bds device_characteristics memory device1 /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device1
  ==>
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_TRANSFER_DATA_L2 THEN
INTRO_TAC THEN
ITAC append_external_bds_invariant_l2_preservation_lemmasTheory.APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_BDS_TO_PROCESS_LEMMA THEN
IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
AIRTAC THEN
STAC
QED

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA:
!device_characteristics memory device1 device2.
  device2 = dma_append_external_abstract_bds device_characteristics memory device1 /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_WRITE_BACK_BD_L2 THEN
INTRO_TAC THEN
ITAC append_external_bds_invariant_l2_preservation_lemmasTheory.APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_BDS_TO_WRITE_BACK_LEMMA THEN
IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
AIRTAC THEN
STAC
QED

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA:
!device_characteristics memory device1 device2.
  device2 = dma_append_external_abstract_bds device_characteristics memory device1 /\
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device1
  ==>
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_SCRATCHPAD_R_L2 THEN
IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
STAC
QED

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA:
!device_characteristics memory device1 device2.
  device2 = dma_append_external_abstract_bds device_characteristics memory device1 /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device1
  ==>
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_SCRATCHPAD_W_L2 THEN
IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
STAC
QED

Theorem REGISTER_WRITE_APPEND_BDS_PRESERVES_INVARIANT_L2_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width_copy, 'channel_index_width_read, 'channel_index_width_write,
                            'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type,
                            'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width_copy, 'channel_index_width_read, 'channel_index_width_write, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device : ('bd_type, 'channel_index_width_copy, 'channel_index_width_read, 'channel_index_width_write, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width_copy, 'channel_index_width_read, 'channel_index_width_write, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 internal_state memory pending_requests.
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device1 device internal_state pending_requests /\
  REGISTER_WRITE_APPENDS_ABSTRACT_BDS_EXTERNAL_R_W device_characteristics device1 memory internal_state /\
  device2 = dma_append_external_abstract_bds device_characteristics memory device /\
  INVARIANT_L2 device_characteristics memory device
  ==>
  INVARIANT_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_L2 THEN
ITAC REGISTER_WRITE_APPEND_BDS_PRESERVES_DEFINED_CHANNELS_LEMMA THEN
ITAC REGISTER_WRITE_APPEND_BDS_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA THEN
ITAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA THEN
ITAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA THEN
ITAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA THEN
ITAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA THEN
ITAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA THEN
STAC
QED

Theorem REGISTER_WRITE_APPEND_BDS_PRESERVES_INVARIANT_L2_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 internal_state memory pending_requests.
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device1 device internal_state pending_requests /\
  REGISTER_WRITE_APPENDS_CONCRETE_BDS_EXTERNAL_R_W device_characteristics memory device1.dma_state.internal_state internal_state /\
  device2 = dma_append_external_abstract_bds device_characteristics memory device /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device1 device1 /\
  INVARIANT_L2 device_characteristics memory device
  ==>
  INVARIANT_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_L2 THEN
ITAC REGISTER_WRITE_APPEND_BDS_PRESERVES_DEFINED_CHANNELS_LEMMA THEN
ITAC REGISTER_WRITE_APPEND_BDS_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA THEN
ITAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA THEN
ITAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA THEN
ITAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA THEN
ITAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA THEN
ITAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA THEN
STAC
QED
*)

Theorem REGISTER_WRITE_IMPLIES_SCRATCHPAD_R_W_L2_LEMMA:
!INVARIANT_CPU cpu_transition cpu1 cpu2 memory
 (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 address_bytes internal_state requests.
  INVARIANT_CPU memory cpu1 /\
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_SCRATCHPAD_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  (internal_state, requests) = device_characteristics.dma_characteristics.register_write device1.dma_state.internal_state address_bytes
  ==>
  REGISTER_WRITE_SCRATCHPAD_R_W_L2 device_characteristics memory device1 internal_state requests address_bytes
Proof
INTRO_TAC THEN
PTAC REGISTER_WRITE_SCRATCHPAD_R_W_L2 THEN
PTAC proof_obligations_cpu_l2Theory.PROOF_OBLIGATION_CPU_REGISTER_WRITE_SCRATCHPAD_R_W THEN
AITAC THEN
STAC
QED

(*
Theorem REGISTER_WRITE_IMPLIES_APPENDS_ABSTRACT_BDS_EXTERNAL_R_W_LEMMA:
!INVARIANT_CPU requests cpu_transition
 (device_characteristics : ('bd_type, 'channel_index_width_copy, 'channel_index_width_read, 'channel_index_width_write,
                            'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type,
                            'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width_copy, 'channel_index_width_read, 'channel_index_width_write, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 cpu1 cpu2 address_bytes memory internal_state.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_APPENDS_ABSTRACT_BDS_EXTERNAL_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  (internal_state, requests) = device_characteristics.dma_characteristics.register_write device1.dma_state.internal_state address_bytes
  ==>
  REGISTER_WRITE_APPENDS_ABSTRACT_BDS_EXTERNAL_R_W device_characteristics device1 memory internal_state
Proof
INTRO_TAC THEN
PTAC proof_obligations_cpu_l2Theory.PROOF_OBLIGATION_CPU_REGISTER_WRITE_APPENDS_ABSTRACT_BDS_EXTERNAL_R_W THEN
AIRTAC THEN
STAC
QED

Theorem REGISTER_WRITE_IMPLIES_APPENDS_CONCRETE_BDS_EXTERNAL_R_W_LEMMA:
!INVARIANT_CPU requests cpu_transition
 (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 cpu1 cpu2 address_bytes memory internal_state.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_APPENDS_CONCRETE_BDS_EXTERNAL_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  (internal_state, requests) = device_characteristics.dma_characteristics.register_write device1.dma_state.internal_state address_bytes
  ==>
  REGISTER_WRITE_APPENDS_CONCRETE_BDS_EXTERNAL_R_W device_characteristics memory device1.dma_state.internal_state internal_state
Proof
INTRO_TAC THEN
PTAC proof_obligations_cpu_l2Theory.PROOF_OBLIGATION_CPU_REGISTER_WRITE_APPENDS_CONCRETE_BDS_EXTERNAL_R_W THEN
AIRTAC THEN
STAC
QED
*)

Definition APPENDED_ABSTRACT_BDS_R_W:
APPENDED_ABSTRACT_BDS_R_W device_characteristics memory1 memory2 device1 device2 =
!channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  (?appended_bds.
    (schannel device2 channel_id).queue.bds_to_fetch = (schannel device1 channel_id).queue.bds_to_fetch ++ appended_bds /\
    (schannel device2 channel_id).queue.bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory2 device2.dma_state.internal_state /\
    APPENDED_BDS_R_W device_characteristics memory2 device2.dma_state.internal_state channel_id appended_bds) /\
  (schannel device2 channel_id).queue.bds_to_update = (schannel device1 channel_id).queue.bds_to_update /\
  (schannel device2 channel_id).queue.bds_to_process = (schannel device1 channel_id).queue.bds_to_process /\
  (schannel device2 channel_id).queue.bds_to_write_back = (schannel device1 channel_id).queue.bds_to_write_back
End

Theorem FILTER_IS_VALID_L2_ID_LEMMA:
!l.
  FILTER is_valid_l2 l = l
Proof
Induct THEN REWRITE_TAC [listTheory.FILTER] THEN
GEN_TAC THEN
PTAC l2Theory.is_valid_l2 THEN
REWRITE_TAC [l2Theory.is_valid_l2] THEN
STAC
QED

Theorem DMA_REGISTER_WRITE_L2_IMPLIES_DMA_APPEND_EXTERNAL_ABSTRACT_BDS_LEMMA:
!device_characteristics memory1 device1 device2 cpu_address_bytes dma_address_bytes.
  (device2, dma_address_bytes) = dma_register_write device_characteristics is_valid_l2 (SOME memory1) device1 cpu_address_bytes
  ==>
  ?internal_state new_requests write_requests device memory2.
    (internal_state, new_requests) = device_characteristics.dma_characteristics.register_write device1.dma_state.internal_state cpu_address_bytes /\
    write_requests = FILTER WRITE_REQUEST new_requests /\
    dma_address_bytes = FLAT (MAP request_to_address_bytes write_requests) /\
    memory2 = update_memory memory1 dma_address_bytes /\
    CHANNELS_EQ device1 device /\
    device.dma_state.internal_state = internal_state /\
    device2 = dma_append_external_abstract_bds device_characteristics memory2 device
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_register_write THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 2 THEN
ETAC FILTER_IS_VALID_L2_ID_LEMMA THEN
PTAC operationsTheory.dma_append_internal_abstract_bds THENL
[
 PTAC operationsTheory.update_memory_option THEN
 LRTAC THEN
 HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
 ,
 PTAC operationsTheory.update_memory_option THEN
 LRTAC THEN
 ETAC optionTheory.SOME_11 THEN
 Q.EXISTS_TAC ‘internal_state’ THEN
 Q.EXISTS_TAC ‘new_requests’ THEN
 Q.EXISTS_TAC ‘write_requests’ THEN
 Q.EXISTS_TAC ‘device’ THEN
 Q.EXISTS_TAC ‘x’ THEN
 ALL_LRTAC THEN
 ETAC stateTheory.CHANNELS_EQ THEN
 RECORD_TAC THEN
 STAC
]
QED

Definition EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS:
EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS device_characteristics memory device1 device2 =
!channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  !bds_to_fetch channel1 channel2.
    bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory device1.dma_state.internal_state ∧
    channel1 = schannel device1 channel_id /\
    channel2 = schannel device2 channel_id
    ==>
    EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL channel1 channel2 bds_to_fetch
End

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_IMPLIES_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  device2 = dma_append_external_abstract_bds device_characteristics memory device1
  ==>
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS device_characteristics memory device1 device2
Proof
INTRO_TAC THEN
PTAC EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS THEN
INTRO_TAC THEN
INTRO_TAC THEN
IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
STAC
QED

Definition INTERNAL_BDS_TO_FETCH_EQ:
INTERNAL_BDS_TO_FETCH_EQ device_characteristics =
!channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  !internal_state memory1 memory2.
    (cverification device_characteristics channel_id).bds_to_fetch memory1 internal_state =
    (cverification device_characteristics channel_id).bds_to_fetch memory2 internal_state
End

Theorem INTERNAL_BDS_IMPLIES_INTERNAL_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  INTERNAL_BDS device_characteristics
  ==>
  INTERNAL_BDS_TO_FETCH_EQ device_characteristics
Proof
INTRO_TAC THEN
ETAC proof_obligationsTheory.PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY THEN
ETAC INTERNAL_BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
AIRTAC THEN
CCONTR_TAC THEN
CONTR_ASMS_TAC
QED

Theorem INTERNAL_BDS_TO_FETCH_EQ_PRESERVES_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_LEMMA:
!device_characteristics memory1 device1 device2.
  INTERNAL_BDS_TO_FETCH_EQ device_characteristics /\
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS device_characteristics memory1 device1 device2
  ==>
  !memory2.
    EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS device_characteristics memory2 device1 device2
Proof
INTRO_TAC THEN
GEN_TAC THEN
ETAC EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS THEN
INTRO_TAC THEN
INTRO_TAC THEN
AITAC THEN
PTAC INTERNAL_BDS_TO_FETCH_EQ THEN
AIRTAC THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC_ALL (SPEC “(device1 : ('a, 'b, 'h, 'e, 'f, 'i) device_state_type).dma_state.internal_state” thm))) THEN
RLTAC THEN
AIRTAC THEN
STAC
QED

Theorem REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_LEMMA:
!device_characteristics memory1 memory2 device1 device device2.
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory1 device1 device1 /\
  CHANNELS_EQ device1 device /\
  REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W device_characteristics memory1 memory2 device1.dma_state.internal_state device.dma_state.internal_state /\
  device2.dma_state.internal_state = device.dma_state.internal_state /\
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS device_characteristics memory2 device device2
  ==>
  APPENDED_ABSTRACT_BDS_R_W device_characteristics memory1 memory2 device1 device2
Proof
INTRO_TAC THEN
ETAC APPENDED_ABSTRACT_BDS_R_W THEN
INTRO_TAC THEN
ETAC proof_obligations_cpu_l2Theory.REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W THEN
AITAC THEN
ETAC EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS THEN
AITAC THEN
ETAC stateTheory.CHANNELS_EQ THEN
RW_HYPS_TAC stateTheory.schannel THEN
REWRITE_TAC [stateTheory.schannel] THEN
RLTAC THEN
RLTAC THEN
RW_HYPS_TAC (GSYM stateTheory.schannel) THEN
REWRITE_TAC [GSYM stateTheory.schannel] THEN
AITAC THEN
AXTAC THEN
ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL THEN
SPLIT_ASM_DISJS_TAC THENL
[
 ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH THEN
 ETAC operationsTheory.APPENDED_BDS THEN
 ETAC operationsTheory.EXTENDED_BDS THEN
 AXTAC THEN
 LRTAC THEN
 CONJS_TAC THENL
 [
  ETAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
  AIRTAC THEN
  LRTAC THEN
  LRTAC THEN
  RECORD_TAC THEN
  ETAC listTheory.APPEND_11 THEN
  LRTAC THEN
  PAXTAC THEN
  STAC
  ,
  LRTAC THEN LRTAC THEN RECORD_TAC THEN STAC
  ,
  LRTAC THEN LRTAC THEN RECORD_TAC THEN STAC
  ,
  LRTAC THEN LRTAC THEN RECORD_TAC THEN STAC
 ]
 ,
 ETAC operationsTheory.NOT_EXTENDED_ABSTRACT_BDS_TO_FETCH_AND_UNCHANGED_CHANNEL THEN
 ETAC operationsTheory.EXTENDED_BDS THEN
 ASM_NOT_EXISTS_TO_FORALL_NOT_TAC THEN
 ETAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
 AIRTAC THEN
 PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC_ALL thm)) THEN
 MATCH_MP_TAC boolTheory.FALSITY THEN
 LRTAC THEN
 CONTR_ASMS_TAC
]
QED

Definition DMA_STATE_EQ:
DMA_STATE_EQ device1 device2 = (
  device1.dma_state = device2.dma_state
)
End

Theorem FUNCTION_REGISTER_WRITE_IMPLIES_DMA_STATE_EQ_LEMMA:
!device_characteristics device1 device2 cpu_address_bytes.
  device2 = function_register_write device_characteristics device1 cpu_address_bytes
  ==>
  DMA_STATE_EQ device1 device2
Proof
INTRO_TAC THEN
PTAC operationsTheory.function_register_write THEN
ETAC DMA_STATE_EQ THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_DMA_STATE_EQ_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_LEMMA:
!device_characteristics memory device1 device2.
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device1 device1 /\
  DMA_STATE_EQ device1 device2
  ==>
  APPENDED_ABSTRACT_BDS_R_W device_characteristics memory memory device1 device2
Proof
REWRITE_TAC [DMA_STATE_EQ, APPENDED_ABSTRACT_BDS_R_W, stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ, stateTheory.schannel] THEN
INTRO_TAC THEN
LRTAC THEN
REWRITE_TAC [] THEN
INTRO_TAC THEN
AIRTAC THEN
LRTAC THEN
Q.EXISTS_TAC ‘[]’ THEN
ETAC proof_obligations_cpu_l2Theory.APPENDED_BDS_R_W THEN
REWRITE_TAC [listTheory.MEM, listTheory.APPEND_NIL]
QED

Theorem ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_REFL_LEMMA:
!device_characteristics memory device.
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device device
  ==>
  APPENDED_ABSTRACT_BDS_R_W device_characteristics memory memory device device
Proof
INTRO_TAC THEN
ETAC APPENDED_ABSTRACT_BDS_R_W THEN
REWRITE_TAC [] THEN
INTRO_TAC THEN
Q.EXISTS_TAC ‘[]’ THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
AIRTAC THEN
LRTAC THEN
REWRITE_TAC [listTheory.APPEND_NIL, proof_obligations_cpu_l2Theory.APPENDED_BDS_R_W, listTheory.MEM]
QED

Theorem DEVICE_REGISTER_WRITE_L2_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_INTERNAL_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory1 device1 device1 /\
  INTERNAL_BDS device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write cpu_address_bytes) cpu2 /\
  (device2, dma_address_bytes) = device_register_write_l2 device_characteristics memory1 device1 cpu_address_bytes /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  APPENDED_ABSTRACT_BDS_R_W device_characteristics memory1 memory2 device1 device2
Proof
INTRO_TAC THEN
PTAC l2Theory.device_register_write_l2 THEN
PTAC operationsTheory.device_register_write THENL
[
 WEAKEN_TAC (fn assumption => (not o is_eq) assumption) THEN
 ITAC INTERNAL_BDS_IMPLIES_INTERNAL_BDS_TO_FETCH_EQ_LEMMA THEN
 IRTAC DMA_REGISTER_WRITE_L2_IMPLIES_DMA_APPEND_EXTERNAL_ABSTRACT_BDS_LEMMA THEN
 AXTAC THEN
 ASM_RL_RW_OTHERS_KEEP_TAC THEN
 RLTAC THEN
 PTAC proof_obligations_cpu_l2Theory.PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W THEN
 AIRTAC THEN
 RLTAC THEN
 ITAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
 IRTAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_IMPLIES_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_LEMMA THEN
 IRTAC INTERNAL_BDS_TO_FETCH_EQ_PRESERVES_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_LEMMA THEN
 IRTAC REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
 IRTAC FUNCTION_REGISTER_WRITE_IMPLIES_DMA_STATE_EQ_LEMMA THEN
 IRTAC ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_DMA_STATE_EQ_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
 NRLTAC 2 THEN
 IRTAC ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_REFL_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
 NRLTAC 2 THEN
 IRTAC ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_REFL_LEMMA THEN
 STAC
]
QED

Theorem DMA_REGISTER_WRITE_L2_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_EXTERNAL_LEMMA:
!device_characteristics INVARIANT_CPU cpu_transition cpu1 cpu2  memory1 memory2 device1 device2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  EXTERNAL_BDS device_characteristics /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory1 device1 device1 /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write cpu_address_bytes) cpu2 /\
  (device2, dma_address_bytes) = device_register_write_l2 device_characteristics memory1 device1 cpu_address_bytes /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  APPENDED_ABSTRACT_BDS_R_W device_characteristics memory1 memory2 device1 device2
Proof
INTRO_TAC THEN
PTAC l2Theory.device_register_write_l2 THEN
PTAC operationsTheory.device_register_write THENL
[
 IRTAC DMA_REGISTER_WRITE_L2_IMPLIES_DMA_APPEND_EXTERNAL_ABSTRACT_BDS_LEMMA THEN
 AXTAC THEN
 ASM_RL_RW_OTHERS_KEEP_TAC THEN
 RLTAC THEN
 PTAC proof_obligations_cpu_l2Theory.PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W THEN
 AIRTAC THEN
 ITAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
 IRTAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_IMPLIES_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_LEMMA THEN
 IRTAC REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
 IRTAC FUNCTION_REGISTER_WRITE_IMPLIES_DMA_STATE_EQ_LEMMA THEN
 IRTAC ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_DMA_STATE_EQ_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
 NRLTAC 2 THEN
 IRTAC ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_REFL_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
 NRLTAC 2 THEN
 IRTAC ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_REFL_LEMMA THEN
 STAC
]
QED

Theorem DEVICE_REGISTER_WRITE_L2_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics memory1 memory2 cpu1 cpu2 device1 device2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory1 device1 device1 /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write cpu_address_bytes) cpu2 /\
  (device2, dma_address_bytes) = device_register_write_l2 device_characteristics memory1 device1 cpu_address_bytes /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  APPENDED_ABSTRACT_BDS_R_W device_characteristics memory1 memory2 device1 device2
Proof
INTRO_TAC THEN
Cases_on ‘INTERNAL_BDS device_characteristics’ THENL
[
 IRTAC DEVICE_REGISTER_WRITE_L2_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_INTERNAL_LEMMA THEN STAC
 ,
 IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
 IRTAC DMA_REGISTER_WRITE_L2_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_EXTERNAL_LEMMA THEN
 STAC
]
QED

Theorem DEVICE_TRANSITION_L2_CPU_REGISTER_WRITE_MEMORY_IMPLIES_WRITE_APPENDED_ABSTRACT_BDS_R_W_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics memory1 memory2 cpu1 cpu2 device1 device2 cpu_dma_address_bytes.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory1 device1 device1 /\
  INVARIANT_CPU memory1 cpu1 /\
  system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device1) (cpu_register_write_memory_write cpu_dma_address_bytes) (cpu2, memory2, device2)
  ==>
  APPENDED_ABSTRACT_BDS_R_W device_characteristics memory1 memory2 device1 device2
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
INTRO_TAC THEN
AXTAC THEN
PAT_X_ASSUM “x = (y, z)” (fn thm => ASSUME_TAC (GSYM thm)) THEN
NRLTAC 7 THEN
AXTAC THEN
NRLTAC 3 THEN
WEAKEN_TAC is_disj THEN
IRTAC DEVICE_REGISTER_WRITE_L2_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_LEMMA THEN
STAC
QED

Theorem DEVICE_REGISTER_WRITE_L2_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA:
!device_characteristics memory device1 device2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_WRITE_PRESERVES_BD_INTERPRETATION device_characteristics /\
  (device2, dma_address_bytes) = device_register_write_l2 device_characteristics memory device1 cpu_address_bytes
  ==>
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC l2Theory.device_register_write_l2 THEN
ETAC stateTheory.BD_TRANSFER_RAS_WAS_EQ THEN
PTAC operationsTheory.device_register_write THENL
[
 IRTAC DMA_REGISTER_WRITE_L2_IMPLIES_DMA_APPEND_EXTERNAL_ABSTRACT_BDS_LEMMA THEN
 AXTAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_WRITE_PRESERVES_BD_INTERPRETATION THEN
 AIRTAC THEN
 IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
 RLTAC THEN
 RLTAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN PTAC operationsTheory.function_register_write THEN LRTAC THEN RECORD_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem DEVICE_TRANSITION_L2_CPU_REGISTER_WRITE_MEMORY_WRITE_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA:
!device_characteristics cpu_transition cpu1 cpu2 memory1 memory2 device1 device2 cpu_dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_WRITE_PRESERVES_BD_INTERPRETATION device_characteristics /\
  system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device1) (cpu_register_write_memory_write cpu_dma_address_bytes) (cpu2, memory2, device2)
  ==>
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
INTRO_TAC THEN
AXTAC THEN
PAT_X_ASSUM “x = (y, z)” (fn thm => ASSUME_TAC (GSYM thm)) THEN
NRLTAC 7 THEN
AXTAC THEN
NRLTAC 3 THEN
WEAKEN_TAC is_disj THEN
IRTAC DEVICE_REGISTER_WRITE_L2_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA THEN
STAC
QED

Theorem DMA_REGISTER_WRITE_L2_WRITE_WRITABLE_MEMORY_LEMMA:
!device_characteristics memory device1 device2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device1 /\
  (device2, dma_address_bytes) = dma_register_write device_characteristics is_valid_l2 (SOME memory) device1 cpu_address_bytes
  ==>
  EVERY (device_characteristics.dma_characteristics.W memory) (MAP FST dma_address_bytes)
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_register_write THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 2 THEN
IRTAC write_properties_lemmasTheory.WRITE_REQUESTS_IMPLIES_WRITE_REQUEST_LEMMA THEN
ETAC listTheory.EVERY_MEM THEN
INTRO_TAC THEN
IRTAC lists_lemmasTheory.MEM_ADDRESS_IMPLIES_MEM_ADDRESS_BYTES_LEMMA THEN
AXTAC THEN
AIRTAC THEN
AXTAC THEN
LRTAC THEN
LRTAC THEN
LRTAC THEN
LRTAC THEN
ETAC listTheory.MEM_FILTER THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD THEN
AITAC THEN
IRTAC lists_lemmasTheory.MEM_ADDRESS_BYTE_IN_LIST1_IN_LIST2_IMPLIES_MEM_ADDRESS_LEMMA THEN
PTAC INVARIANT_SCRATCHPAD_W_L2 THEN
AIRTAC THEN
ETAC listTheory.EVERY_MEM THEN
AIRTAC THEN
STAC
QED

Theorem DEVICE_REGISTER_WRITE_L2_WRITE_WRITABLE_MEMORY_LEMMA:
!device_characteristics memory device1 device2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device1 /\
  (device2, dma_address_bytes) = device_register_write_l2 device_characteristics memory device1 cpu_address_bytes
  ==>
  EVERY (device_characteristics.dma_characteristics.W memory) (MAP FST dma_address_bytes)
Proof
INTRO_TAC THEN
PTAC l2Theory.device_register_write_l2 THEN
PTAC operationsTheory.device_register_write THENL
[
 IRTAC DMA_REGISTER_WRITE_L2_WRITE_WRITABLE_MEMORY_LEMMA THEN STAC
 ,
 PTAC operationsTheory.function_register_write THEN EQ_PAIR_ASM_TAC THEN LRTAC THEN REWRITE_TAC [listTheory.MAP, listTheory.EVERY_DEF]
 ,
 EQ_PAIR_ASM_TAC THEN LRTAC THEN REWRITE_TAC [listTheory.MAP, listTheory.EVERY_DEF] 
 ,
 EQ_PAIR_ASM_TAC THEN LRTAC THEN REWRITE_TAC [listTheory.MAP, listTheory.EVERY_DEF] 
]
QED

Theorem DEVICE_REGISTER_WRITE_L2_IMPLIES_R_W_EQ_LEMMA:
!device_characteristics memory1 memory2 device1 device2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory1 device1 /\
  (device2, dma_address_bytes) = device_register_write_l2 device_characteristics memory1 device1 cpu_address_bytes /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  R_W_EQ device_characteristics memory1 memory2
Proof
INTRO_TAC THEN
IRTAC DEVICE_REGISTER_WRITE_L2_WRITE_WRITABLE_MEMORY_LEMMA THEN
ITAC write_properties_lemmasTheory.WRITING_WRITABLE_MEMORY_PRESERVES_UNWRITABLE_MEMORY_LEMMA THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_READABLE_WRITABLE THEN
AIRTAC THEN
ETAC stateTheory.R_W_EQ THEN
STAC
QED

Theorem DEVICE_TRANSITION_L2_CPU_REGISTER_WRITE_MEMORY_WRITE_IMPLIES_R_W_EQ_LEMMA:
!device_characteristics cpu_transition cpu1 cpu2 memory1 memory2 device1 device2 cpu_dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory1 device1 /\
  system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device1) (cpu_register_write_memory_write cpu_dma_address_bytes) (cpu2, memory2, device2)
  ==>
  R_W_EQ device_characteristics memory1 memory2
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
INTRO_TAC THEN
AXTAC THEN
PAT_X_ASSUM “x = (y, z)” (fn thm => ASSUME_TAC (GSYM thm)) THEN
NRLTAC 7 THEN
AXTAC THEN
NRLTAC 3 THEN
WEAKEN_TAC is_disj THEN
IRTAC DEVICE_REGISTER_WRITE_L2_IMPLIES_R_W_EQ_LEMMA THEN
STAC
QED

Theorem DEVICE_REGISTER_WRITE_L2_PRESERVES_DEFINED_CHANNELS_LEMMA:
!device_characteristics memory1 device1 device2 cpu_address_bytes dma_address_bytes.
  (device2, dma_address_bytes) = device_register_write_l2 device_characteristics memory1 device1 cpu_address_bytes /\
  DEFINED_CHANNELS device_characteristics device1
  ==>
  DEFINED_CHANNELS device_characteristics device2
Proof
INTRO_TAC THEN
PTAC l2Theory.device_register_write_l2 THEN
PTAC operationsTheory.device_register_write THENL
[
 PTAC operationsTheory.dma_register_write THEN
 ETAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
 IRTAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_PRESERVES_DEFINED_CHANNELS_LEMMA THEN
 PTAC operationsTheory.dma_append_internal_abstract_bds THENL
 [
  RLTAC THEN EQ_PAIR_ASM_TAC THEN STAC
  ,
  EQ_PAIR_ASM_TAC THEN
  IRTAC REGISTER_WRITE_APPEND_BDS_PRESERVES_DEFINED_CHANNELS_LEMMA THEN
  STAC
 ]
 ,
 EQ_PAIR_ASM_TAC THEN
 PTAC operationsTheory.function_register_write THEN 
 ETAC stateTheory.DEFINED_CHANNELS THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem DEVICE_TRANSITION_L2_CPU_REGISTER_WRITE_MEMORY_WRITE_PRESERVES_DEFINED_CHANNELS_LEMMA:
!device_characteristics cpu_transition cpu1 cpu2 cpu_dma_address_bytes memory1 memory2 device1 device2.
  system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device1) (cpu_register_write_memory_write cpu_dma_address_bytes) (cpu2, memory2, device2) /\
  DEFINED_CHANNELS device_characteristics device1
  ==>
  DEFINED_CHANNELS device_characteristics device2
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
INTRO_TAC THEN
AXTAC THEN
PAT_X_ASSUM “x = (y, z)” (fn thm => ASSUME_TAC (GSYM thm)) THEN
NRLTAC 7 THEN
AXTAC THEN
NRLTAC 3 THEN
WEAKEN_TAC is_disj THEN
IRTAC DEVICE_REGISTER_WRITE_L2_PRESERVES_DEFINED_CHANNELS_LEMMA THEN
STAC
QED

Theorem APPENDED_ABSTRACT_BDS_R_W_BD_TRANSFER_RAS_WAS_EQ_R_W_EQ_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA:
!device_characteristics memory1 memory2 device1 device2.
  APPENDED_ABSTRACT_BDS_R_W device_characteristics memory1 memory2 device1 device2 /\
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state /\
  R_W_EQ device_characteristics memory1 memory2 /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory1 device1
  ==>
  INVARIANT_FETCH_BD_L2 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_FETCH_BD_L2 THEN
INTRO_TAC THEN
LRTAC THEN LRTAC THEN LRTAC THEN LRTAC THEN
ETAC APPENDED_ABSTRACT_BDS_R_W THEN
AITAC THEN
AXTAC THEN
LRTAC THEN
ETAC listTheory.MEM_APPEND THEN
SPLIT_ASM_DISJS_TAC THENL
[
 ETAC stateTheory.BD_TRANSFER_RAS_WAS_EQ THEN AITAC THEN QRLTAC THEN ETAC stateTheory.R_W_EQ THEN ALL_RLTAC THEN AIRTAC THEN STAC
 ,
 ETAC proof_obligations_cpu_l2Theory.APPENDED_BDS_R_W THEN ETAC stateTheory.R_W_EQ THEN RLTAC THEN RLTAC THEN AIRTAC THEN AIRTAC THEN STAC
]
QED

Theorem APPENDED_ABSTRACT_BDS_R_W_BD_TRANSFER_RAS_WAS_EQ_R_W_EQ_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA:
!device_characteristics memory1 memory2 device1 device2.
  APPENDED_ABSTRACT_BDS_R_W device_characteristics memory1 memory2 device1 device2 /\
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state /\
  R_W_EQ device_characteristics memory1 memory2 /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory1 device1
  ==>
  INVARIANT_UPDATE_BD_L2 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_UPDATE_BD_L2 THEN
INTRO_TAC THEN
LRTAC THEN LRTAC THEN LRTAC THEN LRTAC THEN
ETAC stateTheory.BD_TRANSFER_RAS_WAS_EQ THEN
AITAC THEN
QRLTAC THEN
ETAC stateTheory.R_W_EQ THEN
ALL_RLTAC THEN
ETAC APPENDED_ABSTRACT_BDS_R_W THEN
AITAC THEN
AIRTAC THEN
STAC
QED

Theorem APPENDED_ABSTRACT_BDS_R_W_BD_TRANSFER_RAS_WAS_EQ_R_W_EQ_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA:
!device_characteristics memory1 memory2 device1 device2.
  APPENDED_ABSTRACT_BDS_R_W device_characteristics memory1 memory2 device1 device2 /\
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state /\
  R_W_EQ device_characteristics memory1 memory2 /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory1 device1
  ==>
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_TRANSFER_DATA_L2 THEN
INTRO_TAC THEN
LRTAC THEN LRTAC THEN LRTAC THEN LRTAC THEN
ETAC stateTheory.BD_TRANSFER_RAS_WAS_EQ THEN
AITAC THEN
QRLTAC THEN
ETAC stateTheory.R_W_EQ THEN
ALL_RLTAC THEN
ETAC APPENDED_ABSTRACT_BDS_R_W THEN
AITAC THEN
AIRTAC THEN
STAC
QED

Theorem APPENDED_ABSTRACT_BDS_R_W_R_W_EQ_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA:
!device_characteristics memory1 memory2 device1 device2.
  APPENDED_ABSTRACT_BDS_R_W device_characteristics memory1 memory2 device1 device2 /\
  R_W_EQ device_characteristics memory1 memory2 /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory1 device1
  ==>
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_WRITE_BACK_BD_L2 THEN
INTRO_TAC THEN
ETAC stateTheory.R_W_EQ THEN
ETAC APPENDED_ABSTRACT_BDS_R_W THEN
AITAC THEN
AIRTAC THEN
STAC
QED

Theorem DEVICE_TRANSITION_L2_CPU_REGISTER_WRITE_MEMORY_WRITE_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA:
!INVARIANT_CPU device_characteristics cpu_transition cpu1 cpu2 cpu_dma_address_bytes memory1 memory2 device1 device2.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory1 device1 device1 /\
  INVARIANT_CPU memory1 cpu1 /\
  system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device1) (cpu_register_write_memory_write cpu_dma_address_bytes) (cpu2, memory2, device2) /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory1 device1 /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory1 device1
  ==>
  INVARIANT_FETCH_BD_L2 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
ITAC DEVICE_TRANSITION_L2_CPU_REGISTER_WRITE_MEMORY_IMPLIES_WRITE_APPENDED_ABSTRACT_BDS_R_W_LEMMA THEN
ITAC DEVICE_TRANSITION_L2_CPU_REGISTER_WRITE_MEMORY_WRITE_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA THEN
IRTAC DEVICE_TRANSITION_L2_CPU_REGISTER_WRITE_MEMORY_WRITE_IMPLIES_R_W_EQ_LEMMA THEN
IRTAC APPENDED_ABSTRACT_BDS_R_W_BD_TRANSFER_RAS_WAS_EQ_R_W_EQ_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA THEN
STAC
QED

Theorem DEVICE_TRANSITION_L2_CPU_REGISTER_WRITE_MEMORY_WRITE_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA:
!INVARIANT_CPU device_characteristics cpu_transition cpu1 cpu2 cpu_dma_address_bytes memory1 memory2 device1 device2.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory1 device1 device1 /\
  INVARIANT_CPU memory1 cpu1 /\
  system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device1) (cpu_register_write_memory_write cpu_dma_address_bytes) (cpu2, memory2, device2) /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory1 device1 /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory1 device1
  ==>
  INVARIANT_UPDATE_BD_L2 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
ITAC DEVICE_TRANSITION_L2_CPU_REGISTER_WRITE_MEMORY_IMPLIES_WRITE_APPENDED_ABSTRACT_BDS_R_W_LEMMA THEN
ITAC DEVICE_TRANSITION_L2_CPU_REGISTER_WRITE_MEMORY_WRITE_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA THEN
IRTAC DEVICE_TRANSITION_L2_CPU_REGISTER_WRITE_MEMORY_WRITE_IMPLIES_R_W_EQ_LEMMA THEN
IRTAC APPENDED_ABSTRACT_BDS_R_W_BD_TRANSFER_RAS_WAS_EQ_R_W_EQ_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA THEN
STAC
QED

Theorem DEVICE_TRANSITION_L2_CPU_REGISTER_WRITE_MEMORY_WRITE_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA:
!INVARIANT_CPU device_characteristics cpu_transition cpu1 cpu2 cpu_dma_address_bytes memory1 memory2 device1 device2.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory1 device1 device1 /\
  INVARIANT_CPU memory1 cpu1 /\
  system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device1) (cpu_register_write_memory_write cpu_dma_address_bytes) (cpu2, memory2, device2) /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory1 device1 /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory1 device1
  ==>
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
ITAC DEVICE_TRANSITION_L2_CPU_REGISTER_WRITE_MEMORY_IMPLIES_WRITE_APPENDED_ABSTRACT_BDS_R_W_LEMMA THEN
ITAC DEVICE_TRANSITION_L2_CPU_REGISTER_WRITE_MEMORY_WRITE_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA THEN
IRTAC DEVICE_TRANSITION_L2_CPU_REGISTER_WRITE_MEMORY_WRITE_IMPLIES_R_W_EQ_LEMMA THEN
IRTAC APPENDED_ABSTRACT_BDS_R_W_BD_TRANSFER_RAS_WAS_EQ_R_W_EQ_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA THEN
STAC
QED

Theorem DEVICE_TRANSITION_L2_CPU_REGISTER_WRITE_MEMORY_WRITE_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA:
!INVARIANT_CPU device_characteristics cpu_transition cpu1 cpu2 cpu_dma_address_bytes memory1 memory2 device1 device2.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory1 device1 device1 /\
  INVARIANT_CPU memory1 cpu1 /\
  system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device1) (cpu_register_write_memory_write cpu_dma_address_bytes) (cpu2, memory2, device2) /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory1 device1 /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory1 device1
  ==>
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
ITAC DEVICE_TRANSITION_L2_CPU_REGISTER_WRITE_MEMORY_IMPLIES_WRITE_APPENDED_ABSTRACT_BDS_R_W_LEMMA THEN
IRTAC DEVICE_TRANSITION_L2_CPU_REGISTER_WRITE_MEMORY_WRITE_IMPLIES_R_W_EQ_LEMMA THEN
IRTAC APPENDED_ABSTRACT_BDS_R_W_R_W_EQ_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA THEN
STAC
QED



Theorem DMA_REGISTER_WRITE_L2_IMPLIES_R_W_EQ_LEMMA:
!device_characteristics memory1 memory2 device1 device2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory1 device1 /\
  (device2, dma_address_bytes) = dma_register_write device_characteristics is_valid_l2 (SOME memory1) device1 cpu_address_bytes /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  R_W_EQ device_characteristics memory1 memory2
Proof
INTRO_TAC THEN
IRTAC DMA_REGISTER_WRITE_L2_WRITE_WRITABLE_MEMORY_LEMMA THEN
ITAC write_properties_lemmasTheory.WRITING_WRITABLE_MEMORY_PRESERVES_UNWRITABLE_MEMORY_LEMMA THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_READABLE_WRITABLE THEN
AIRTAC THEN
ETAC stateTheory.R_W_EQ THEN
STAC
QED

Theorem DMA_REGISTER_WRITE_L2_IMPLIES_INVARIANT_SCRATCHPAD_R_W_L2_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_SCRATCHPAD_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write cpu_address_bytes) cpu2 /\
  (device2, dma_address_bytes) = dma_register_write device_characteristics is_valid_l2 (SOME memory1) device1 cpu_address_bytes /\
  R_W_EQ device_characteristics memory1 memory2
  ==>
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory2 device2 /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_register_write THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 2 THEN
PTAC proof_obligations_cpu_l2Theory.PROOF_OBLIGATION_CPU_REGISTER_WRITE_SCRATCHPAD_R_W THEN
AITAC THEN
IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
CONJS_TAC THENL
[
 ETAC INVARIANT_SCRATCHPAD_R_L2 THEN
 LRTAC THEN
 ETAC proof_obligationsTheory.SCRATCHPAD_R_W THEN
 ETAC proof_obligationsTheory.SCRATCHPAD_R THEN
 LRTAC THEN
 LRTAC THEN
 RECORD_TAC THEN
 ETAC stateTheory.R_W_EQ THEN
 STAC
 ,
 ETAC INVARIANT_SCRATCHPAD_W_L2 THEN
 LRTAC THEN
 ETAC proof_obligationsTheory.SCRATCHPAD_R_W THEN
 ETAC proof_obligationsTheory.SCRATCHPAD_W THEN
 LRTAC THEN
 LRTAC THEN
 RECORD_TAC THEN
 ETAC stateTheory.R_W_EQ THEN
 STAC
]
QED

Theorem DEVICE_REGISTER_WRITE_L2_PRESERVES_INVARIANT_SCRATCHPAD_R_W_L2_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_SCRATCHPAD_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write cpu_address_bytes) cpu2 /\
  (device2, dma_address_bytes) = device_register_write_l2 device_characteristics memory1 device1 cpu_address_bytes /\
  memory2 = update_memory memory1 dma_address_bytes /\
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory1 device1 /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory1 device1
  ==>
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory2 device2 /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
PTAC l2Theory.device_register_write_l2 THEN
PTAC operationsTheory.device_register_write THENL
[
 ITAC DMA_REGISTER_WRITE_L2_IMPLIES_R_W_EQ_LEMMA THEN IRTAC DMA_REGISTER_WRITE_L2_IMPLIES_INVARIANT_SCRATCHPAD_R_W_L2_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
 RLTAC THEN
 CONJS_TAC THENL
 [
  ETAC INVARIANT_SCRATCHPAD_R_L2 THEN PTAC operationsTheory.function_register_write THEN LRTAC THEN RECORD_TAC THEN STAC
  ,
  ETAC INVARIANT_SCRATCHPAD_W_L2 THEN PTAC operationsTheory.function_register_write THEN LRTAC THEN RECORD_TAC THEN STAC
 ]
 ,
 EQ_PAIR_ASM_TAC THEN IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN STAC
]
QED

Theorem DEVICE_TRANSITION_L2_CPU_REGISTER_WRITE_MEMORY_WRITE_PRESERVES_INVARIANT_SCRATCHPAD_R_W_L2_LEMMA:
!INVARIANT_CPU device_characteristics cpu_transition cpu1 cpu2 cpu_dma_address_bytes memory1 memory2 device1 device2.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_SCRATCHPAD_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  system_transition cpu_transition (device_transition_l2 device_characteristics) (cpu1, memory1, device1) (cpu_register_write_memory_write cpu_dma_address_bytes) (cpu2, memory2, device2) /\
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory1 device1 /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory1 device1
  ==>
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory2 device2 /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory2 device2
Proof
REWRITE_TAC [operationsTheory.system_transitions_cases] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM operationsTheory.system_transition_labels_type_distinct] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [operationsTheory.system_transition_labels_type_11] THEN
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
INTRO_TAC THEN
AXTAC THEN
PAT_X_ASSUM “x = (y, z)” (fn thm => ASSUME_TAC (GSYM thm)) THEN
NRLTAC 7 THEN
AXTAC THEN
NRLTAC 3 THEN
WEAKEN_TAC is_disj THEN
IRTAC DEVICE_REGISTER_WRITE_L2_PRESERVES_INVARIANT_SCRATCHPAD_R_W_L2_LEMMA THEN
STAC
QED

val _ = export_theory();
