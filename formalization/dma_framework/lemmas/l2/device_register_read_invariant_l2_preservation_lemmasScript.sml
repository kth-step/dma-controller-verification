open HolKernel Parse boolLib bossLib helper_tactics;
open invariant_l2Theory;

val _ = new_theory "device_register_read_invariant_l2_preservation_lemmas";

Theorem DEVICE_REGISTER_READ_PRESERVES_DEFINED_CHANNELS_LEMMA:
!device_characteristics device1 device2 address_bytes dma_address_bytes.
  (device2, dma_address_bytes, MAP SND address_bytes) = device_register_read device_characteristics is_valid_l2 device1 (MAP FST address_bytes) /\
  DEFINED_CHANNELS device_characteristics device1
  ==>
  DEFINED_CHANNELS device_characteristics device2
Proof
INTRO_TAC THEN
ETAC stateTheory.DEFINED_CHANNELS THEN
ETAC stateTheory.VALID_CHANNELS THEN
PTAC operationsTheory.device_register_read THENL
[
 PTAC operationsTheory.dma_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 PTAC operationsTheory.function_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem DEVICE_REGISTER_READ_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA:
!device_characteristics memory device1 device2 address_bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BD_INTERPRETATION device_characteristics /\
  (device2, dma_address_bytes, MAP SND address_bytes) = device_register_read device_characteristics is_valid_l2 device1 (MAP FST address_bytes) /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_FETCH_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_FETCH_BD_L2 THEN
PTAC operationsTheory.device_register_read THENL
[
 INTRO_TAC THEN
 RLTAC THEN
 RLTAC THEN
 RLTAC THEN
 RW_HYPS_TAC stateTheory.schannel THEN
 PTAC operationsTheory.dma_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 2 THEN
 LRTAC THEN
 RECORD_TAC THEN
 RLTAC THEN
 ETAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BD_INTERPRETATION THEN
 AITAC THEN
 AITAC THEN
 AIRTAC THEN
 QLRTAC THEN
 STAC
 ,
 PTAC operationsTheory.function_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 RW_HYPS_TAC stateTheory.schannel THEN
 REWRITE_TAC [stateTheory.schannel] THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem DEVICE_REGISTER_READ_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA:
!device_characteristics memory device1 device2 address_bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BD_INTERPRETATION device_characteristics /\
  (device2, dma_address_bytes, MAP SND address_bytes) = device_register_read device_characteristics is_valid_l2 device1 (MAP FST address_bytes) /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_UPDATE_BD_L2 THEN
PTAC operationsTheory.device_register_read THENL
[
 INTRO_TAC THEN
 RLTAC THEN
 RLTAC THEN
 RLTAC THEN
 RW_HYPS_TAC stateTheory.schannel THEN
 PTAC operationsTheory.dma_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 2 THEN
 LRTAC THEN
 RECORD_TAC THEN
 RLTAC THEN
 ETAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BD_INTERPRETATION THEN
 AITAC THEN
 AITAC THEN
 AIRTAC THEN
 QLRTAC THEN
 STAC
 ,
 PTAC operationsTheory.function_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 RW_HYPS_TAC stateTheory.schannel THEN
 REWRITE_TAC [stateTheory.schannel] THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem DEVICE_REGISTER_READ_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA:
!device_characteristics memory device1 device2 address_bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BD_INTERPRETATION device_characteristics /\
  (device2, dma_address_bytes, MAP SND address_bytes) = device_register_read device_characteristics is_valid_l2 device1 (MAP FST address_bytes) /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device1
  ==>
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_TRANSFER_DATA_L2 THEN
PTAC operationsTheory.device_register_read THENL
[
 INTRO_TAC THEN
 RLTAC THEN
 RLTAC THEN
 RLTAC THEN
 RW_HYPS_TAC stateTheory.schannel THEN
 PTAC operationsTheory.dma_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 2 THEN
 LRTAC THEN
 RECORD_TAC THEN
 RLTAC THEN
 ETAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BD_INTERPRETATION THEN
 AITAC THEN
 AITAC THEN
 AIRTAC THEN
 QLRTAC THEN
 STAC
 ,
 PTAC operationsTheory.function_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 RW_HYPS_TAC stateTheory.schannel THEN
 REWRITE_TAC [stateTheory.schannel] THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem DEVICE_REGISTER_READ_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA:
!device_characteristics memory device1 device2 address_bytes dma_address_bytes.
  (device2, dma_address_bytes, MAP SND address_bytes) = device_register_read device_characteristics is_valid_l2 device1 (MAP FST address_bytes) /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_WRITE_BACK_BD_L2 THEN
PTAC operationsTheory.device_register_read THENL
[
 INTRO_TAC THEN
 PTAC operationsTheory.dma_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 2 THEN
 LRTAC THEN
 RW_HYPS_TAC stateTheory.schannel THEN
 RECORD_TAC THEN
 AITAC THEN
 STAC
 ,
 PTAC operationsTheory.function_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 RW_HYPS_TAC stateTheory.schannel THEN
 REWRITE_TAC [stateTheory.schannel] THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem DEVICE_REGISTER_READ_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA:
!device_characteristics memory device1 device2 address_bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_SCRATCHPAD device_characteristics /\
  (device2, dma_address_bytes, MAP SND address_bytes) = device_register_read device_characteristics is_valid_l2 device1 (MAP FST address_bytes) /\
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device1
  ==>
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_SCRATCHPAD_R_L2 THEN
PTAC operationsTheory.device_register_read THENL
[
 INTRO_TAC THEN
 PTAC operationsTheory.dma_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 2 THEN
 ETAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_READ_PRESERVES_SCRATCHPAD THEN
 AIRTAC THEN
 AIRTAC THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 PTAC operationsTheory.function_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 RW_HYPS_TAC stateTheory.schannel THEN
 REWRITE_TAC [stateTheory.schannel] THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem DEVICE_REGISTER_READ_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA:
!device_characteristics memory device1 device2 address_bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_SCRATCHPAD device_characteristics /\
  (device2, dma_address_bytes, MAP SND address_bytes) = device_register_read device_characteristics is_valid_l2 device1 (MAP FST address_bytes) /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device1
  ==>
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_SCRATCHPAD_W_L2 THEN
PTAC operationsTheory.device_register_read THENL
[
 INTRO_TAC THEN
 PTAC operationsTheory.dma_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 2 THEN
 ETAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_READ_PRESERVES_SCRATCHPAD THEN
 AIRTAC THEN
 AIRTAC THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 PTAC operationsTheory.function_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 RW_HYPS_TAC stateTheory.schannel THEN
 REWRITE_TAC [stateTheory.schannel] THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem DEVICE_TRANSITION_L2_DEVICE_REGISTER_READ_IMPLIES_DEVICE_REGISTER_READ_L2_LEMMA:
!device_characteristics device1 memory1 device2 cpu_address_bytes dma_address_bytes.
  device_transition_l2 device_characteristics device1 (memory1, device_register_read (cpu_address_bytes, dma_address_bytes)) device2
  ==>
  (device2, dma_address_bytes, MAP SND cpu_address_bytes) = device_register_read_l2 device_characteristics memory1 device1 (MAP FST cpu_address_bytes)
Proof
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
INTRO_TAC THEN
AXTAC THEN
NRLTAC 3 THEN
STAC
QED

Theorem DEVICE_TRANSITION_L2_EXTERNAL_BDS_APPENDED_IMPLIES_APPEND_EXTERNAL_ABSTRACT_BDS_L2_LEMMA:
!device_characteristics memory device1 device2.
  device_transition_l2 device_characteristics device1 (memory, external_bds_appended) device2
  ==>
  device2 = append_external_abstract_bds_l2 device_characteristics memory device1
Proof
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
STAC
QED

Theorem DEVICE_REGISTER_READ_L2_WRITE_WRITABLE_MEMORY_LEMMA:
!device_characteristics memory device1 device2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device1 /\
  (device2, dma_address_bytes, MAP SND cpu_address_bytes) = device_register_read_l2 device_characteristics memory device1 (MAP FST cpu_address_bytes)
  ==>
  EVERY (device_characteristics.dma_characteristics.W memory) (MAP FST dma_address_bytes)
Proof
INTRO_TAC THEN
PTAC l2Theory.device_register_read_l2 THEN
PTAC operationsTheory.device_register_read THENL
[
 PTAC operationsTheory.dma_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 3 THEN
 IRTAC write_properties_lemmasTheory.WRITE_REQUESTS_IMPLIES_WRITE_REQUEST_LEMMA THEN
 ETAC listTheory.EVERY_MEM THEN
 INTRO_TAC THEN
 IRTAC lists_lemmasTheory.MEM_ADDRESS_IMPLIES_MEM_ADDRESS_BYTES_LEMMA THEN
 AXTAC THEN
 AIRTAC THEN
 AXTAC THEN
 LRTAC THEN
 LRTAC THEN
 ETAC listTheory.MEM_FILTER THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_READ_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD THEN
 AITAC THEN
 IRTAC lists_lemmasTheory.MEM_ADDRESS_BYTE_IN_LIST1_IN_LIST2_IMPLIES_MEM_ADDRESS_LEMMA THEN
 PTAC INVARIANT_SCRATCHPAD_W_L2 THEN
 AIRTAC THEN
 ETAC listTheory.EVERY_MEM THEN
 AIRTAC THEN
 STAC
 ,
 PTAC operationsTheory.function_register_read THEN EQ_PAIR_ASM_TAC THEN LRTAC THEN REWRITE_TAC [listTheory.MAP, listTheory.EVERY_DEF]
 ,
 EQ_PAIR_ASM_TAC THEN LRTAC THEN REWRITE_TAC [listTheory.MAP, listTheory.EVERY_DEF] 
 ,
 EQ_PAIR_ASM_TAC THEN LRTAC THEN REWRITE_TAC [listTheory.MAP, listTheory.EVERY_DEF] 
]
QED

Theorem DEVICE_REGISTER_READ_L2_IMPLIES_R_W_EQ_LEMMA:
!device_characteristics memory1 memory2 device1 device2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory1 device1 /\
  (device2, dma_address_bytes, MAP SND cpu_address_bytes) = device_register_read_l2 device_characteristics memory1 device1 (MAP FST cpu_address_bytes) /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  R_W_EQ device_characteristics memory1 memory2
Proof
INTRO_TAC THEN
IRTAC DEVICE_REGISTER_READ_L2_WRITE_WRITABLE_MEMORY_LEMMA THEN
ITAC write_properties_lemmasTheory.WRITING_WRITABLE_MEMORY_PRESERVES_UNWRITABLE_MEMORY_LEMMA THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_READABLE_WRITABLE THEN
AIRTAC THEN
ETAC stateTheory.R_W_EQ THEN
STAC
QED

Theorem R_W_EQ_PRESERVES_INVARIANT_L2_LEMMA:
!device_characteristics memory1 memory2 device.
  R_W_EQ device_characteristics memory1 memory2 /\
  INVARIANT_L2 device_characteristics memory1 device
  ==>
  INVARIANT_L2 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC stateTheory.R_W_EQ THEN
ETAC INVARIANT_L2 THEN
CONJS_TAC THENL
[
 STAC
 ,
 ETAC INVARIANT_FETCH_BD_L2 THEN STAC
 ,
 ETAC INVARIANT_UPDATE_BD_L2 THEN STAC
 ,
 ETAC INVARIANT_TRANSFER_DATA_L2 THEN STAC
 ,
 ETAC INVARIANT_WRITE_BACK_BD_L2 THEN STAC
 ,
 ETAC INVARIANT_SCRATCHPAD_R_L2 THEN STAC
 ,
 ETAC INVARIANT_SCRATCHPAD_W_L2 THEN STAC
]
QED

Theorem INVARIANT_L2_IMPLIES_INVARIANT_SCRATCHPAD_W_L2_LEMMA:
!device_characteristics memory device.
  INVARIANT_L2 device_characteristics memory device
  ==>
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device
Proof
INTRO_TAC THEN
ETAC INVARIANT_L2 THEN
STAC
QED

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

Theorem REGISTER_READ_L2_IMPLIES_NEW_REQUESTS_EQ_FILTERED_REQUESTS_LEMMA:
!device_characteristics internal_state1 internal_state2 cpu_address_bytes new_requests.
  (internal_state2, MAP SND cpu_address_bytes, new_requests) = device_characteristics.dma_characteristics.register_read internal_state1 (MAP FST cpu_address_bytes)
  ==>
  new_requests = FILTER is_valid_l2 new_requests
Proof
REWRITE_TAC [FILTER_IS_VALID_L2_ID_LEMMA]
QED

Theorem DEVICE_TRANSITION_L2_DEVICE_REGISTER_READ_IMPLIES_PRESERVATION_OR_REGISTER_READ_LEMMA:
!device_characteristics device1 device2 memory cpu_address_bytes dma_address_bytes.
  device_transition_l2 device_characteristics device1 (memory, device_register_read (cpu_address_bytes, dma_address_bytes)) device2
  ==>
  CHANNELS_EQ device1 device2 /\ INTERNAL_STATES_EQ device1 device2 /\ dma_address_bytes = [] \/
  ?internal_state new_requests write_requests.
    (internal_state, MAP SND cpu_address_bytes, new_requests) = device_characteristics.dma_characteristics.register_read device1.dma_state.internal_state (MAP FST cpu_address_bytes) /\
    write_requests = FILTER WRITE_REQUEST new_requests /\
    dma_address_bytes = FLAT (MAP request_to_address_bytes write_requests) /\
    CHANNELS_EQ device1 device2 /\
    device2.dma_state.internal_state = internal_state
Proof
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
INTRO_TAC THEN
AXTAC THEN
NRLTAC 3 THEN
WEAKEN_TAC is_disj THEN
PTAC l2Theory.device_register_read_l2 THEN
PTAC operationsTheory.device_register_read THENL
[
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 PTAC operationsTheory.dma_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 NLRTAC 3 THEN
 ITAC REGISTER_READ_L2_IMPLIES_NEW_REQUESTS_EQ_FILTERED_REQUESTS_LEMMA THEN
 RLTAC THEN
 LRTAC THEN
 ETAC stateTheory.CHANNELS_EQ THEN
 PAXTAC THEN
 ALL_LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
 PTAC operationsTheory.function_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 CONJS_TAC THEN TRY STAC THENL
 [
  ETAC stateTheory.CHANNELS_EQ THEN RLTAC THEN RECORD_TAC THEN STAC
  ,
  ETAC stateTheory.INTERNAL_STATES_EQ THEN RLTAC THEN RECORD_TAC THEN STAC
 ]
 ,
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN REWRITE_TAC [stateTheory.CHANNELS_EQ, stateTheory.INTERNAL_STATES_EQ] THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN REWRITE_TAC [stateTheory.CHANNELS_EQ, stateTheory.INTERNAL_STATES_EQ] THEN EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem CHANNELS_EQ_PRESERVES_DEFINED_CHANNELS_LEMMA:
!device_characteristics device1 device2.
  CHANNELS_EQ device1 device2 /\
  DEFINED_CHANNELS device_characteristics device1
  ==>
  DEFINED_CHANNELS device_characteristics device2
Proof
INTRO_TAC THEN
ETAC stateTheory.CHANNELS_EQ THEN
ETAC stateTheory.DEFINED_CHANNELS THEN
STAC
QED

Theorem DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ_REFL_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (memory : 'interconnect_address_width memory_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ device_characteristics memory memory device
Proof
REPEAT GEN_TAC THEN
PTAC proof_obligations_cpu_l1Theory.DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
ETAC stateTheory.R_W_EQ THEN
STAC
QED

Theorem MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W_REFL_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (memory : 'interconnect_address_width memory_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W device_characteristics device.dma_state.internal_state memory memory
Proof
REPEAT GEN_TAC THEN
PTAC proof_obligationsTheory.MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W THEN
INTRO_TAC THEN
ALL_LRTAC THEN
EXISTS_EQ_TAC THEN
Q.EXISTS_TAC ‘[]’ THEN
REWRITE_TAC [listTheory.APPEND_NIL, listTheory.MEM]
QED

Theorem INTERNAL_STATES_CHANNELS_EQ_PRESERVES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (memory : 'interconnect_address_width memory_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  INTERNAL_STATES_EQ device1 device2 /\
  CHANNELS_EQ device1 device2 /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device1 device1
  ==>
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device2 device2
Proof
REWRITE_TAC [stateTheory.INTERNAL_STATES_EQ, stateTheory.CHANNELS_EQ, stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ, stateTheory.schannel] THEN
INTRO_TAC THEN
STAC
QED

Theorem INTERNAL_STATES_CHANNELS_EQ_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA:
!device_characteristics memory device1 device2.
  INTERNAL_STATES_EQ device1 device2 /\
  CHANNELS_EQ device1 device2 /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_FETCH_BD_L2 device_characteristics memory device2
Proof
REWRITE_TAC [stateTheory.INTERNAL_STATES_EQ, stateTheory.CHANNELS_EQ, INVARIANT_FETCH_BD_L2, stateTheory.schannel] THEN
INTRO_TAC THEN
NRLTAC 2 THEN
STAC
QED

Theorem INTERNAL_STATES_CHANNELS_EQ_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA:
!device_characteristics memory device1 device2.
  INTERNAL_STATES_EQ device1 device2 /\
  CHANNELS_EQ device1 device2 /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device2
Proof
REWRITE_TAC [stateTheory.INTERNAL_STATES_EQ, stateTheory.CHANNELS_EQ, INVARIANT_UPDATE_BD_L2, stateTheory.schannel] THEN
INTRO_TAC THEN
NRLTAC 2 THEN
STAC
QED

Theorem INTERNAL_STATES_CHANNELS_EQ_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA:
!device_characteristics memory device1 device2.
  INTERNAL_STATES_EQ device1 device2 /\
  CHANNELS_EQ device1 device2 /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device1
  ==>
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device2
Proof
REWRITE_TAC [stateTheory.INTERNAL_STATES_EQ, stateTheory.CHANNELS_EQ, INVARIANT_TRANSFER_DATA_L2, stateTheory.schannel] THEN
INTRO_TAC THEN
NRLTAC 2 THEN
STAC
QED

Theorem INTERNAL_STATES_CHANNELS_EQ_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA:
!device_characteristics memory device1 device2.
  INTERNAL_STATES_EQ device1 device2 /\
  CHANNELS_EQ device1 device2 /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device2
Proof
REWRITE_TAC [stateTheory.INTERNAL_STATES_EQ, stateTheory.CHANNELS_EQ, INVARIANT_WRITE_BACK_BD_L2, stateTheory.schannel] THEN
INTRO_TAC THEN
NRLTAC 2 THEN
STAC
QED

Theorem INTERNAL_STATES_EQ_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA:
!device_characteristics memory device1 device2.
  INTERNAL_STATES_EQ device1 device2 /\
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device1
  ==>
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device2
Proof
REWRITE_TAC [stateTheory.INTERNAL_STATES_EQ, INVARIANT_SCRATCHPAD_R_L2] THEN
INTRO_TAC THEN
RLTAC THEN
STAC
QED

Theorem INTERNAL_STATES_EQ_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA:
!device_characteristics memory device1 device2.
  INTERNAL_STATES_EQ device1 device2 /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device1
  ==>
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device2
Proof
REWRITE_TAC [stateTheory.INTERNAL_STATES_EQ, INVARIANT_SCRATCHPAD_W_L2] THEN
INTRO_TAC THEN
RLTAC THEN
STAC
QED

Theorem NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W_REFL_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (memory : 'interconnect_address_width memory_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W device_characteristics device memory memory
Proof
REPEAT GEN_TAC THEN
PTAC proof_obligations_cpu_l2Theory.NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W THEN
REWRITE_TAC []
QED

Theorem ABSTRACT_CONCRETE_BDS_TO_FETCH_INTERNAL_STATE_CHANNELS_EQ_EXTERNAL_BDS_APPENDED_PRESERVES_INVARIANT_L2_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (memory : 'interconnect_address_width memory_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device1 device1 /\
  INTERNAL_STATES_EQ device1 device /\
  CHANNELS_EQ device1 device /\
  device_transition_l2 device_characteristics device (memory, external_bds_appended) device2 /\
  INVARIANT_L2 device_characteristics memory device1
  ==>
  INVARIANT_L2 device_characteristics memory device2
Proof
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
RLTAC THEN
ETAC INVARIANT_L2 THEN
ASSUME_TAC DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ_REFL_LEMMA THEN
ASSUME_TAC MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W_REFL_LEMMA THEN
ITAC INTERNAL_STATES_CHANNELS_EQ_PRESERVES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA THEN
CONJS_TAC THENL
[
 IRTAC CHANNELS_EQ_PRESERVES_DEFINED_CHANNELS_LEMMA THEN 
 IRTAC append_external_bds_invariant_l2_preservation_lemmasTheory.APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_DEFINED_CHANNELS_LEMMA THEN
 STAC
 ,
 IRTAC INTERNAL_STATES_CHANNELS_EQ_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA THEN
 MATCH_MP_TAC append_external_bds_invariant_l2_preservation_lemmasTheory.APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA THEN
 PAXTAC THEN
 STAC
 ,
 IRTAC INTERNAL_STATES_CHANNELS_EQ_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA THEN
 MATCH_MP_TAC append_external_bds_invariant_l2_preservation_lemmasTheory.APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA THEN
 PAXTAC THEN
 STAC
 ,
 IRTAC INTERNAL_STATES_CHANNELS_EQ_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA THEN
 MATCH_MP_TAC append_external_bds_invariant_l2_preservation_lemmasTheory.APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA THEN
 PAXTAC THEN
 STAC
 ,
 IRTAC INTERNAL_STATES_CHANNELS_EQ_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA THEN
 MATCH_MP_TAC append_external_bds_invariant_l2_preservation_lemmasTheory.APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA THEN
 PAXTAC THEN
 STAC
 ,
 ASSUME_TAC NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W_REFL_LEMMA THEN
 IRTAC INTERNAL_STATES_EQ_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA THEN
 MATCH_MP_TAC append_external_bds_invariant_l2_preservation_lemmasTheory.APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA THEN
 PAXTAC THEN
 STAC
 ,
 ASSUME_TAC NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W_REFL_LEMMA THEN
 IRTAC INTERNAL_STATES_EQ_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA THEN
 MATCH_MP_TAC append_external_bds_invariant_l2_preservation_lemmasTheory.APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA THEN
 PAXTAC THEN
 STAC
]
QED

Theorem R_W_EQ_IMPLIES_DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (memory1 : 'interconnect_address_width memory_type)
 (memory2 : 'interconnect_address_width memory_type).
  R_W_EQ device_characteristics memory1 memory2
  ==>
  !(device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
    DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ device_characteristics memory1 memory2 device
Proof
INTRO_TAC THEN
GEN_TAC THEN
ETAC proof_obligations_cpu_l1Theory.DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
STAC
QED

Theorem ALL_BDS_TO_FETCH_CHANNELS_EQ_PRESERVES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics memory device1 device2.
  ALL_BDS_TO_FETCH_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state /\
  CHANNELS_EQ device1 device2 /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device1 device1
  ==>
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device2 device2
Proof
REWRITE_TAC [stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ, stateTheory.ALL_BDS_TO_FETCH_EQ, stateTheory.CHANNELS_EQ, stateTheory.schannel] THEN
INTRO_TAC THEN
INTRO_TAC THEN
AITAC THEN
AIRTAC THEN
STAC
QED

Theorem R_W_EQ_IMPLIES_NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (memory1 : 'interconnect_address_width memory_type)
 (memory2 : 'interconnect_address_width memory_type).
  R_W_EQ device_characteristics memory1 memory2
  ==>
  !(device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
    NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W device_characteristics device memory1 memory2
Proof
REWRITE_TAC [stateTheory.R_W_EQ, proof_obligations_cpu_l2Theory.NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W] THEN
INTRO_TAC THEN
STAC
QED

Theorem ABSTRACT_CONCRETE_BDS_TO_FETCH_R_W_APPENDS_EXTERNAL_CONCRETE_BDS_CHANNELS_EQ_PRESERVES_INVARIANT_L2_LEMMA:
!device_characteristics memory1 memory2 device1 device device2.
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory1 device1 device1 /\
  R_W_EQ device_characteristics memory1 memory2 /\
  MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W device_characteristics device.dma_state.internal_state memory1 memory2 /\
  ALL_BDS_TO_FETCH_EQ device_characteristics device1.dma_state.internal_state device.dma_state.internal_state /\
  CHANNELS_EQ device1 device /\
  device_transition_l2 device_characteristics device (memory2, external_bds_appended) device2 /\
  INVARIANT_L2 device_characteristics memory1 device
  ==>
  INVARIANT_L2 device_characteristics memory2 device2
Proof
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
RLTAC THEN
ITAC R_W_EQ_PRESERVES_INVARIANT_L2_LEMMA THEN
ITAC R_W_EQ_IMPLIES_DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ_LEMMA THEN
IRTAC R_W_EQ_IMPLIES_NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W_LEMMA THEN
ETAC INVARIANT_L2 THEN
CONJS_TAC THENL
[
 IRTAC CHANNELS_EQ_PRESERVES_DEFINED_CHANNELS_LEMMA THEN 
 IRTAC append_external_bds_invariant_l2_preservation_lemmasTheory.APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_DEFINED_CHANNELS_LEMMA THEN
 STAC
 ,
 IRTAC ALL_BDS_TO_FETCH_CHANNELS_EQ_PRESERVES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA THEN
 MATCH_MP_TAC append_external_bds_invariant_l2_preservation_lemmasTheory.APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA THEN
 PAXTAC THEN
 STAC
 ,
 IRTAC INTERNAL_STATES_CHANNELS_EQ_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA THEN
 MATCH_MP_TAC append_external_bds_invariant_l2_preservation_lemmasTheory.APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA THEN
 PAXTAC THEN
 STAC
 ,
 IRTAC INTERNAL_STATES_CHANNELS_EQ_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA THEN
 MATCH_MP_TAC append_external_bds_invariant_l2_preservation_lemmasTheory.APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA THEN
 PAXTAC THEN
 STAC
 ,
 IRTAC INTERNAL_STATES_CHANNELS_EQ_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA THEN
 MATCH_MP_TAC append_external_bds_invariant_l2_preservation_lemmasTheory.APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA THEN
 PAXTAC THEN
 STAC
 ,
 ASSUME_TAC NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W_REFL_LEMMA THEN
 MATCH_MP_TAC append_external_bds_invariant_l2_preservation_lemmasTheory.APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA THEN
 PAXTAC THEN
 STAC
 ,
 ASSUME_TAC NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W_REFL_LEMMA THEN
 MATCH_MP_TAC append_external_bds_invariant_l2_preservation_lemmasTheory.APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA THEN
 PAXTAC THEN
 STAC
]
QED

Theorem REGISTER_READ_IMPLIES_ALL_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics internal_state1 internal_state2 cpu_address_bytes new_requests.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  (internal_state2, MAP SND cpu_address_bytes, new_requests) = device_characteristics.dma_characteristics.register_read internal_state1 (MAP FST cpu_address_bytes)
  ==>
  ALL_BDS_TO_FETCH_EQ device_characteristics internal_state1 internal_state2
Proof
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH THEN
AIRTAC THEN
REWRITE_TAC [stateTheory.ALL_BDS_TO_FETCH_EQ] THEN
INTRO_TAC THEN
AIRTAC THEN
STAC
QED

Theorem REGISTER_READ_IMPLIES_SCRATCHPAD_ADDRESSES_EQ_LEMMA:
!device_characteristics internal_state1 internal_state2 cpu_address_bytes new_requests.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_SCRATCHPAD device_characteristics /\
  (internal_state2, MAP SND cpu_address_bytes, new_requests) = device_characteristics.dma_characteristics.register_read internal_state1 (MAP FST cpu_address_bytes)
  ==>
  SCRATCHPAD_ADDRESSES_EQ device_characteristics internal_state1 internal_state2
Proof
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_READ_PRESERVES_SCRATCHPAD THEN
AIRTAC THEN
REWRITE_TAC [stateTheory.SCRATCHPAD_ADDRESSES_EQ] THEN
STAC
QED

val _ = export_theory();
