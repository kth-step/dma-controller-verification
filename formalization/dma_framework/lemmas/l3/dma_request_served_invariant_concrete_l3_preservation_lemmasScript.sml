open HolKernel Parse boolLib bossLib helper_tactics;
open l3Theory invariant_l3Theory;

val _ = new_theory "dma_request_served_invariant_concrete_l3_preservation_lemmas";

Theorem DMA_PENDING_REQUEST_SERVED_L3_PRESERVES_INVARIANT_BDS_TO_FETCH_DISJOINT_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory
 (serviced_request : 8 word list # ('interconnect_address_width, 'tag_width) interconnect_request_type).
  device2 = dma_request_served_l3 device_characteristics device1 serviced_request /\
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device1
  ==>
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC l3Theory.dma_request_served_l3 THEN
ETAC invariant_l3Theory.INVARIANT_BDS_TO_FETCH_DISJOINT THEN
ITAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN
LRTAC THEN
STAC
QED

Theorem DMA_PENDING_REQUEST_SERVED_L3_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory
 (serviced_request : 8 word list # ('interconnect_address_width, 'tag_width) interconnect_request_type).
  device2 = dma_request_served_l3 device_characteristics device1 serviced_request /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device1
  ==>
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC l3Theory.dma_request_served_l3 THEN
ETAC invariant_l3Theory.NO_MEMORY_WRITES_TO_BDS THEN
ITAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN
LRTAC THEN
INTRO_TAC THEN
ITAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_NOT_ADDING_REQUESTS_LEMMA THEN
IRTAC internal_operation_lemmasTheory.LIST1_IN_LIST2_PRESERVES_REQUEST_TO_WRITE_ADDRESSES_LEMMA THEN
AIRTAC THEN
IRTAC collect_dma_state_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_PIPELINE_BDS_LEMMA THEN
STAC
QED

Theorem DMA_PENDING_REQUEST_SERVED_L3_PRESERVES_NOT_DMA_BDS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory
 (serviced_request : 8 word list # ('interconnect_address_width, 'tag_width) interconnect_request_type).
  device2 = dma_request_served_l3 device_characteristics device1 serviced_request /\
  NOT_DMA_BDS device_characteristics memory device1
  ==>
  NOT_DMA_BDS device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC l3Theory.dma_request_served_l3 THEN
ETAC invariant_l3Theory.NOT_DMA_BDS THEN
INTRO_TAC THEN
PAT_X_ASSUM “!x.P” (fn thm => MATCH_MP_TAC thm) THEN
INST_EXISTS_TAC THEN
CONJS_TAC THEN TRY STAC THENL
[
 IRTAC invariant_l3_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_CHANNEL_BDS_LEMMA THEN QLRTAC THEN STAC
 ,
 IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN STAC
 ,
 PAT_X_ASSUM “VALID_CHANNEL_ID device_characteristics channel_id_dma_bd” (fn thm => ALL_TAC) THEN
 IRTAC invariant_l3_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_CHANNEL_BDS_LEMMA THEN QLRTAC THEN STAC
]
QED

(*
Theorem DMA_PENDING_REQUEST_SERVED_L3_PRESERVES_NOT_DMA_SCRATCHPAD_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory
 (serviced_request : 8 word list # ('interconnect_address_width, 'tag_width) interconnect_request_type).
  device2 = dma_request_served_l3 device_characteristics device1 serviced_request /\
  NOT_DMA_SCRATCHPAD device_characteristics memory device1
  ==>
  NOT_DMA_SCRATCHPAD device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC l3Theory.dma_request_served_l3 THEN
ETAC invariant_l3Theory.NOT_DMA_SCRATCHPAD THEN
INTRO_TAC THEN
PAT_X_ASSUM “!x.P” (fn thm => MATCH_MP_TAC thm) THEN
INST_EXISTS_TAC THEN
CONJS_TAC THEN TRY STAC THENL
[
 IRTAC invariant_l3_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_CHANNEL_BDS_LEMMA THEN QLRTAC THEN STAC
 ,
 IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN STAC
 ,
 IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN STAC
]
QED
*)

Theorem DMA_PENDING_REQUEST_SERVED_L3_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (serviced_request : 8 word list # ('interconnect_address_width, 'tag_width) interconnect_request_type).
  device2 = dma_request_served_l3 device_characteristics device1 serviced_request /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device1
  ==>
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device2
Proof
INTRO_TAC THEN
PTAC l3Theory.dma_request_served_l3 THEN
ETAC invariant_l3Theory.MEMORY_WRITES_PRESERVES_BDS_TO_FETCH THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_NOT_ADDING_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA THEN
ETAC stateTheory.READ_REQUESTS THEN
ETAC listTheory.EVERY_MEM THEN
INTRO_TAC THEN
IRTAC lists_lemmasTheory.LIST1_IN_LIST2_MEM_LIST1_IMPLIES_MEM_LIST2_LEMMA THEN
AIRTAC THEN
STAC
QED

Theorem DMA_PENDING_REQUEST_SERVED_L3_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory
 address_bytes tag.
  MAP memory (MAP FST address_bytes) = MAP SND address_bytes /\
  MEM (request_read (MAP FST address_bytes) tag) (dma_pending_requests_l3 device_characteristics device1) /\
  device2 = dma_request_served_l3 device_characteristics device1 (MAP SND address_bytes, request_read (MAP FST address_bytes) tag) /\
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device1 /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device1
  ==>
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC l3Theory.dma_request_served_l3 THEN
ETAC invariant_l3Theory.INVARIANT_EXTERNAL_FETCH_BD_REPLY THEN
INTRO_TAC THEN
ITAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN
LRTAC THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
AITAC THEN
PTAC operationsTheory.APPENDED_REPLY_REMOVED_REQUEST_CHANNEL THEN
ETAC stateTheory.schannel THEN
ETAC stateTheory.schannel THEN
IRTAC internal_operation_lemmasTheory.APPEND_REPLY_REMOVE_REQUEST_CHANNEL_MATCHES_OR_PRESERVES_FETCHING_BD_REPLY_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 LRTAC THEN
 ETAC optionTheory.SOME_11 THEN
 EQ_PAIR_ASM_TAC THEN
 ETAC invariant_l3Theory.FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES THEN
 AIRTAC THEN
 LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 STAC
 ,
 LRTAC THEN AIRTAC THEN STAC
]
QED

Theorem DMA_PENDING_REQUEST_SERVED_L3_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory
 (serviced_request : 8 word list # ('interconnect_address_width, 'tag_width) interconnect_request_type).
  device2 = dma_request_served_l3 device_characteristics device1 serviced_request /\
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device1
  ==>
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC l3Theory.dma_request_served_l3 THEN
ETAC invariant_l3Theory.FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES THEN
INTRO_TAC THEN
ITAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN
LRTAC THEN
ITAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
AITAC THEN
ETAC (GSYM stateTheory.schannel) THEN
PTAC operationsTheory.APPENDED_REPLY_REMOVED_REQUEST_CHANNEL THEN
ITAC internal_operation_lemmasTheory.APPEND_REPLY_REMOVE_REQUEST_CHANNEL_PRESERVES_OR_REMOVES_FETCHING_BD_REQUEST_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AIRTAC THEN STAC
 ,
 LRTAC THEN HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
]
QED



Theorem DMA_REQUESTS_SERVED_L3_READ_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory
 address_bytes tag.
  MAP memory (MAP FST address_bytes) = MAP SND address_bytes /\
  MEM (request_read (MAP FST address_bytes) tag) (dma_pending_requests_l3 device_characteristics device1) /\
  device2 = dma_request_served_l3 device_characteristics device1 (MAP SND address_bytes, request_read (MAP FST address_bytes) tag) /\
  INVARIANT_CONCRETE_L3 device_characteristics memory device1
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_CONCRETE_L3 THEN
ITAC DMA_PENDING_REQUEST_SERVED_L3_PRESERVES_INVARIANT_BDS_TO_FETCH_DISJOINT_LEMMA THEN
ITAC DMA_PENDING_REQUEST_SERVED_L3_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA THEN
ITAC DMA_PENDING_REQUEST_SERVED_L3_PRESERVES_NOT_DMA_BDS_LEMMA THEN
(*ITAC DMA_PENDING_REQUEST_SERVED_L3_PRESERVES_NOT_DMA_SCRATCHPAD_LEMMA THEN*)
ITAC DMA_PENDING_REQUEST_SERVED_L3_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA THEN
ITAC DMA_PENDING_REQUEST_SERVED_L3_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA THEN
ITAC DMA_PENDING_REQUEST_SERVED_L3_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA THEN
STAC
QED





Theorem DMA_REQUEST_SERVED_L3_WRITE_PRESERVES_INVARIANT_BDS_TO_FETCH_DISJOINT_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory1 memory2
 address_bytes tag
 (serviced_request : 8 word list # ('interconnect_address_width, 'tag_width) interconnect_request_type).
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device1 /\
  memory2 = update_memory memory1 address_bytes /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l3 device_characteristics device1) /\
  device2 = dma_request_served_l3 device_characteristics device1 serviced_request /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device1 /\
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory1 device1
  ==>
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory2 device2
Proof
INTRO_TAC THEN
PTAC l3Theory.dma_request_served_l3 THEN
ITAC (ONCE_REWRITE_RULE [invariant_l3_lemmasTheory.BDS_TO_FETCH_EQ_INTERNAL_STATE_SYM_LEMMA] (REWRITE_RULE [GSYM invariant_l3_lemmasTheory.BDS_TO_FETCH_EQ_INTERNAL_STATE] invariant_l3_lemmasTheory.NO_MEMORY_WRITES_BDS_TO_FETCH_PRESERVES_BDS_TO_FETCH_LEMMA)) THEN
ETAC invariant_l3Theory.INVARIANT_BDS_TO_FETCH_DISJOINT THEN
INTRO_TAC THEN
AITAC THEN
ETAC invariant_l3_lemmasTheory.BDS_TO_FETCH_EQ_INTERNAL_STATE THEN
AIRTAC THEN
RLTAC THEN
ITAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN
RLTAC THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_L3_WRITE_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory1 memory2 address_bytes tag.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device1 /\
  memory2 = update_memory memory1 address_bytes /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l3 device_characteristics device1) /\
  device2 = dma_request_served_l3 device_characteristics device1 ([], request_write address_bytes tag) /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device1
  ==>
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory2 device2
Proof
INTRO_TAC THEN
ETAC dma_request_served_l3 THEN
ITAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN
ETAC dma_request_served_l3 THEN
ITAC (ONCE_REWRITE_RULE [invariant_l3_lemmasTheory.BDS_TO_FETCH_EQ_INTERNAL_STATE_SYM_LEMMA] (REWRITE_RULE [GSYM invariant_l3_lemmasTheory.BDS_TO_FETCH_EQ_INTERNAL_STATE] invariant_l3_lemmasTheory.NO_MEMORY_WRITES_BDS_TO_FETCH_PRESERVES_BDS_TO_FETCH_LEMMA)) THEN
RLTAC THEN
IRTAC DMA_PENDING_REQUEST_SERVED_L3_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA THEN
FIRTAC invariant_l3_lemmasTheory.BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_L3_WRITE_PRESERVES_NOT_DMA_BDS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory1 memory2 address_bytes tag.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device1 /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device1 /\
  memory2 = update_memory memory1 address_bytes /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l3 device_characteristics device1) /\
  device2 = dma_request_served_l3 device_characteristics device1 ([], request_write address_bytes tag) /\
  NOT_DMA_BDS device_characteristics memory1 device1
  ==>
  NOT_DMA_BDS device_characteristics memory2 device2
Proof
INTRO_TAC THEN
ITAC (REWRITE_RULE [GSYM l3Theory.dma_request_served_l3] dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA) THEN
ITAC (ONCE_REWRITE_RULE [invariant_l3_lemmasTheory.BDS_TO_FETCH_EQ_INTERNAL_STATE_SYM_LEMMA] (REWRITE_RULE [GSYM invariant_l3_lemmasTheory.BDS_TO_FETCH_EQ_INTERNAL_STATE] invariant_l3_lemmasTheory.NO_MEMORY_WRITES_BDS_TO_FETCH_PRESERVES_BDS_TO_FETCH_LEMMA)) THEN
RLTAC THEN
IRTAC DMA_PENDING_REQUEST_SERVED_L3_PRESERVES_NOT_DMA_BDS_LEMMA THEN
IRTAC invariant_l3_lemmasTheory.BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_NOT_DMA_BDS_LEMMA THEN
STAC
QED

(*
Theorem DMA_REQUEST_SERVED_L3_WRITE_PRESERVES_NOT_DMA_SCRATCHPAD_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory1 memory2 address_bytes tag.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device1 /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device1 /\
  memory2 = update_memory memory1 address_bytes /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l3 device_characteristics device1) /\
  device2 = dma_request_served_l3 device_characteristics device1 ([], request_write address_bytes tag) /\
  NOT_DMA_SCRATCHPAD device_characteristics memory1 device1
  ==>
  NOT_DMA_SCRATCHPAD device_characteristics memory2 device2
Proof
INTRO_TAC THEN
ITAC (REWRITE_RULE [GSYM l3Theory.dma_request_served_l3] dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA) THEN
ITAC (ONCE_REWRITE_RULE [invariant_l3_lemmasTheory.BDS_TO_FETCH_EQ_INTERNAL_STATE_SYM_LEMMA] (REWRITE_RULE [GSYM invariant_l3_lemmasTheory.BDS_TO_FETCH_EQ_INTERNAL_STATE] invariant_l3_lemmasTheory.NO_MEMORY_WRITES_BDS_TO_FETCH_PRESERVES_BDS_TO_FETCH_LEMMA)) THEN
RLTAC THEN
IRTAC DMA_PENDING_REQUEST_SERVED_L3_PRESERVES_NOT_DMA_SCRATCHPAD_LEMMA THEN
IRTAC invariant_l3_lemmasTheory.BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_NOT_DMA_SCRATCHPAD_LEMMA THEN
STAC
QED
*)

Theorem DMA_REQUEST_SERVED_L3_WRITE_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory1 memory2 address_bytes tag.
  memory2 = update_memory memory1 address_bytes /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l3 device_characteristics device1) /\
  device2 = dma_request_served_l3 device_characteristics device1 ([], request_write address_bytes tag) /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device1
  ==>
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device2
Proof
INTRO_TAC THEN
ITAC DMA_PENDING_REQUEST_SERVED_L3_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_L3_WRITE_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory1 memory2 address_bytes tag.
  PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ device_characteristics /\
  PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS device_characteristics /\
  memory2 = update_memory memory1 address_bytes /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l3 device_characteristics device1) /\
  device2 = dma_request_served_l3 device_characteristics device1 ([], request_write address_bytes tag) /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device1 /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device1 /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory1 device1
  ==>
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory2 device2
Proof
INTRO_TAC THEN
ETAC l3Theory.dma_pending_requests_l3 THEN
ETAC l3Theory.dma_request_served_l3 THEN
ETAC invariant_l3Theory.INVARIANT_EXTERNAL_FETCH_BD_REPLY THEN
INTRO_TAC THEN
ITAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN
LRTAC THEN
ITAC dma_request_served_lemmasTheory.DMA_WRITE_REQUEST_SERVED_PRESERVED_PENDING_ACCESSES_REPLIES_FETCHING_BD_LEMMA THEN
AITAC THEN (CONJS_TAC THEN TRY STAC) THEN
IRTAC invariant_l3_lemmasTheory.DMA_PENDING_WRITE_REQUEST_PRESERVES_BD_TO_FETCH_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_L3_WRITE_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory1 memory2 address_bytes tag.
  memory2 = update_memory memory1 address_bytes /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l3 device_characteristics device1) /\
  device2 = dma_request_served_l3 device_characteristics device1 ([], request_write address_bytes tag) /\
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory1 device1
  ==>
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory2 device2
Proof
INTRO_TAC THEN
ETAC FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES THEN
INTRO_TAC THEN
ETAC l3Theory.dma_request_served_l3 THEN
ITAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN
LRTAC THEN
ITAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_NOT_REMOVED_IMPLIES_PRESTATE_REQUEST_LEMMA THEN
AIRTAC THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_L3_WRITE_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory1 memory2 address_bytes tag.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics /\
  PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ device_characteristics /\
  PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS device_characteristics /\
  memory2 = update_memory memory1 address_bytes /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l3 device_characteristics device1) /\
  device2 = dma_request_served_l3 device_characteristics device1 ([], request_write address_bytes tag) /\
  INVARIANT_CONCRETE_L3 device_characteristics memory1 device1
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_CONCRETE_L3 THEN
ITAC DMA_REQUEST_SERVED_L3_WRITE_PRESERVES_INVARIANT_BDS_TO_FETCH_DISJOINT_LEMMA THEN
ITAC DMA_REQUEST_SERVED_L3_WRITE_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA THEN
ITAC DMA_REQUEST_SERVED_L3_WRITE_PRESERVES_NOT_DMA_BDS_LEMMA THEN
(*ITAC DMA_REQUEST_SERVED_L3_WRITE_PRESERVES_NOT_DMA_SCRATCHPAD_LEMMA THEN*)
ITAC DMA_REQUEST_SERVED_L3_WRITE_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA THEN
ITAC DMA_REQUEST_SERVED_L3_WRITE_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA THEN
ITAC DMA_REQUEST_SERVED_L3_WRITE_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA THEN
STAC
QED

val _ = export_theory();

