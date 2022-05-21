open HolKernel Parse boolLib bossLib helper_tactics;
open invariant_l3Theory proof_obligationsTheory proof_obligations_cpu_l2Theory fetching_bd_lemmasTheory;

val _ = new_theory "invariant_l3_lemmas";

Theorem PROOF_OBLIGATION_CPU_APPENDS_EXTERNAL_CONCRETE_BDS_IMPlIES_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_LEMMA:
!device_characteristics INVARIANT_CPU cpu_transition memory1 memory2 cpu1 cpu2 address_bytes device.
  PROOF_OBLIGATION_CPU_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  EXTERNAL_BDS device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_L3 device_characteristics memory1 device /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes
  ==>
  MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W device_characteristics device.dma_state.internal_state memory1 memory2
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATION_CPU_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W THEN
AITAC THEN
STAC
QED

Theorem INVARIANT_L3_IMPLIES_INVARIANT_L2_LEMMA:
!device_characteristics memory device2.
  INVARIANT_L3 device_characteristics memory device2
  ==>
  DEFINED_CHANNELS device_characteristics device2 /\
  INVARIANT_FETCH_BD_L3 device_characteristics memory device2 /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device2 /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device2 /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device2 /\
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device2 /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_L3 THEN
STAC
QED

Theorem INVARIANT_L3_IMPLIES_INVARIANT_CONCRETE_L3_LEMMA:
!device_characteristics memory device.
  INVARIANT_L3 device_characteristics memory device
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory device
Proof
INTRO_TAC THEN
ETAC INVARIANT_L3 THEN
ETAC INVARIANT_CONCRETE_L3 THEN
STAC
QED

Theorem INVARIANT_L3_IMPLIES_DEFINED_CHANNELS_LEMMA:
!device_characteristics memory device.
  INVARIANT_L3 device_characteristics memory device
  ==>
  DEFINED_CHANNELS device_characteristics device
Proof
INTRO_TAC THEN
ETAC INVARIANT_L3 THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_PRESERVES_CHANNEL_BDS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory
 channel_id
 (serviced_request : 8 word list # ('interconnect_address_width, 'tag_width) interconnect_request_type).
  VALID_CHANNEL_ID device_characteristics channel_id /\
  device2 = dma_request_served device_characteristics device1 serviced_request
  ==>
  channel_bds device_characteristics memory device2.dma_state channel_id = channel_bds device_characteristics memory device1.dma_state channel_id
Proof
INTRO_TAC THEN
ETAC invariant_l3Theory.channel_bds THEN
ITAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA THEN
LRTAC THEN
LETS_TAC THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
AIRTAC THEN
PTAC operationsTheory.APPENDED_REPLY_REMOVED_REQUEST_CHANNEL THEN
PTAC operationsTheory.append_reply_remove_request_channel THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem MEM_BDS_TO_FETCH_RAS_IMPLIES_MEM_BDS_TO_FETCH_LEMMA:
!bds_to_fetch bds_to_fetch_as address.
  bds_to_fetch_as = bds_to_fetch_ras bds_to_fetch /\
  MEM address bds_to_fetch_as
  ==>
  ?bd bd_ras bd_was uflag.
    MEM ((bd, bd_ras, bd_was), uflag) bds_to_fetch /\
    MEM address bd_ras
Proof
Induct THENL
[
 INTRO_TAC THEN
 PTAC bd_queuesTheory.bds_to_fetch_ras THEN
 LRTAC THEN
 ETAC listTheory.MEM THEN
 SOLVE_F_ASM_TAC
 ,
 INTRO_TAC THEN
 PTAC bd_queuesTheory.bds_to_fetch_ras THEN
 ALL_LRTAC THEN
 ETAC listTheory.MEM_APPEND THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  REWRITE_TAC [listTheory.MEM] THEN
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  EXISTS_EQ_TAC THEN
  STAC
  ,
  AIRTAC THEN
  REWRITE_TAC [listTheory.MEM] THEN
  AXTAC THEN
  PAXTAC THEN
  STAC
 ]
]
QED

Theorem MEMORY_WRITE_REQUEST_NOT_BD_TO_FETCH_PRESERVES_BDS_LEMMA:
!device_characteristics memory1 memory2 was bds_to_fetch bds_to_fetch_as internal_state channel_id address_bytes.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory1 internal_state /\
  bds_to_fetch_as = bds_to_fetch_ras bds_to_fetch /\
  memory2 = update_memory memory1 address_bytes /\
  was = MAP FST address_bytes /\
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory1 internal_state was
  ==>
  !address.
    MEM address bds_to_fetch_as
    ==>
    memory1 address = memory2 address
Proof
INTRO_TAC THEN
INTRO_TAC THEN
ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
IRTAC MEM_BDS_TO_FETCH_RAS_IMPLIES_MEM_BDS_TO_FETCH_LEMMA THEN
AXTAC THEN
AIRTAC THEN
ETAC listsTheory.DISJOINT_LISTS THEN
RW_HYP_LEMMA_TAC lists_lemmasTheory.EVERY_NOT_MEM_SYM_LEMMA THEN
IRTAC write_properties_lemmasTheory.UPDATING_UNREAD_MEMORY_IMPLIES_SAME_MEMORY_LEMMA THEN
STAC
QED

Theorem MEMORY_WRITE_REQUEST_NOT_SCRATCHPAD_PRESERVES_BDS_LEMMA:
!device_characteristics memory1 memory2 was scratchpad_addresses internal_state address_bytes.
  scratchpad_addresses = device_characteristics.dma_characteristics.scratchpad_addresses internal_state /\
  memory2 = update_memory memory1 address_bytes /\
  was = MAP FST address_bytes /\
  WRITE_ADDRESS_NOT_SCRATCHPAD device_characteristics internal_state was
  ==>
  !address.
    MEM address scratchpad_addresses
    ==>
    memory1 address = memory2 address
Proof
INTRO_TAC THEN
INTRO_TAC THEN
ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_SCRATCHPAD THEN
AITAC THEN
ETAC listsTheory.DISJOINT_LISTS THEN
RW_HYP_LEMMA_TAC lists_lemmasTheory.EVERY_NOT_MEM_SYM_LEMMA THEN
IRTAC write_properties_lemmasTheory.UPDATING_UNREAD_MEMORY_IMPLIES_SAME_MEMORY_LEMMA THEN
STAC
QED

Theorem SCRATCHPAD_BDS_TO_FETCH_ADDRESSES_LEMMA:
!device_characteristics channel_id scratchpad_as bds_to_fetch_as scratchpad_bds_to_fetch_as memory1 memory2 internal_state.
  scratchpad_as = (device_characteristics.dma_characteristics.scratchpad_addresses internal_state) /\
  bds_to_fetch_as = bds_to_fetch_ras ((cverification device_characteristics channel_id).bds_to_fetch memory1 internal_state) /\
  (!address.
     MEM address scratchpad_as
     ==>
     memory1 address = memory2 address) /\
  (!address.
     MEM address bds_to_fetch_as
     ==>
     memory1 address = memory2 address) /\
  scratchpad_bds_to_fetch_as = bds_to_fetch_as ++ scratchpad_as
  ==>
  (!address.
     MEM address scratchpad_bds_to_fetch_as
     ==>
     memory1 address = memory2 address)
Proof
INTRO_TAC THEN
WEAKEN_TAC is_eq THEN
WEAKEN_TAC is_eq THEN
LRTAC THEN
INTRO_TAC THEN
ETAC listTheory.MEM_APPEND THEN
SPLIT_ASM_DISJS_TAC THEN REPEAT AIRTAC THEN STAC
QED

Theorem NO_MEMORY_WRITES_BDS_TO_FETCH_PRESERVES_EXTERNAL_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id memory1 memory2 device address_bytes tag.
  PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics /\
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l3 device_characteristics device) /\
  memory2 = update_memory memory1 address_bytes
  ==>
  (cverification device_characteristics channel_id).bds_to_fetch memory1 device.dma_state.internal_state =
  (cverification device_characteristics channel_id).bds_to_fetch memory2 device.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC l3Theory.dma_pending_requests_l3 THEN 
PTAC operationsTheory.dma_pending_requests THEN
ETAC listTheory.MEM_APPEND THEN
SPLIT_ASM_DISJS_TAC THENL
[
 PTAC invariant_l3Theory.NO_MEMORY_WRITES_TO_BDS THEN
 IRTAC internal_operation_lemmasTheory.REQUEST_WAS_IN_REQUESTS_WAS_LEMMA THEN
 AIRTAC THEN
 PTAC bd_queuesTheory.CONSISTENT_DMA_WRITE THEN
 AIRTAC THEN
 ITAC MEMORY_WRITE_REQUEST_NOT_BD_TO_FETCH_PRESERVES_BDS_LEMMA THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE THEN
 AIRTAC THEN
 STAC
 ,
 PTAC MEMORY_WRITES_PRESERVES_BDS_TO_FETCH THEN
 PTAC stateTheory.READ_REQUESTS THEN
 ETAC listTheory.EVERY_MEM THEN
 AIRTAC THEN
 PTAC stateTheory.READ_REQUEST THEN
 SOLVE_F_ASM_TAC
]
QED

Theorem NO_MEMORY_WRITES_BDS_TO_FETCH_PRESERVES_INTERNAL_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id memory1 memory2 device address_bytes tag.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  INTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l3 device_characteristics device) /\
  memory2 = update_memory memory1 address_bytes
  ==>
  (cverification device_characteristics channel_id).bds_to_fetch memory1 device.dma_state.internal_state =
  (cverification device_characteristics channel_id).bds_to_fetch memory2 device.dma_state.internal_state
Proof
INTRO_TAC THEN
IRTAC state_lemmasTheory.NOT_EXTERNAL_BDS_IMPLIES_INTERNAL_BDS_LEMMA THEN
ETAC proof_obligationsTheory.PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY THEN
INST_IMP_ASM_GOAL_TAC THEN
STAC
QED

Theorem NO_MEMORY_WRITES_BDS_TO_FETCH_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics memory1 memory2 device address_bytes tag.
  PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics /\
  PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l3 device_characteristics device) /\
  memory2 = update_memory memory1 address_bytes
  ==>
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (cverification device_characteristics channel_id).bds_to_fetch memory1 device.dma_state.internal_state =
    (cverification device_characteristics channel_id).bds_to_fetch memory2 device.dma_state.internal_state
Proof
INTRO_TAC THEN
INTRO_TAC THEN
Cases_on ‘EXTERNAL_BDS device_characteristics’ THENL
[
 IRTAC NO_MEMORY_WRITES_BDS_TO_FETCH_PRESERVES_EXTERNAL_BDS_TO_FETCH_LEMMA THEN STAC
 ,
 ITAC state_lemmasTheory.NOT_EXTERNAL_BDS_IMPLIES_INTERNAL_BDS_LEMMA THEN
 IRTAC NO_MEMORY_WRITES_BDS_TO_FETCH_PRESERVES_INTERNAL_BDS_TO_FETCH_LEMMA THEN
 STAC
]
QED

Definition BDS_TO_FETCH_EQ_INTERNAL_STATE:
BDS_TO_FETCH_EQ_INTERNAL_STATE device_characteristics memory1 memory2 internal_state =
!channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  (cverification device_characteristics channel_id).bds_to_fetch memory2 internal_state =
  (cverification device_characteristics channel_id).bds_to_fetch memory1 internal_state
End

Theorem BDS_TO_FETCH_EQ_INTERNAL_STATE_SYM_LEMMA:
!device_characteristics memory1 memory2 internal_state.
BDS_TO_FETCH_EQ_INTERNAL_STATE device_characteristics memory1 memory2 internal_state =
BDS_TO_FETCH_EQ_INTERNAL_STATE device_characteristics memory2 memory1 internal_state
Proof
REPEAT GEN_TAC THEN
ETAC BDS_TO_FETCH_EQ_INTERNAL_STATE THEN
EQ_TAC THEN
 INTRO_TAC THEN
 INTRO_TAC THEN
 AIRTAC THEN
 STAC
QED

Theorem BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA:
!device_characteristics memory1 memory2 device.
  BDS_TO_FETCH_EQ_INTERNAL_STATE device_characteristics memory1 memory2 device.dma_state.internal_state /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device
  ==>
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC NO_MEMORY_WRITES_TO_BDS THEN
INTRO_TAC THEN
AIRTAC THEN
ETAC bd_queuesTheory.CONSISTENT_DMA_WRITE THEN
INTRO_TAC THEN
AIRTAC THEN
CONJS_TAC THEN TRY STAC THEN
ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
INTRO_TAC THEN
PTAC BDS_TO_FETCH_EQ_INTERNAL_STATE THEN
AITAC THEN
LRTAC THEN
AIRTAC THEN
STAC
QED

Theorem BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_CHANNEL_BDS_LEMMA:
!device_characteristics memory1 memory2 device channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BDS_TO_FETCH_EQ_INTERNAL_STATE device_characteristics memory1 memory2 device.dma_state.internal_state
  ==>
  channel_bds device_characteristics memory2 device.dma_state channel_id = channel_bds device_characteristics memory1 device.dma_state channel_id
Proof
INTRO_TAC THEN
ETAC invariant_l3Theory.channel_bds THEN
ETAC BDS_TO_FETCH_EQ_INTERNAL_STATE THEN
AIRTAC THEN
STAC
QED

Theorem BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_NOT_DMA_BDS_LEMMA:
!device_characteristics memory1 memory2 device.
  BDS_TO_FETCH_EQ_INTERNAL_STATE device_characteristics memory1 memory2 device.dma_state.internal_state /\
  NOT_DMA_BDS device_characteristics memory1 device
  ==>
  NOT_DMA_BDS device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC NOT_DMA_BDS THEN
INTRO_TAC THEN
PAT_X_ASSUM “!x.P” (fn thm => MATCH_MP_TAC thm) THEN
INST_EXISTS_TAC THEN
CONJS_TAC THEN TRY STAC THENL
[
 IRTAC BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_CHANNEL_BDS_LEMMA THEN STAC
 ,
 PAT_X_ASSUM “VALID_CHANNEL_ID device_characteristics channel_id_bd” (fn thm => ASSUME_TAC thm) THEN
 IRTAC BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_CHANNEL_BDS_LEMMA THEN
 STAC
]
QED

(*
Theorem BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_NOT_DMA_SCRATCHPAD_LEMMA:
!device_characteristics memory1 memory2 device.
  BDS_TO_FETCH_EQ_INTERNAL_STATE device_characteristics memory1 memory2 device.dma_state.internal_state /\
  NOT_DMA_SCRATCHPAD device_characteristics memory1 device
  ==>
  NOT_DMA_SCRATCHPAD device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC invariant_l3Theory.NOT_DMA_SCRATCHPAD THEN
INTRO_TAC THEN
ITAC BDS_TO_FETCH_EQ_INTERNAL_STATE_PRESERVES_CHANNEL_BDS_LEMMA THEN
LRTAC THEN
AIRTAC THEN
STAC
QED
*)

Theorem MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_WRITE_REQUEST_IMPLIES_F_LEMMA:
!device address_bytes tag.
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device /\
  MEM (request_write address_bytes tag) device.dma_state.pending_register_related_memory_requests
  ==>
  F
Proof
INTRO_TAC THEN
ETAC MEMORY_WRITES_PRESERVES_BDS_TO_FETCH THEN
ETAC stateTheory.READ_REQUESTS THEN
ETAC listTheory.EVERY_MEM THEN
AIRTAC THEN
ETAC stateTheory.READ_REQUEST THEN
STAC
QED

Theorem BDS_TO_FETCH_IMPLIES_MEMORY_LOCATIONS_OF_BD_EQUAL_LEMMA:
!device_characteristics channel_id memory1 memory2 device addresses tag bd bd_ras bd_was uf bds address_bytes write_tag.
  EXTERNAL_BDS device_characteristics /\
  PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device /\
  (cverification device_characteristics channel_id).bds_to_fetch memory1 device.dma_state.internal_state = ((bd, bd_ras, bd_was), uf)::bds /\
  (addresses, tag) = (coperation device_characteristics channel_id).fetch_bd_addresses device.dma_state.internal_state /\
  MEM (request_write address_bytes write_tag) (dma_pending_requests device_characteristics device) /\
  memory2 = update_memory memory1 address_bytes
  ==>
  MAP memory2 addresses = MAP memory1 addresses
Proof
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS THEN
AITAC THEN
PTAC NO_MEMORY_WRITES_TO_BDS THEN
IRTAC dma_pending_requests_lemmasTheory.DMA_PENDING_REQUEST_FROM_VALID_SCHANNEL_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AXTAC THEN
 IRTAC dma_pending_requests_lemmasTheory.PENDING_WRITE_REQUEST_IS_CHANNEL_REQUEST_LEMMA THEN
 AIRTAC THEN
 PTAC bd_queuesTheory.CONSISTENT_DMA_WRITE THEN
 AIRTAC THEN
 PTAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
 IRTAC lists_lemmasTheory.MEM_HD_LEMMA THEN
 AIRTAC THEN
 IRTAC lists_lemmasTheory.LIST1_IN_LIST2_PRESERVES_DISJOINTNESS2_LEMMA THEN
 IRTAC write_properties_lemmasTheory.DISJOINT_ADDRESSES_IMPLIES_SAME_MEMORY_LEMMA THEN
 STAC
 ,
 IRTAC MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_WRITE_REQUEST_IMPLIES_F_LEMMA THEN
 SOLVE_F_ASM_TAC
]
QED

Theorem DMA_PENDING_WRITE_REQUEST_PRESERVES_BD_TO_FETCH_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id addresses tag1 tag2 memory1 memory2 address_bytes.
  PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ device_characteristics /\
  PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS device_characteristics /\
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory1 device /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device /\
  (addresses, tag1) = (coperation device_characteristics channel_id).fetch_bd_addresses device.dma_state.internal_state /\
  MEM (request_write address_bytes tag2) (dma_pending_requests device_characteristics device) /\
  memory2 = update_memory memory1 address_bytes
  ==>
  MAP memory2 addresses = MAP memory1 addresses
Proof
INTRO_TAC THEN
Cases_on ‘(cverification device_characteristics channel_id).bds_to_fetch memory1 device.dma_state.internal_state = []’ THENL
[
 IRTAC fetching_bd_suboperations_lemmasTheory.NO_BDS_TO_FETCH_IMPLIES_MEMORY_LOCATIONS_OF_BD_EQUAL_LEMMA THEN
 REPEAT (WEAKEN_TAC (not o is_forall)) THEN
 PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPECL [“memory2 : 'interconnect_address_width memory_type”, “memory1 : 'interconnect_address_width memory_type”] thm)) THEN
 STAC
 ,
 ASSUME_TAC (SPEC
   “(cverification (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type) channel_id).bds_to_fetch
      memory1
      (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).dma_state.internal_state :
    ('bd_type, 'interconnect_address_width) bds_to_fetch_entry_type list”
   (INST_TYPE [“: 'a” |-> “: ('bd_type, 'interconnect_address_width) bds_to_fetch_entry_type”] listTheory.list_nchotomy)) THEN
 SPLIT_ASM_DISJS_TAC THEN (TRY CONTR_ASMS_TAC) THEN
 AXTAC THEN
 IRTAC BDS_TO_FETCH_IMPLIES_MEMORY_LOCATIONS_OF_BD_EQUAL_LEMMA THEN
 STAC
]
QED

Theorem DMA_REGISTER_READ_PRESERVES_CHANNEL_BDS_LEMMA:
!device_characteristics memory device1 device2 addresses bytes channel_id.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (device2, bytes) = dma_register_read device_characteristics is_valid_l3 device1 addresses
  ==>
  channel_bds device_characteristics memory device2.dma_state channel_id =
  channel_bds device_characteristics memory device1.dma_state channel_id
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_register_read THEN
EQ_PAIR_ASM_TAC THEN
PAT_X_ASSUM “x = (y, z)” (fn thm => ASSUME_TAC (GSYM thm)) THEN
NRLTAC 2 THEN
LRTAC THEN
RECORD_TAC THEN
ETAC invariant_l3Theory.channel_bds THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH THEN
AIRTAC THEN
AIRTAC THEN
LETS_TAC THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_CHANNELS_LEMMA:
!device_characteristics device1 device2.
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1
  ==>
  device2.dma_state.channels = device1.dma_state.channels
Proof
INTRO_TAC THEN
PTAC operationsTheory.process_register_related_memory_access THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_CHANNEL_BDS_LEMMA:
!device_characteristics device1 device2.
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLY_PRESERVES_BDS_TO_FETCH device_characteristics /\
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1
  ==>
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    !memory.
      channel_bds device_characteristics memory device2.dma_state channel_id =
      channel_bds device_characteristics memory device1.dma_state channel_id
Proof
INTRO_TAC THEN
ITAC PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_CHANNELS_LEMMA THEN
IRTAC internal_operation_lemmasTheory.PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_BDS_TO_FETCH_LEMMA THEN
INTRO_TAC THEN
AIRTAC THEN
REWRITE_TAC [channel_bds] THEN
STAC
QED

Theorem SCRATCHPAD_ADDRESSES_EQ_PRESERVES_WRITE_ADDRESS_NOT_SCRATCHPAD_LEMMA:
!device_characteristics device1 device2 request_was.
  SCRATCHPAD_ADDRESSES_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
  ==>
  WRITE_ADDRESS_NOT_SCRATCHPAD device_characteristics device1.dma_state.internal_state request_was =
  WRITE_ADDRESS_NOT_SCRATCHPAD device_characteristics device2.dma_state.internal_state request_was
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_SCRATCHPAD THEN
ETAC stateTheory.SCRATCHPAD_ADDRESSES_EQ THEN
STAC
QED

Theorem BDS_TO_FETCH_EQ_PRESERVES_WRITE_ADDRESS_NOT_BD_TO_FETCH_LEMMA:
!device_characteristics memory device1 device2 request_was.
  BDS_TO_FETCH_EQ device_characteristics memory device1.dma_state.internal_state device2.dma_state.internal_state
  ==>
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory device1.dma_state.internal_state request_was =
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory device2.dma_state.internal_state request_was
Proof
INTRO_TAC THEN
EQ_TAC THEN
 INTRO_TAC THEN
 ETAC stateTheory.BDS_TO_FETCH_EQ THEN
 REWRITE_TAC [bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH] THEN
 INTRO_TAC THEN
 AITAC THEN
 LRTAC THEN
 ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
 AIRTAC THEN
 STAC
QED

Theorem BDS_TO_FETCH_EQ_SCRATCHPAD_ADDRESSES_EQ_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA:
!device_characteristics memory device1 device2 request_was.
  BDS_TO_FETCH_EQ device_characteristics memory device1.dma_state.internal_state device2.dma_state.internal_state (*/\
  SCRATCHPAD_ADDRESSES_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state*)
  ==>
  CONSISTENT_DMA_WRITE device_characteristics memory device1.dma_state.internal_state request_was =
  CONSISTENT_DMA_WRITE device_characteristics memory device2.dma_state.internal_state request_was
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.CONSISTENT_DMA_WRITE THEN
EQ_TAC THENL
[
 INTRO_TAC THEN
 INTRO_TAC THEN
 AIRTAC THEN
 IRTAC BDS_TO_FETCH_EQ_PRESERVES_WRITE_ADDRESS_NOT_BD_TO_FETCH_LEMMA THEN QLRTAC THEN STAC
(* CONJS_TAC THEN TRY STAC THENL
 [
  IRTAC BDS_TO_FETCH_EQ_PRESERVES_WRITE_ADDRESS_NOT_BD_TO_FETCH_LEMMA THEN QLRTAC THEN STAC
  ,
  IRTAC SCRATCHPAD_ADDRESSES_EQ_PRESERVES_WRITE_ADDRESS_NOT_SCRATCHPAD_LEMMA THEN QLRTAC THEN STAC
 ]*)
 ,
 INTRO_TAC THEN
 INTRO_TAC THEN
 AIRTAC THEN
 IRTAC BDS_TO_FETCH_EQ_PRESERVES_WRITE_ADDRESS_NOT_BD_TO_FETCH_LEMMA THEN QLRTAC THEN STAC
(* CONJS_TAC THEN TRY STAC THENL
 [
  IRTAC BDS_TO_FETCH_EQ_PRESERVES_WRITE_ADDRESS_NOT_BD_TO_FETCH_LEMMA THEN QLRTAC THEN STAC
  ,
  IRTAC SCRATCHPAD_ADDRESSES_EQ_PRESERVES_WRITE_ADDRESS_NOT_SCRATCHPAD_LEMMA THEN QLRTAC THEN STAC
 ]*)
]
QED

Theorem CHANNELS_EQ_PRESERVES_CHANNEL_REQUESTS_LEMMA:
!device_characteristics device1 device2.
  CHANNELS_EQ device1 device2
  ==>
  channel_requests device_characteristics device2 = channel_requests device_characteristics device1
Proof
INTRO_TAC THEN
ETAC stateTheory.CHANNELS_EQ THEN
ETAC operationsTheory.channel_requests THEN
STAC
QED

Theorem CHANNELS_EQ_PRESERVES_COLLECT_CHANNELS_STATE_LEMMA:
!device_characteristics device1 device2.
  CHANNELS_EQ device1 device2
  ==>
  collect_channels_state device_characteristics.dma_characteristics device2.dma_state.channels =
  collect_channels_state device_characteristics.dma_characteristics device1.dma_state.channels
Proof
INTRO_TAC THEN
ETAC stateTheory.CHANNELS_EQ THEN
ETAC operationsTheory.collect_channels_state THEN
STAC
QED

Theorem CHANNELS_EQ_BDS_TO_FETCH_EQ_SCRATCHPAD_ADDRESSES_EQ_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA:
!device_characteristics memory device1 device2.
  CHANNELS_EQ device1 device2 /\
  BDS_TO_FETCH_EQ device_characteristics memory device1.dma_state.internal_state device2.dma_state.internal_state (*/\
  SCRATCHPAD_ADDRESSES_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state*)
  ==>
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device2 = NO_MEMORY_WRITES_TO_BDS device_characteristics memory device1
Proof
INTRO_TAC THEN
EQ_TAC THEN (
 INTRO_TAC THEN
 REWRITE_TAC [NO_MEMORY_WRITES_TO_BDS] THEN
 INTRO_TAC THEN
 ITAC CHANNELS_EQ_PRESERVES_CHANNEL_REQUESTS_LEMMA THEN
 RLTAC THEN
 ETAC NO_MEMORY_WRITES_TO_BDS THEN
 FAIRTAC THEN
 IRTAC BDS_TO_FETCH_EQ_SCRATCHPAD_ADDRESSES_EQ_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA THEN
 QRLTAC THEN
 STAC
)
QED

Theorem UPDATE_DEVICE_STATE_BDS_TO_FETCH_EQ_NOT_ADDING_BDS_LEMMA:
!device_characteristics memory channel_id device1 device2 internal_state1
 internal_state2 channel1 channel2 channel_bd_queues1 channel_bd_queues2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BDS_TO_FETCH_EQ device_characteristics memory internal_state1 internal_state2 /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  channel2 = schannel device2 channel_id /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  channel_bd_queues1 = channel_bd_queues device_characteristics channel_id memory internal_state1 channel1 /\
  channel_bd_queues2 = channel_bd_queues device_characteristics channel_id memory internal_state2 channel2 /\
  CHANNEL_SET channel_bd_queues2 SUBSET CHANNEL_SET channel_bd_queues1
  ==>
  CHANNEL_BD_QUEUES_SUBSET device_characteristics memory device1 device2
Proof
INTRO_TAC THEN
REWRITE_TAC [CHANNEL_BD_QUEUES_SUBSET] THEN
ITAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
RLTAC THEN
INTRO_TAC THEN
Cases_on ‘channel_id = channel_id'’ THENL
[
 RLTAC THEN IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN ALL_LRTAC THEN STAC
 ,
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN
 PAT_X_ASSUM “x <> y” (fn thm => ASSUME_TAC (GSYM thm)) THEN
 AIRTAC THEN
 RLTAC THEN
 RLTAC THEN
 RLTAC THEN
 LRTAC THEN
 LRTAC THEN
 REWRITE_TAC [channel_bd_queues] THEN
 LETS_TAC THEN
 ETAC stateTheory.BDS_TO_FETCH_EQ THEN
 AIRTAC THEN
 RLTAC THEN
 RLTAC THEN
 RLTAC THEN
 RLTAC THEN
 REWRITE_TAC [pred_setTheory.SUBSET_REFL]
]
QED

Theorem CHANNEL_BDS_EQ_BD_TRANSFER_RAS_WAS_EQ_PRESERVES_NOT_DMA_BDS_LEMMA:
!device_characteristics memory device1 device2.
  CHANNEL_BDS_EQ device_characteristics memory device1 device2 /\
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
  ==>
  NOT_DMA_BDS device_characteristics memory device2 = NOT_DMA_BDS device_characteristics memory device1
Proof
INTRO_TAC THEN
EQ_TAC THEN (
 INTRO_TAC THEN
 ETAC NOT_DMA_BDS THEN
 INTRO_TAC THEN
 PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC_ALL thm)) THEN
 PAT_X_ASSUM “P ==> Q” (fn thm => MATCH_MP_TAC thm) THEN 
 CONJS_TAC THEN TRY STAC THENL
 [
  ETAC CHANNEL_BDS_EQ THEN
  PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC “channel_id_dma_bd : 'b channel_id_type” thm)) THEN
  AIRTAC THEN
  STAC
  ,
  ETAC stateTheory.BD_TRANSFER_RAS_WAS_EQ THEN
  PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC “channel_id_dma_bd : 'b channel_id_type” thm)) THEN
  AIRTAC THEN
  STAC
  ,
  ETAC CHANNEL_BDS_EQ THEN
  PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC “channel_id_bd : 'b channel_id_type” thm)) THEN
  AIRTAC THEN
  STAC
 ]
)
QED

(*
Theorem CHANNEL_BDS_EQ_BD_TRANSFER_RAS_WAS_EQ_SCRATCHPAD_ADDRESSES_EQ_LEMMA:
!device_characteristics memory device1 device2.
  CHANNEL_BDS_EQ device_characteristics memory device1 device2 /\
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state (*/\
  SCRATCHPAD_ADDRESSES_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state*)
  ==>
  NOT_DMA_SCRATCHPAD device_characteristics memory device2 = NOT_DMA_SCRATCHPAD device_characteristics memory device1
Proof
INTRO_TAC THEN
EQ_TAC THENL
[
 INTRO_TAC THEN
 REWRITE_TAC [NOT_DMA_SCRATCHPAD] THEN
 INTRO_TAC THEN
 ETAC stateTheory.BD_TRANSFER_RAS_WAS_EQ THEN
 AITAC THEN
 QLRTAC THEN
 ETAC CHANNEL_BDS_EQ THEN
 AITAC THEN
 LRTAC THEN
 ETAC NOT_DMA_SCRATCHPAD THEN
 AIRTAC THEN
 ETAC stateTheory.SCRATCHPAD_ADDRESSES_EQ THEN
 STAC
 ,
 INTRO_TAC THEN
 REWRITE_TAC [NOT_DMA_SCRATCHPAD] THEN
 INTRO_TAC THEN
 ETAC stateTheory.BD_TRANSFER_RAS_WAS_EQ THEN
 AITAC THEN
 QRLTAC THEN
 ETAC CHANNEL_BDS_EQ THEN
 AITAC THEN
 RLTAC THEN
 ETAC NOT_DMA_SCRATCHPAD THEN
 AIRTAC THEN
 ETAC stateTheory.SCRATCHPAD_ADDRESSES_EQ THEN
 STAC
]
QED
*)

Theorem FETCH_BD_ADDRESSES_EQ_CHANNELS_EQ_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA:
!device_characteristics memory device1 device2.
  FETCH_BD_ADDRESSES_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state /\
  CHANNELS_EQ device1 device2
  ==>
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device2 =
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device1
Proof
INTRO_TAC THEN
EQ_TAC THENL
[
 INTRO_TAC THEN
 REWRITE_TAC [INVARIANT_EXTERNAL_FETCH_BD_REPLY] THEN
 INTRO_TAC THEN
 ETAC stateTheory.FETCH_BD_ADDRESSES_EQ THEN
 AITAC THEN
 RLTAC THEN
 ETAC stateTheory.CHANNELS_EQ THEN
 ETAC stateTheory.schannel THEN
 LRTAC THEN
 ETAC stateTheory.schannel THEN
 ETAC INVARIANT_EXTERNAL_FETCH_BD_REPLY THEN
 AIRTAC THEN
 STAC
 ,
 INTRO_TAC THEN
 REWRITE_TAC [INVARIANT_EXTERNAL_FETCH_BD_REPLY] THEN
 INTRO_TAC THEN
 ETAC stateTheory.FETCH_BD_ADDRESSES_EQ THEN
 AITAC THEN
 RLTAC THEN
 ETAC stateTheory.CHANNELS_EQ THEN
 ETAC stateTheory.schannel THEN
 RLTAC THEN
 ETAC stateTheory.schannel THEN
 ETAC INVARIANT_EXTERNAL_FETCH_BD_REPLY THEN
 AIRTAC THEN
 STAC
]
QED

Theorem CHANNELS_EQ_FETCH_BD_ADDRESSES_EQ_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA:
!device_characteristics memory device1 device2.
  CHANNELS_EQ device1 device2 /\
  FETCH_BD_ADDRESSES_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
  ==>
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device2 =
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device1
Proof
INTRO_TAC THEN
ETAC FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES THEN
REWRITE_TAC [stateTheory.schannel] THEN
ETAC stateTheory.CHANNELS_EQ THEN
LRTAC THEN
ETAC stateTheory.FETCH_BD_ADDRESSES_EQ THEN
EQ_TAC THEN
 INTRO_TAC THEN
 INTRO_TAC THEN
 AITAC THEN
 AIRTAC THEN
 STAC
QED






(**************************)

Theorem SET_ETA_LEMMA:
!requests P l.
  {e | MEM e l} = {e | (\e. MEM e l) e}
Proof
APP_SCALAR_TAC THEN STAC
QED

Theorem MEM_EQ_MEM_ABS_LEMMA:
!e l. MEM e l = (\e. MEM e l) e
Proof
APP_SCALAR_TAC THEN STAC
QED

Theorem IN_MEM_ABS_EQ_MEM_LEMMA:
!x l.
  (x IN (\e. MEM e l)) = (MEM x l)
Proof
ONCE_REWRITE_TAC [MEM_EQ_MEM_ABS_LEMMA] THEN REWRITE_TAC [pred_setTheory.IN_ABS]
QED

Theorem IN_MEM_ABS_TRANSFER_EQ_MEM_TRANSFER_LEMMA:
!l1 l2.
  (!x. x IN (\e. MEM e l2) ==> x IN (λe. MEM e l1)) = (!x. MEM x l2 ==> MEM x l1)
Proof
REWRITE_TAC [IN_MEM_ABS_EQ_MEM_LEMMA]
QED



Theorem MEM_FILTER_WRITE_REQUEST_IMPLIES_REQUEST_LEMMA:
!requests write_requests address_bytes tag.
  write_requests = FILTER WRITE_REQUEST requests /\
  MEM (request_write address_bytes tag) write_requests
  ==>
  MEM (request_write address_bytes tag) requests
Proof
INTRO_TAC THEN
LRTAC THEN
ETAC listTheory.MEM_FILTER THEN
STAC
QED

Theorem WRITE_REQUEST_MEMBER_IMPLIES_FILTER_WRITE_REQUEST_MEMBER_LEMMA:
!requests address_bytes tag.
  MEM (request_write address_bytes tag) requests
  ==>
  MEM (request_write address_bytes tag) (FILTER WRITE_REQUEST requests)
Proof
Induct THENL
[
 REWRITE_TAC [listTheory.MEM]
 ,
 INTRO_TAC THEN
 ETAC listTheory.MEM THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  RLTAC THEN
  REWRITE_TAC [listTheory.FILTER] THEN
  IF_SPLIT_TAC THENL
  [
   REWRITE_TAC [listTheory.MEM]
   ,
   ETAC stateTheory.WRITE_REQUEST THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC
  ]
  ,
  AIRTAC THEN
  REWRITE_TAC [listTheory.FILTER] THEN
  IF_SPLIT_TAC THEN
   ASM_REWRITE_TAC [listTheory.MEM]
 ]
]
QED

Theorem WRITE_REQUEST_IN_CHANNEL_REQUESTS_IMPLIES_IN_CHANNEL_WRITE_REQUESTS_LEMMA:
!device_characteristics device requests write_requests channel_id address_bytes tag.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  requests = channel_requests device_characteristics device /\
  write_requests = FILTER WRITE_REQUEST requests /\
  MEM (request_write address_bytes tag) (channel_pending_requests (schannel device channel_id).pending_accesses.requests)
  ==>
  MEM (request_write address_bytes tag) write_requests
Proof
INTRO_TAC THEN
ITAC dma_pending_requests_lemmasTheory.CHANNEL_PENDING_REQUESTS_IN_CHANNEL_REQUESTS_LEMMA THEN
IRTAC WRITE_REQUEST_MEMBER_IMPLIES_FILTER_WRITE_REQUEST_MEMBER_LEMMA THEN
STAC
QED

Theorem MEM_WRITE_REQUESTS_IMPLIES_WRITE_REQUEST_LEMMA:
!requests write_requests request.
  write_requests = FILTER WRITE_REQUEST requests /\
  MEM request write_requests
  ==>
  ?address_bytes tag.
    request = request_write address_bytes tag
Proof
Induct THENL
[
 INTRO_TAC THEN
 ETAC listTheory.FILTER THEN
 LRTAC THEN
 ETAC listTheory.MEM THEN
 SOLVE_F_ASM_TAC
 ,
 INTRO_TAC THEN
 LRTAC THEN
 ETAC listTheory.FILTER THEN
 IF_SPLIT_TAC THENL
 [
  ETAC listTheory.MEM THEN
  SPLIT_ASM_DISJS_TAC THENL
  [
   RLTAC THEN
   PTAC stateTheory.WRITE_REQUEST THEN TRY SOLVE_F_ASM_TAC THEN
   LRTAC THEN
   EXISTS_EQ_TAC
   ,
   AIRTAC THEN STAC
  ]
  ,
  AIRTAC THEN STAC
 ]
]
QED

Theorem NO_WRITE_ADDRESSES_OR_WRITE_REQUEST_LEMMA:
!requests requests_was was.
  requests_was = MAP request_to_write_addresses requests /\
  MEM was requests_was
  ==>
  was = [] \/
  ?address_bytes tag.
    MEM (request_write address_bytes tag) requests /\
    MAP FST address_bytes = was
Proof
Induct THENL
[
 INTRO_TAC THEN
 ETAC listTheory.MAP THEN
 LRTAC THEN
 ETAC listTheory.MEM THEN
 SOLVE_F_ASM_TAC
 ,
 INTRO_TAC THEN
 ETAC listTheory.MAP THEN
 LRTAC THEN
 ETAC listTheory.MEM THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  PTAC operationsTheory.request_to_write_addresses THEN TRY STAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  PAXTAC THEN
  REWRITE_TAC [listTheory.MEM] THEN
  STAC
  ,
  AIRTAC THEN
  SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
  AXTAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  PAXTAC THEN
  ETAC listTheory.MEM THEN
  STAC
 ]
]
QED

Theorem WRITE_REQUEST_SUBSET_TRANSFERS_MEMBER_LEMMA:
!requests1 requests2 write_requests1 write_requests2 requests_was1 address_bytes tag.
  write_requests1 = FILTER WRITE_REQUEST requests1 /\
  write_requests2 = FILTER WRITE_REQUEST requests2 /\
  CHANNEL_SET write_requests2 SUBSET CHANNEL_SET write_requests1 /\
  requests_was1 = MAP request_to_write_addresses requests1 /\
  MEM (request_write address_bytes tag) requests2
  ==>
  MEM (MAP FST address_bytes) requests_was1
Proof
INTRO_TAC THEN
ITAC WRITE_REQUEST_MEMBER_IMPLIES_FILTER_WRITE_REQUEST_MEMBER_LEMMA THEN
RLTAC THEN
ETAC CHANNEL_SET THEN
IRTAC pred_setTheory.SUBSET_THM THEN
ETAC SET_ETA_LEMMA THEN
ETAC pred_setTheory.GSPEC_ETA THEN
ETAC IN_MEM_ABS_TRANSFER_EQ_MEM_TRANSFER_LEMMA THEN
AIRTAC THEN
LRTAC THEN
ETAC listTheory.MEM_FILTER THEN
LRTAC THEN
REWRITE_TAC [listTheory.MEM_MAP] THEN
PAXTAC THEN
ASM_REWRITE_TAC [operationsTheory.request_to_write_addresses]
QED

Theorem INVARIANT_EXTERNAL_FETCH_BD_REPLY_IMPLIES_EXTERNAL_BD_ADDRESSES_LEMMA:
!device_characteristics memory device channel_id.
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device /\
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  EXTERNAL_BD_ADDRESSES device_characteristics channel_id memory device.dma_state.internal_state (schannel device channel_id)
Proof
INTRO_TAC THEN
PTAC EXTERNAL_BD_ADDRESSES THEN
INTRO_TAC THEN
PTAC INVARIANT_EXTERNAL_FETCH_BD_REPLY THEN
AIRTAC THEN
STAC
QED

Theorem CHANNEL_BD_QUEUES_EQ_CHANNEL_BDS_LEMMA:
!device_characteristics channel_id memory internal_state device channel_id.
  channel_bd_queues device_characteristics channel_id memory device.dma_state.internal_state (schannel device channel_id) =
  channel_bds device_characteristics memory device.dma_state channel_id
Proof
REPEAT GEN_TAC THEN
ETAC channel_bd_queues THEN
ETAC channel_bds THEN
ETAC stateTheory.schannel THEN
LETS_TAC THEN
STAC
QED

Theorem UPDATE_DEVICE_STATE_NOT_ADDING_BDS_LEMMA:
!device_characteristics memory channel_id device1 device2 internal_state1
 internal_state2 channel1 channel2 channel_bd_queues1 channel_bd_queues2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  OTHER_BDS_TO_FETCH_EQ device_characteristics channel_id memory internal_state1 internal_state2 /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  channel2 = schannel device2 channel_id /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  channel_bd_queues1 = channel_bd_queues device_characteristics channel_id memory internal_state1 channel1 /\
  channel_bd_queues2 = channel_bd_queues device_characteristics channel_id memory internal_state2 channel2 /\
  CHANNEL_SET channel_bd_queues2 SUBSET CHANNEL_SET channel_bd_queues1
  ==>
  CHANNEL_BD_QUEUES_SUBSET device_characteristics memory device1 device2
Proof
REWRITE_TAC [CHANNEL_BD_QUEUES_SUBSET] THEN
INTRO_TAC THEN
INTRO_TAC THEN
Cases_on ‘channel_id = channel_id'’ THENL
[
 RLTAC THEN IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN ALL_LRTAC THEN STAC
 ,
 ITAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN
 ITAC OTHER_BDS_TO_FETCH_EQ_PRESERVES_BDS_TO_FETCH_LEMMA THEN
 AIRTAC THEN
 ALL_LRTAC THEN
 REWRITE_TAC [channel_bd_queues] THEN
 LETS_TAC THEN
 RLTAC THEN
 RLTAC THEN
 RLTAC THEN
 REWRITE_TAC [pred_setTheory.SUBSET_REFL]
]
QED

Theorem CHANNEL_BD_QUEUES_SUBSET_TRANSFERS_MEM_LEMMA:
!device_characteristics memory device1 device2 bd channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  CHANNEL_BD_QUEUES_SUBSET device_characteristics memory device1 device2 /\
  MEM bd (channel_bd_queues device_characteristics channel_id memory device2.dma_state.internal_state (schannel device2 channel_id))
  ==>
  MEM bd (channel_bd_queues device_characteristics channel_id memory device1.dma_state.internal_state (schannel device1 channel_id))
Proof
REWRITE_TAC [CHANNEL_BD_QUEUES_SUBSET] THEN
REWRITE_TAC [pred_setTheory.SUBSET_DEF] THEN
REWRITE_TAC [CHANNEL_SET] THEN
REWRITE_TAC [SET_ETA_LEMMA] THEN
REWRITE_TAC [pred_setTheory.GSPEC_ETA] THEN
REWRITE_TAC [IN_MEM_ABS_EQ_MEM_LEMMA] THEN
INTRO_TAC THEN
AIRTAC THEN
AIRTAC THEN
STAC
QED

Theorem BD_TRANSFER_RAS_WAS_PRESERVES_BD_DMA_WRITE_ADDRESSES_LEMMA:
!device_characteristics device1 device2 channel_id was bd.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state /\
  was = SND ((cverification device_characteristics channel_id).bd_transfer_ras_was device2.dma_state.internal_state bd)
  ==>
  was = SND ((cverification device_characteristics channel_id).bd_transfer_ras_was device1.dma_state.internal_state bd)
Proof
INTRO_TAC THEN
ETAC stateTheory.BD_TRANSFER_RAS_WAS_EQ THEN
AIRTAC THEN
STAC
QED

val _ = export_theory();
