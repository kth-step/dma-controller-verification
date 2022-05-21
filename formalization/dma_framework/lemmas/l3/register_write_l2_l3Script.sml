open HolKernel Parse boolLib bossLib helper_tactics;
open proof_obligationsTheory;
open l2Theory invariant_l2Theory proof_obligations_cpu_l2Theory l3Theory L23EQTheory;

val _ = new_theory "register_write_l2_l3";

Theorem IS_VALID_L2_EQ_IS_VALID_L3:
is_valid_l2 = is_valid_l3
Proof
REWRITE_TAC [is_valid_l2, is_valid_l3, boolTheory.FUN_EQ_THM]
QED

Theorem INTERNAL_STATES_EQ_REGISTER_WRITE_PRESERVES_INTERNAL_STATE_EQUAL_NEW_REQUESTS_LEMMA:
!devicea deviceb address_bytes internal_statea internal_stateb new_requestsa new_requestsb register_write.
  INTERNAL_STATES_EQ devicea deviceb /\
  (internal_statea, new_requestsa) = register_write devicea.dma_state.internal_state address_bytes /\
  (internal_stateb, new_requestsb) = register_write deviceb.dma_state.internal_state address_bytes
  ==>
  internal_statea = internal_stateb /\
  new_requestsa = new_requestsb
Proof
INTRO_TAC THEN
ETAC stateTheory.INTERNAL_STATES_EQ THEN
RLTAC THEN
RLTAC THEN
EQ_PAIR_ASM_TAC THEN
STAC
QED

Theorem DMA_REGISTER_WRITE_L2_L3_LEMMA:
!device_characteristics device21 device31 device22 memory cpu_address_bytes dma_address_bytes.
  INTERNAL_STATES_EQ device21 device31 /\
  (device22, dma_address_bytes) = dma_register_write device_characteristics is_valid_l2 (SOME memory) device21 cpu_address_bytes
  ==>
  ?device32.
    (device32, dma_address_bytes) = dma_register_write device_characteristics is_valid_l3 NONE device31 cpu_address_bytes
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_register_write THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
EXISTS_EQ_TAC THEN
PTAC operationsTheory.dma_register_write THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 2 THEN
IRTAC INTERNAL_STATES_EQ_REGISTER_WRITE_PRESERVES_INTERNAL_STATE_EQUAL_NEW_REQUESTS_LEMMA THEN
NLRTAC 2 THEN
ETAC IS_VALID_L2_EQ_IS_VALID_L3 THEN
RLTAC THEN
RLTAC THEN
NRLTAC 2 THEN
NRLTAC 2 THEN
RLTAC THEN
STAC
QED

Theorem DMA_REGISTER_WRITE_L3_L2_LEMMA:
!device_characteristics device21 device31 device32 cpu_address_bytes dma_address_bytes.
  INTERNAL_STATES_EQ device21 device31 /\
  (device32, dma_address_bytes) = dma_register_write device_characteristics is_valid_l3 NONE device31 cpu_address_bytes
  ==>
  !memory.
    ?device22.
      (device22, dma_address_bytes) = dma_register_write device_characteristics is_valid_l2 (SOME memory) device21 cpu_address_bytes
Proof
INTRO_TAC THEN
GEN_TAC THEN
PTAC operationsTheory.dma_register_write THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
EXISTS_EQ_TAC THEN
PTAC operationsTheory.dma_register_write THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 2 THEN
IRTAC INTERNAL_STATES_EQ_REGISTER_WRITE_PRESERVES_INTERNAL_STATE_EQUAL_NEW_REQUESTS_LEMMA THEN
NLRTAC 2 THEN
ETAC IS_VALID_L2_EQ_IS_VALID_L3 THEN
RLTAC THEN
RLTAC THEN
NRLTAC 2 THEN
NRLTAC 2 THEN
RLTAC THEN
STAC
QED

Definition ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS:
ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device1 device2 internal_state pending_requests = (
  device2 = device1 with dma_state := device1.dma_state with
            <|internal_state := internal_state;
              pending_register_related_memory_requests := pending_requests|>
)
End

Theorem INTERNAL_STATE_PENDING_REGISTER_RELATED_REQUESTS_PRESERVS_L23EQ_LEMMA:
!device_characteristics memory device21 device31 device22 device32 internal_state pending_requests.
  BDS_TO_FETCH_EQ device_characteristics memory device31.dma_state.internal_state internal_state /\
  L23EQ device_characteristics memory device21 device31 /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device21 device22 internal_state pending_requests /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device31 device32 internal_state pending_requests
  ==>
  L23EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
ETAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
ETAC L23EQ THEN
CONJS_TAC THENL
[
 ALL_LRTAC THEN
 ETAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
 INTRO_TAC THEN
 AITAC THEN
 ETAC stateTheory.schannel THEN
 RECORD_TAC THEN
 PTAC stateTheory.BDS_TO_FETCH_EQ THEN
 AIRTAC THEN
 STAC
 ,
 ETAC stateTheory.BDS_TO_UPDATE_EQ THEN 
 INTRO_TAC THEN
 AIRTAC THEN
 ALL_LRTAC THEN
 ETAC stateTheory.schannel THEN
 RECORD_TAC THEN
 STAC
 ,
 ETAC stateTheory.BDS_TO_PROCESS_EQ THEN
 INTRO_TAC THEN
 AIRTAC THEN
 ALL_LRTAC THEN
 ETAC stateTheory.schannel THEN
 RECORD_TAC THEN
 STAC
 ,
 ETAC stateTheory.BDS_TO_WRITE_BACK_EQ THEN
 INTRO_TAC THEN
 AIRTAC THEN
 ALL_LRTAC THEN
 ETAC stateTheory.schannel THEN
 RECORD_TAC THEN
 STAC
 ,
 ETAC stateTheory.MEMORY_REQUESTS_REPLIES_EQ THEN
 ASM_REWRITE_TAC [] THEN
 RECORD_TAC THEN
 ASM_REWRITE_TAC [] THEN
 INTRO_TAC THEN
 AIRTAC THEN
 ETAC stateTheory.schannel THEN
 RECORD_TAC THEN
 STAC
 ,
 ETAC stateTheory.FUNCTION_STATES_EQ THEN ALL_LRTAC THEN RECORD_TAC THEN STAC
 ,
 ETAC stateTheory.INTERNAL_STATES_EQ THEN ALL_LRTAC THEN RECORD_TAC THEN STAC
 ,
 ETAC stateTheory.DEFINED_CHANNELS_EQ THEN ALL_LRTAC THEN RECORD_TAC THEN STAC
]
QED

(*
Theorem CPU_APPENDS_INTERNAL_BDS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 address_bytes cpu_transition memory cpu1 cpu2 internal_state2 INVARIANT_CPU requests.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  (internal_state2, requests) = device_characteristics.dma_characteristics.register_write device.dma_state.internal_state address_bytes
  ==>
  REGISTER_WRITE_APPENDS_CONCRETE_BDS_EXTERNAL_R_W device_characteristics memory device.dma_state.internal_state internal_state2
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W THEN
AIRTAC THEN
STAC
QED
*)

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

Theorem CPU_APPENDS_INTERNAL_BDS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 cpu_address_bytes cpu_transition memory1 memory2 cpu1 cpu2 INVARIANT_CPU dma_address_bytes.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write cpu_address_bytes) cpu2 /\
  (device2, dma_address_bytes) = dma_register_write device_characteristics is_valid_l2 (SOME memory1) device1 cpu_address_bytes /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W device_characteristics memory1 memory2 device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_register_write THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 2 THEN
PTAC PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W THEN
ETAC FILTER_IS_VALID_L2_ID_LEMMA THEN
AIRTAC THEN
IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
LRTAC THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem REGISTER_WRITE_APPENDS_ASSIGN_INTERNAL_STATE_IMPLIES_BDS_TO_FETCH_EQS_EXISTS_LEMMA:
!device_characteristics channel_id memory1 memory2 device1 device2 internal_state requests.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W device_characteristics memory1 memory2 device1.dma_state.internal_state internal_state /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device1 device2 internal_state requests
  ==>
  (cverification device_characteristics channel_id).bds_to_fetch memory2 device2.dma_state.internal_state =
  (cverification device_characteristics channel_id).bds_to_fetch memory2 internal_state /\
  ?appended_bds.
    (cverification device_characteristics channel_id).bds_to_fetch memory2 device2.dma_state.internal_state =
    ((cverification device_characteristics channel_id).bds_to_fetch memory1 device1.dma_state.internal_state) ++ appended_bds
Proof
INTRO_TAC THEN
ETAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [] THEN
ETAC REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W THEN
AIRTAC THEN
AXTAC THEN
PAXTAC THEN
STAC
QED

Theorem ASSIGN_INTERNAL_STATE_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id device1 device2 internal_state requests.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device1 device2 internal_state requests
  ==>
  (schannel device2 channel_id).queue.bds_to_fetch = (schannel device1 channel_id).queue.bds_to_fetch /\
  !memory.
    (cverification device_characteristics channel_id).bds_to_fetch memory device2.dma_state.internal_state =
    (cverification device_characteristics channel_id).bds_to_fetch memory internal_state
Proof
INTRO_TAC THEN
ETAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_APPEND_INTERNAL_ABSTRACT_BDS_NONE_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics device1 device2 channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  device2 = dma_append_internal_abstract_bds device_characteristics NONE device1
  ==>
  !memory.
    (cverification device_characteristics channel_id).bds_to_fetch memory device2.dma_state.internal_state =
    (cverification device_characteristics channel_id).bds_to_fetch memory device1.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_append_internal_abstract_bds THEN
STAC
QED

(*
(I)
∃appended_bds.
            (cverification device_characteristics channel_id).bds_to_fetch
              memory device22.dma_state.internal_state =
            (schannel device21 channel_id).queue.bds_to_fetch ⧺ appended_bds


(II)
∃appended_bds.
            (cverification device_characteristics channel_id).bds_to_fetch
              memory device32.dma_state.internal_state =
            (cverification device_characteristics channel_id).bds_to_fetch
              memory device31.dma_state.internal_state ⧺ appended_bds


(III)
ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device21 device31
==>
(schannel device21 channel_id).queue.bds_to_fetch =
(cverification device_characteristics channel_id).bds_to_fetch memory device31.dma_state.internal_state


(IV)
ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device31 device32 internal_state requests
==>
(cverification device_characteristics channel_id).bds_to_fetch memory device32.dma_state.internal_state =
(cverification device_characteristics channel_id).bds_to_fetch memory internal_state


(V)
ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device21 device22 internal_state requests
==>
(schannel device22 channel_id).queue.bds_to_fetch = (schannel device21 channel_id).queue.bds_to_fetch /\
(cverification device_characteristics channel_id).bds_to_fetch memory device22.dma_state.internal_state =
(cverification device_characteristics channel_id).bds_to_fetch memory internal_state


(VI)
(IV) + (V)
==>
(cverification device_characteristics channel_id).bds_to_fetch memory device32.dma_state.internal_state =
(cverification device_characteristics channel_id).bds_to_fetch memory device22.dma_state.internal_state


(VII)
(I) + (II) + (VI)
==>
appended_bds' = appended_bds
*)

Theorem DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics memory1 memory2 device21 device31 device22 device32 device23 device33 internal_state requests.
  REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W device_characteristics memory1 memory2 device31.dma_state.internal_state internal_state /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device21 device22 internal_state requests /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device31 device32 internal_state requests /\
  device23 = dma_append_internal_abstract_bds device_characteristics (SOME memory2) device22 /\
  device33 = dma_append_internal_abstract_bds device_characteristics NONE device32 /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory1 device21 device31
  ==>
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory2 device23 device33
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
AITAC THEN
PAT_X_ASSUM “VALID_CHANNEL_ID device_characteristics channel_id” (fn thm => ASSUME_TAC thm THEN ASSUME_TAC thm) THEN
IRTAC REGISTER_WRITE_APPENDS_ASSIGN_INTERNAL_STATE_IMPLIES_BDS_TO_FETCH_EQS_EXISTS_LEMMA THEN
PAT_X_ASSUM “VALID_CHANNEL_ID device_characteristics channel_id” (fn thm => ASSUME_TAC thm THEN ASSUME_TAC thm) THEN
IRTAC ASSIGN_INTERNAL_STATE_PRESERVES_BDS_TO_FETCH_LEMMA THEN
PAT_X_ASSUM “VALID_CHANNEL_ID device_characteristics channel_id” (fn thm => ASSUME_TAC thm THEN ASSUME_TAC thm) THEN
IRTAC DMA_APPEND_INTERNAL_ABSTRACT_BDS_NONE_PRESERVES_BDS_TO_FETCH_LEMMA THEN
QLRTAC THEN
AXTAC THEN
ASM_LR_RW_OTHERS_KEEP_TAC THEN
ETAC operationsTheory.dma_append_internal_abstract_bds THEN
IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL THEN
SPLIT_ASM_DISJS_TAC THENL
[
 ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH THEN
 ETAC operationsTheory.APPENDED_BDS THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 ETAC operationsTheory.NOT_EXTENDED_ABSTRACT_BDS_TO_FETCH_AND_UNCHANGED_CHANNEL THEN
 ETAC operationsTheory.EXTENDED_BDS THEN
 ASM_NOT_EXISTS_TO_FORALL_NOT_TAC THEN
 LRTAC THEN
 LRTAC THEN
 LRTAC THEN
 PAT_X_ASSUM “!x.P” (fn thm =>
 ASSUME_TAC (let val ty = (type_of o #1 o dest_forall o concl) thm in SPECL [mk_var ("appended_bds", ty)] thm end)) THEN
 CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
]
QED

Theorem ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_PRESERVES_BDS_TO_UPDATE_EQ_LEMMA:
!device_characteristics device21 device31 device22 device32 internal_state requests.
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device21 device22 internal_state requests /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device31 device32 internal_state requests /\
  BDS_TO_UPDATE_EQ device_characteristics device21 device31
  ==>
  BDS_TO_UPDATE_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_UPDATE_EQ THEN
INTRO_TAC THEN
AIRTAC THEN
ETAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
ALL_LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
STAC
QED

Theorem ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_PRESERVES_BDS_TO_PROCESS_EQ_LEMMA:
!device_characteristics device21 device31 device22 device32 internal_state requests.
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device21 device22 internal_state requests /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device31 device32 internal_state requests /\
  BDS_TO_PROCESS_EQ device_characteristics device21 device31
  ==>
  BDS_TO_PROCESS_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_PROCESS_EQ THEN
INTRO_TAC THEN
AIRTAC THEN
ETAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
ALL_LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
STAC
QED

Theorem ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_PRESERVES_BDS_TO_WRITE_BACK_EQ_LEMMA:
!device_characteristics device21 device31 device22 device32 internal_state requests.
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device21 device22 internal_state requests /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device31 device32 internal_state requests /\
  BDS_TO_WRITE_BACK_EQ device_characteristics device21 device31
  ==>
  BDS_TO_WRITE_BACK_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_WRITE_BACK_EQ THEN
INTRO_TAC THEN
AIRTAC THEN
ETAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
ALL_LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_BDS_TO_UPDATE_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device23 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device31 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device32 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device33 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 internal_state requests memory.
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device21 device22 internal_state requests /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device31 device32 internal_state requests /\
  device23 = dma_append_internal_abstract_bds device_characteristics (SOME memory) device22 /\
  device33 = dma_append_internal_abstract_bds device_characteristics NONE device32 /\
  BDS_TO_UPDATE_EQ device_characteristics device21 device31
  ==>
  BDS_TO_UPDATE_EQ device_characteristics device23 device33
Proof
INTRO_TAC THEN
FIRTAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_PRESERVES_BDS_TO_UPDATE_EQ_LEMMA THEN
ETAC operationsTheory.dma_append_internal_abstract_bds THEN
RLTAC THEN
ETAC stateTheory.BDS_TO_UPDATE_EQ THEN
INTRO_TAC THEN
AITAC THEN
RLTAC THEN
IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
IRTAC internal_operation_lemmasTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_UPDATE_LEMMA THEN
STAC
QED

Theorem DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_BDS_TO_PROCESS_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device23 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device31 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device32 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device33 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 internal_state requests memory.
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device21 device22 internal_state requests /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device31 device32 internal_state requests /\
  device23 = dma_append_internal_abstract_bds device_characteristics (SOME memory) device22 /\
  device33 = dma_append_internal_abstract_bds device_characteristics NONE device32 /\
  BDS_TO_PROCESS_EQ device_characteristics device21 device31
  ==>
  BDS_TO_PROCESS_EQ device_characteristics device23 device33
Proof
INTRO_TAC THEN
FIRTAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_PRESERVES_BDS_TO_PROCESS_EQ_LEMMA THEN
ETAC operationsTheory.dma_append_internal_abstract_bds THEN
RLTAC THEN
ETAC stateTheory.BDS_TO_PROCESS_EQ THEN
INTRO_TAC THEN
AITAC THEN
RLTAC THEN
IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
IRTAC internal_operation_lemmasTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_PROCESS_LEMMA THEN
STAC
QED

Theorem DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_BDS_TO_WRITE_BACK_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device23 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device31 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device32 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device33 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 internal_state requests memory.
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device21 device22 internal_state requests /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device31 device32 internal_state requests /\
  device23 = dma_append_internal_abstract_bds device_characteristics (SOME memory) device22 /\
  device33 = dma_append_internal_abstract_bds device_characteristics NONE device32 /\
  BDS_TO_WRITE_BACK_EQ device_characteristics device21 device31
  ==>
  BDS_TO_WRITE_BACK_EQ device_characteristics device23 device33
Proof
INTRO_TAC THEN
FIRTAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_PRESERVES_BDS_TO_WRITE_BACK_EQ_LEMMA THEN
ETAC operationsTheory.dma_append_internal_abstract_bds THEN
RLTAC THEN
ETAC stateTheory.BDS_TO_WRITE_BACK_EQ THEN
INTRO_TAC THEN
AITAC THEN
RLTAC THEN
IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
IRTAC internal_operation_lemmasTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_WRITE_BACK_LEMMA THEN
STAC
QED

Theorem ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_PRESERVES_MEMORY_REQUESTS_REPLIES_EQ_LEMMA:
!device_characteristics device21 device31 device22 device32 internal_state requests.
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device21 device22 internal_state requests /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device31 device32 internal_state requests /\
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device21 device31
  ==>
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.MEMORY_REQUESTS_REPLIES_EQ THEN
ETAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
ALL_LRTAC THEN
RECORD_TAC THEN
ASM_REWRITE_TAC [] THEN
INTRO_TAC THEN
AIRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_MEMORY_REQUESTS_REPLIES_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device23 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device31 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device32 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device33 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 internal_state requests memory.
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device21 device22 internal_state requests /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device31 device32 internal_state requests /\
  device23 = dma_append_internal_abstract_bds device_characteristics (SOME memory) device22 /\
  device33 = dma_append_internal_abstract_bds device_characteristics NONE device32 /\
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device21 device31
  ==>
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device23 device33
Proof
INTRO_TAC THEN
FIRTAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_PRESERVES_MEMORY_REQUESTS_REPLIES_EQ_LEMMA THEN
ETAC stateTheory.MEMORY_REQUESTS_REPLIES_EQ THEN
REPEAT CONJ_TAC THENL
[
 ETAC operationsTheory.dma_append_internal_abstract_bds THEN
 RLTAC THEN
 RLTAC THEN
 LRTAC THEN
 REPEAT (WEAKEN_TAC (fn _ => true)) THEN
 PTAC operationsTheory.dma_append_external_abstract_bds THEN
 RECORD_TAC THEN
 STAC
 ,
 ETAC operationsTheory.dma_append_internal_abstract_bds THEN
 RLTAC THEN
 RLTAC THEN
 LRTAC THEN
 REPEAT (WEAKEN_TAC (fn _ => true)) THEN
 PTAC operationsTheory.dma_append_external_abstract_bds THEN
 RECORD_TAC THEN
 STAC
 ,
 INTRO_TAC THEN
 AITAC THEN
 ETAC operationsTheory.dma_append_internal_abstract_bds THEN
 IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_PENDING_ACCESSES_LEMMA THEN
 STAC
]
QED

Theorem ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_PRESERVES_FUNCTION_STATES_EQ_LEMMA:
!device21 device31 device22 device32 internal_state requests.
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device21 device22 internal_state requests /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device31 device32 internal_state requests /\
  FUNCTION_STATES_EQ device21 device31
  ==>
  FUNCTION_STATES_EQ device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.FUNCTION_STATES_EQ THEN
ETAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_FUNCTION_STATES_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device23 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device31 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device32 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device33 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 internal_state requests memory.
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device21 device22 internal_state requests /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device31 device32 internal_state requests /\
  device23 = dma_append_internal_abstract_bds device_characteristics (SOME memory) device22 /\
  device33 = dma_append_internal_abstract_bds device_characteristics NONE device32 /\
  FUNCTION_STATES_EQ device21 device31
  ==>
  FUNCTION_STATES_EQ device23 device33
Proof
INTRO_TAC THEN
FIRTAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_PRESERVES_FUNCTION_STATES_EQ_LEMMA THEN
ETAC stateTheory.FUNCTION_STATES_EQ THEN
ETAC operationsTheory.dma_append_internal_abstract_bds THEN
PTAC operationsTheory.dma_append_external_abstract_bds THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_APPEND_INTERNAL_ABSTRACT_BDS_IMPLIES_INTERNAL_STATES_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device23 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device31 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device32 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device33 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 internal_state requests memory.
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device21 device22 internal_state requests /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device31 device32 internal_state requests /\
  device23 = dma_append_internal_abstract_bds device_characteristics (SOME memory) device22 /\
  device33 = dma_append_internal_abstract_bds device_characteristics NONE device32
  ==>
  INTERNAL_STATES_EQ device23 device33
Proof
INTRO_TAC THEN
ETAC stateTheory.INTERNAL_STATES_EQ THEN
ETAC operationsTheory.dma_append_internal_abstract_bds THEN
IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
ALL_LRTAC THEN
ETAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_PRESERVES_DEFINED_CHANNELS_EQ_LEMMA:
!device_characteristics device21 device31 device22 device32 internal_state requests.
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device21 device22 internal_state requests /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device31 device32 internal_state requests /\
  DEFINED_CHANNELS_EQ device_characteristics device21 device31
  ==>
  DEFINED_CHANNELS_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.DEFINED_CHANNELS_EQ THEN
ETAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_PRESERVES_DEFINED_CHANNELS_LEMMA:
!device_characteristics memory device21 device22 internal_state requests.
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device21 device22 internal_state requests /\
  INVARIANT_L2 device_characteristics memory device21
  ==>
  DEFINED_CHANNELS device_characteristics device22
Proof
INTRO_TAC THEN
IRTAC invariant_l2_lemmasTheory.INVARIANT_L2_IMPLIES_DEFINED_CHANNELS_LEMMA THEN
ETAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
ETAC stateTheory.DEFINED_CHANNELS THEN
ETAC stateTheory.VALID_CHANNELS THEN
INTRO_TAC THEN
AIRTAC THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_DEFINED_CHANNELS_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device23 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device31 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device32 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device33 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 internal_state requests memory1 memory2.
  INVARIANT_L2 device_characteristics memory1 device21 /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device21 device22 internal_state requests /\
  ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS device31 device32 internal_state requests /\
  device23 = dma_append_internal_abstract_bds device_characteristics (SOME memory2) device22 /\
  device33 = dma_append_internal_abstract_bds device_characteristics NONE device32 /\
  DEFINED_CHANNELS_EQ device_characteristics device21 device31
  ==>
  DEFINED_CHANNELS_EQ device_characteristics device23 device33
Proof
INTRO_TAC THEN
ITAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_PRESERVES_DEFINED_CHANNELS_LEMMA THEN
FIRTAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_PRESERVES_DEFINED_CHANNELS_EQ_LEMMA THEN
ETAC operationsTheory.dma_append_internal_abstract_bds THEN
ETAC stateTheory.DEFINED_CHANNELS_EQ THEN
GEN_TAC THEN
EQ_TAC THENL
[
 INTRO_TAC THEN
 Cases_on ‘VALID_CHANNEL_ID device_characteristics channel_id’ THENL
 [
  IRTAC state_lemmasTheory.DEFINED_VALID_CHANNEL_IS_SOME_LEMMA THEN QLRTAC THEN QLRTAC THEN STAC
  ,
  IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_SOME_PRESERVED_LEMMA THEN QLRTAC THEN QLRTAC THEN STAC
 ]
 ,
 INTRO_TAC THEN
 Cases_on ‘VALID_CHANNEL_ID device_characteristics channel_id’ THENL
 [
  ITAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_SOME_LEMMA THEN STAC
  ,
  IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_SOME_PRESERVED_LEMMA THEN RLTAC THEN QRLTAC THEN STAC
 ]
]
QED


























        
Theorem INVARIANT_L2_IMPLIES_INVARIANT_FETCH_BD_L2_LEMMA:
!device_characteristics memory device.
  INVARIANT_L2 device_characteristics memory device
  ==>
  INVARIANT_FETCH_BD_L2 device_characteristics memory device
Proof
INTRO_TAC THEN
PTAC INVARIANT_L2 THEN
STAC
QED

Theorem DMA_REGISTER_WRITE_UPDATES_INTERNAL_STATE_LEMMA:
!device_characteristics memory_option device1 device2 cpu_address_bytes dma_address_bytes.
  (device2, dma_address_bytes) = dma_register_write device_characteristics is_valid_l2 memory_option device1 cpu_address_bytes
  ==>
  ?internal_state2 new_requests.
    (internal_state2, new_requests) = device_characteristics.dma_characteristics.register_write device1.dma_state.internal_state cpu_address_bytes /\
    device2.dma_state.internal_state = internal_state2
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_register_write THEN
IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
EQ_PAIR_ASM_TAC THEN
RLTAC THEN
LRTAC THEN
RLTAC THEN
LRTAC THEN
LRTAC THEN
RECORD_TAC THEN
LRTAC THEN
LRTAC THEN
LRTAC THEN
PAXTAC THEN
STAC
QED

Theorem DMA_REGISTER_WRITE_BSIM_L23EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device31 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device32 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory1 memory2 address_bytes cpu_transition cpu1 cpu2 INVARIANT_CPU dma_address_bytes.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_L2 device_characteristics memory1 device21 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  L23EQ device_characteristics memory1 device21 device31 /\
  (device22, dma_address_bytes) = dma_register_write device_characteristics is_valid_l2 (SOME memory1) device21 address_bytes /\
  (device32, dma_address_bytes) = dma_register_write device_characteristics is_valid_l3 NONE device31 address_bytes /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  L23EQ device_characteristics memory2 device22 device32
Proof
INTRO_TAC THEN
ITAC CPU_APPENDS_INTERNAL_BDS_LEMMA THEN
ITAC DMA_REGISTER_WRITE_UPDATES_INTERNAL_STATE_LEMMA THEN
AXTAC THEN
ETAC operationsTheory.dma_register_write THEN
BSIM_ONCE_LETS_TAC THEN
LRTAC THEN
BSIM_ONCE_LETS_TAC THEN
WEAKEN_TAC (fn assumption => (is_eq assumption) andalso ((is_var o lhs) assumption)) THEN
BSIM_ONCE_LETS_TAC THEN
ITAC L23EQ_lemmasTheory.L23EQ_IMPLIES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_EQ_LEMMA THEN
LRTAC THEN
RLTAC THEN
LRTAC THEN
BSIM_ONCE_LETS_TAC THEN
ITAC L23EQ_lemmasTheory.L23EQ_IMPLIES_INTERNAL_STATE_EQ_LEMMA THEN
RLTAC THEN
ASM_LR_RW_OTHERS_KEEP_TAC THEN
EQ_PAIR_ASM_TAC THEN
NLRTAC 2 THEN
ETAC IS_VALID_L2_EQ_IS_VALID_L3 THEN
BSIM_ONCE_LETS_TAC THEN
WEAKEN_TAC (fn assumption => (is_eq assumption) andalso ((is_var o lhs) assumption)) THEN
BSIM_ONCE_LETS_TAC THEN
WEAKEN_TAC (fn assumption => (is_eq assumption) andalso ((is_var o lhs) assumption)) THEN
BSIM_ONCE_LETS_TAC THEN
WEAKEN_TAC (fn assumption => (is_eq assumption) andalso ((is_var o lhs) assumption)) THEN
BSIM_ONCE_LETS_TAC THEN
WEAKEN_TAC (fn assumption => (is_eq assumption) andalso ((is_var o lhs) assumption)) THEN
BSIM_ONCE_LETS_TAC THEN
BSIM_ONCE_LETS_TAC THEN
LRTAC THEN
PTAC operationsTheory.update_memory_option THEN
LRTAC THEN
PTAC operationsTheory.update_memory_option THEN
BSIM_ONCE_LETS_TAC THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 2 THEN
RLTAC THEN
RLTAC THEN
RLTAC THEN
ETAC ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
ITAC L23EQ_lemmasTheory.L23EQ_IMPLIES_INTERNAL_STATE_EQ_LEMMA THEN
LRTAC THEN
ETAC L23EQ THEN
CONJS_TAC THENL
[
 FIRTAC DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA THEN STAC
 ,
 FIRTAC DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_BDS_TO_UPDATE_EQ_LEMMA THEN STAC
 ,
 FIRTAC DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_BDS_TO_PROCESS_EQ_LEMMA THEN STAC
 ,
 FIRTAC DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_BDS_TO_WRITE_BACK_EQ_LEMMA THEN STAC
 ,
 FIRTAC DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_MEMORY_REQUESTS_REPLIES_EQ_LEMMA THEN STAC
 ,
 FIRTAC DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_FUNCTION_STATES_EQ_LEMMA THEN STAC
 ,
 INST_IMP_TAC DMA_APPEND_INTERNAL_ABSTRACT_BDS_IMPLIES_INTERNAL_STATES_EQ_LEMMA THEN STAC
 ,
 FIRTAC DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_DEFINED_CHANNELS_EQ_LEMMA THEN STAC
]
QED

Theorem L23EQ_IMPLIES_INTERNAL_STATES_EQ_LEMMA:
!device_characteristics memory device21 device31.
  L23EQ device_characteristics memory device21 device31
  ==>
  INTERNAL_STATES_EQ device21 device31
Proof
INTRO_TAC THEN
ETAC L23EQ THEN
STAC
QED

Theorem DMA_REGISTER_WRITE_L2_L3_L23EQ_LEMMA:
!device_characteristics device21 device31 device22 memory1 memory2
 cpu_address_bytes dma_address_bytes cpu1 cpu2 cpu_transition INVARIANT_CPU.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_L2 device_characteristics memory1 device21 /\
  cpu_transition cpu1 (cpu_memory_write cpu_address_bytes) cpu2 /\
  L23EQ device_characteristics memory1 device21 device31 /\
  (device22, dma_address_bytes) = dma_register_write device_characteristics is_valid_l2 (SOME memory1) device21 cpu_address_bytes /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  ?device32.
    (device32, dma_address_bytes) = dma_register_write device_characteristics is_valid_l3 NONE device31 cpu_address_bytes /\
    L23EQ device_characteristics memory2 device22 device32
Proof
INTRO_TAC THEN
ITAC L23EQ_IMPLIES_INTERNAL_STATES_EQ_LEMMA THEN
ITAC DMA_REGISTER_WRITE_L2_L3_LEMMA THEN
AXTAC THEN
PAXTAC THEN
CONJ_TAC THEN TRY STAC THEN
IRTAC DMA_REGISTER_WRITE_BSIM_L23EQ_LEMMA THEN
STAC
QED

Theorem DMA_REGISTER_WRITE_L3_L2_L23EQ_LEMMA:
!device_characteristics device21 device31 device32 memory1 memory2
 cpu_address_bytes dma_address_bytes cpu1 cpu2 cpu_transition INVARIANT_CPU.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_L2 device_characteristics memory1 device21 /\
  cpu_transition cpu1 (cpu_memory_write cpu_address_bytes) cpu2 /\
  L23EQ device_characteristics memory1 device21 device31 /\
  (device32, dma_address_bytes) = dma_register_write device_characteristics is_valid_l3 NONE device31 cpu_address_bytes /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  ?device22.
    (device22, dma_address_bytes) = dma_register_write device_characteristics is_valid_l2 (SOME memory1) device21 cpu_address_bytes /\
    L23EQ device_characteristics memory2 device22 device32
Proof
INTRO_TAC THEN
ITAC L23EQ_IMPLIES_INTERNAL_STATES_EQ_LEMMA THEN
ITAC DMA_REGISTER_WRITE_L3_L2_LEMMA THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (Q.SPEC ‘memory1’ thm)) THEN
AXTAC THEN
PAXTAC THEN
CONJ_TAC THEN TRY STAC THEN
IRTAC DMA_REGISTER_WRITE_BSIM_L23EQ_LEMMA THEN
STAC
QED

Theorem FUNCTION_REGISTER_WRITE_PRESERVES_CHANNELS_LEMMA:
!device_characteristics device1 device2 addresses.
  device2 = function_register_write device_characteristics device1 addresses
  ==>
  !channel_id. (schannel device2 channel_id) = (schannel device1 channel_id)
Proof
INTRO_TAC THEN
GEN_TAC THEN
PTAC operationsTheory.function_register_write THEN
LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
STAC
QED

Theorem FUNCTION_REGISTER_WRITE_L2_L3_L23EQ_LEMMA:
!device_characteristics device21 device31 device22 memory address_bytes.
  L23EQ device_characteristics memory device21 device31 /\
  device22 = function_register_write device_characteristics device21 address_bytes
  ==>
  ?device32.
    device32 = function_register_write device_characteristics device31 address_bytes /\
    L23EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
ITAC FUNCTION_REGISTER_WRITE_PRESERVES_CHANNELS_LEMMA THEN
PTAC operationsTheory.function_register_write THEN
PTAC operationsTheory.function_register_write THEN
ITAC L23EQ_lemmasTheory.L23EQ_IMPLIES_FUNCTION_STATE_EQ_LEMMA THEN
RLTAC THEN
RLTAC THEN
LRTAC THEN
EXISTS_EQ_TAC THEN
LRTAC THEN
ETAC L23EQ THEN
RW_HYPS_TAC stateTheory.schannel THEN
RECORD_TAC THEN
REPEAT CONJ_TAC THENL
[
 ETAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
 REWRITE_TAC [stateTheory.schannel] THEN
 RECORD_TAC THEN
 INTRO_TAC THEN
 AIRTAC THEN
 ETAC stateTheory.schannel THEN
 RECORD_TAC THEN
 STAC
 ,
 ETAC stateTheory.BDS_TO_UPDATE_EQ THEN
 REWRITE_TAC [stateTheory.schannel] THEN
 RECORD_TAC THEN
 INTRO_TAC THEN
 AIRTAC THEN
 ETAC stateTheory.schannel THEN
 RECORD_TAC THEN
 STAC
 ,
 ETAC stateTheory.BDS_TO_PROCESS_EQ THEN
 REWRITE_TAC [stateTheory.schannel] THEN
 RECORD_TAC THEN
 INTRO_TAC THEN
 AIRTAC THEN
 ETAC stateTheory.schannel THEN
 RECORD_TAC THEN
 STAC
 ,
 ETAC stateTheory.BDS_TO_WRITE_BACK_EQ THEN
 REWRITE_TAC [stateTheory.schannel] THEN
 RECORD_TAC THEN
 INTRO_TAC THEN
 AIRTAC THEN
 ETAC stateTheory.schannel THEN
 RECORD_TAC THEN
 STAC
 ,
 ETAC stateTheory.MEMORY_REQUESTS_REPLIES_EQ THEN
 RECORD_TAC THEN
 ASM_REWRITE_TAC [] THEN
 INTRO_TAC THEN
 AIRTAC THEN
 ETAC stateTheory.schannel THEN
 RECORD_TAC THEN
 STAC
 ,
 ETAC stateTheory.FUNCTION_STATES_EQ THEN RECORD_TAC THEN STAC
 ,
 ETAC stateTheory.INTERNAL_STATES_EQ THEN RECORD_TAC THEN STAC
 ,
 ETAC stateTheory.DEFINED_CHANNELS_EQ THEN RECORD_TAC THEN STAC
]
QED

Theorem FUNCTION_REGISTER_WRITE_L3_L2_L23EQ_LEMMA:
!device_characteristics device21 device31 device32 memory address_bytes.
  L23EQ device_characteristics memory device21 device31 /\
  device32 = function_register_write device_characteristics device31 address_bytes
  ==>
  ?device22.
    device22 = function_register_write device_characteristics device21 address_bytes /\
    L23EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
ITAC FUNCTION_REGISTER_WRITE_PRESERVES_CHANNELS_LEMMA THEN
PTAC operationsTheory.function_register_write THEN
PTAC operationsTheory.function_register_write THEN
ITAC L23EQ_lemmasTheory.L23EQ_IMPLIES_FUNCTION_STATE_EQ_LEMMA THEN
RLTAC THEN
RLTAC THEN
RLTAC THEN
EXISTS_EQ_TAC THEN
LRTAC THEN
ETAC L23EQ THEN
RW_HYPS_TAC stateTheory.schannel THEN
RECORD_TAC THEN
REPEAT CONJ_TAC THENL
[
 ETAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
 REWRITE_TAC [stateTheory.schannel] THEN
 RECORD_TAC THEN
 INTRO_TAC THEN
 AIRTAC THEN
 ETAC stateTheory.schannel THEN
 RECORD_TAC THEN
 STAC
 ,
 ETAC stateTheory.BDS_TO_UPDATE_EQ THEN
 REWRITE_TAC [stateTheory.schannel] THEN
 RECORD_TAC THEN
 INTRO_TAC THEN
 AIRTAC THEN
 ETAC stateTheory.schannel THEN
 RECORD_TAC THEN
 REPEAT (WEAKEN_TAC (not o is_eq)) THEN
 STAC
 ,
 ETAC stateTheory.BDS_TO_PROCESS_EQ THEN
 REWRITE_TAC [stateTheory.schannel] THEN
 RECORD_TAC THEN
 INTRO_TAC THEN
 AIRTAC THEN
 ETAC stateTheory.schannel THEN
 RECORD_TAC THEN
 REPEAT (WEAKEN_TAC (not o is_eq)) THEN
 STAC
 ,
 ETAC stateTheory.BDS_TO_WRITE_BACK_EQ THEN
 REWRITE_TAC [stateTheory.schannel] THEN
 RECORD_TAC THEN
 INTRO_TAC THEN
 AIRTAC THEN
 ETAC stateTheory.schannel THEN
 RECORD_TAC THEN
 REPEAT (WEAKEN_TAC (not o is_eq)) THEN
 STAC
 ,
 ETAC stateTheory.MEMORY_REQUESTS_REPLIES_EQ THEN
 RECORD_TAC THEN
 ASM_REWRITE_TAC [] THEN
 INTRO_TAC THEN
 AIRTAC THEN
 ETAC stateTheory.schannel THEN
 RECORD_TAC THEN
 REPEAT (WEAKEN_TAC (not o is_eq)) THEN
 STAC
 ,
 ETAC stateTheory.FUNCTION_STATES_EQ THEN RECORD_TAC THEN STAC
 ,
 ETAC stateTheory.INTERNAL_STATES_EQ THEN RECORD_TAC THEN STAC
 ,
 ETAC stateTheory.DEFINED_CHANNELS_EQ THEN RECORD_TAC THEN STAC
]
QED

Theorem DEVICE_SIM_L2_L3_REGISTER_WRITE_LEMMA:
!device_characteristics device21 device31 device22 memory1 memory2
 cpu_address_bytes dma_address_bytes cpu1 cpu2 cpu_transition INVARIANT_CPU.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_L2 device_characteristics memory1 device21 /\
  cpu_transition cpu1 (cpu_memory_write cpu_address_bytes) cpu2 /\
  L23EQ device_characteristics memory1 device21 device31 /\
  (device22, dma_address_bytes) = device_register_write_l2 device_characteristics memory1 device21 cpu_address_bytes /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  ?device32.
    (device32, dma_address_bytes) = device_register_write_l3 device_characteristics device31 cpu_address_bytes /\
    L23EQ device_characteristics memory2 device22 device32
Proof
INTRO_TAC THEN
PTAC device_register_write_l2 THEN
PTAC device_register_write_l3 THEN
PTAC operationsTheory.device_register_write THEN PTAC operationsTheory.device_register_write THENL
[
 IRTAC DMA_REGISTER_WRITE_L2_L3_L23EQ_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ITAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
 IRTAC FUNCTION_REGISTER_WRITE_L2_L3_L23EQ_LEMMA THEN
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN
 AXTAC THEN
 PAXTAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN
 EXISTS_EQ_TAC THEN
 ITAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN
 EXISTS_EQ_TAC THEN
 ITAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
 STAC
]
QED

Theorem DEVICE_SIM_L3_L2_REGISTER_WRITE_LEMMA:
!device_characteristics device21 device31 device32 memory1 memory2
 cpu_address_bytes dma_address_bytes cpu1 cpu2 cpu_transition INVARIANT_CPU.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  INVARIANT_L2 device_characteristics memory1 device21 /\
  cpu_transition cpu1 (cpu_memory_write cpu_address_bytes) cpu2 /\
  L23EQ device_characteristics memory1 device21 device31 /\
  (device32, dma_address_bytes) = device_register_write_l3 device_characteristics device31 cpu_address_bytes /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  ?device22.
    (device22, dma_address_bytes) = device_register_write_l2 device_characteristics memory1 device21 cpu_address_bytes /\
    L23EQ device_characteristics memory2 device22 device32
Proof
INTRO_TAC THEN
PTAC device_register_write_l2 THEN
PTAC device_register_write_l3 THEN
PTAC operationsTheory.device_register_write THEN PTAC operationsTheory.device_register_write THENL
[
 IRTAC DMA_REGISTER_WRITE_L3_L2_L23EQ_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ITAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
 IRTAC FUNCTION_REGISTER_WRITE_L3_L2_L23EQ_LEMMA THEN
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN
 AXTAC THEN
 PAXTAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN
 EXISTS_EQ_TAC THEN
 ITAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN
 EXISTS_EQ_TAC THEN
 ITAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
 STAC
]
QED

val _ = export_theory();

