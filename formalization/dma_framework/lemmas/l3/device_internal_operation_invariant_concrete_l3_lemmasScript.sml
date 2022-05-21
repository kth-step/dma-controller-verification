open HolKernel Parse boolLib bossLib helper_tactics;
open l3Theory invariant_l3Theory;

val _ = new_theory "device_internal_operation_invariant_concrete_l3_lemmas";

Theorem SCHEDULER_OPERATION_IMPLIES_CHANNELS_EQ_LEMMA:
!device_characteristics device1 device2 channel_id operation environment.
  (device2, channel_id, operation) = scheduler_operation device_characteristics device1 environment
  ==>
  CHANNELS_EQ device1 device2
Proof
INTRO_TAC THEN
PTAC operationsTheory.scheduler_operation THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 3 THEN
LRTAC THEN
ETAC stateTheory.CHANNELS_EQ THEN
RECORD_TAC THEN
STAC
QED

Theorem SCHEDULER_OPERATION_IMPLIES_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics memory device1 device2 channel_id operation environment.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH device_characteristics /\
  (device2, channel_id, operation) = scheduler_operation device_characteristics device1 environment
  ==>
  BDS_TO_FETCH_EQ device_characteristics memory device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC operationsTheory.scheduler_operation THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 3 THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH THEN
AIRTAC THEN
ETAC stateTheory.BDS_TO_FETCH_EQ THEN
ALL_LRTAC THEN
RECORD_TAC THEN
INTRO_TAC THEN
AIRTAC THEN
STAC
QED

(*
Theorem SCHEDULER_OPERATION_IMPLIES_SCRATCHPAD_ADDRESSES_EQ_LEMMA:
!device_characteristics device1 device2 channel_id operation environment.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_SCRATCHPAD device_characteristics /\
  (device2, channel_id, operation) = scheduler_operation device_characteristics device1 environment
  ==>
  SCRATCHPAD_ADDRESSES_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC operationsTheory.scheduler_operation THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 3 THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_SCHEDULER_PRESERVES_SCRATCHPAD THEN
AIRTAC THEN
ETAC stateTheory.SCRATCHPAD_ADDRESSES_EQ THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED
*)

Theorem SCHEDULER_OPERATION_IMPLIES_VALID_CHANNEL_ID_LEMMA:
!device_characteristics channel_id device1 device2 operation environment.
  PROOF_OBLIGATION_SCHEDULER device_characteristics /\
  (device2, channel_id, operation) = scheduler_operation device_characteristics device1 environment
  ==>
  VALID_CHANNEL_ID device_characteristics channel_id
Proof
INTRO_TAC THEN
PTAC operationsTheory.scheduler_operation THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_SCHEDULER THEN
AIRTAC THEN
EQ_PAIR_ASM_TAC THEN
STAC
QED

Theorem SCHEDULER_OPERATION_IMPLIES_CHANNEL_BDS_EQ_LEMMA:
!device_characteristics device1 device2 memory environment channel_id operation.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH device_characteristics /\
  (device2, channel_id, operation) = scheduler_operation device_characteristics device1 environment
  ==>
  CHANNEL_BDS_EQ device_characteristics memory device1 device2
Proof
INTRO_TAC THEN
ETAC CHANNEL_BDS_EQ THEN
INTRO_TAC THEN
ETAC channel_bds THEN
LETS_TAC THEN
ITAC SCHEDULER_OPERATION_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
IRTAC SCHEDULER_OPERATION_IMPLIES_CHANNELS_EQ_LEMMA THEN
RW_HYPS_TAC stateTheory.BDS_TO_FETCH_EQ THEN
AIRTAC THEN
QRLTAC THEN
ETAC stateTheory.CHANNELS_EQ THEN
STAC
QED

Theorem SCHEDULER_OPERATION_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA:
!device_characteristics device1 device2 environment channel_id operation.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION device_characteristics /\
  (device2, channel_id, operation) = scheduler_operation device_characteristics device1 environment
  ==>
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
ETAC stateTheory.BD_TRANSFER_RAS_WAS_EQ THEN
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION THEN
PTAC operationsTheory.scheduler_operation THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 3 THEN
AIRTAC THEN
AIRTAC THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem SCHEDULER_OPERATION_IMPLIES_FETCH_BD_ADDRESSES_EQ_LEMMA:
!device_characteristics device1 device2 channel_id operation environment.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  (device2, channel_id, operation) = scheduler_operation device_characteristics device1 environment
  ==>
  FETCH_BD_ADDRESSES_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC operationsTheory.scheduler_operation THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 3 THEN
ETAC proof_obligationsTheory.PROOF_OBLIGATION_SCHEDULER_PRESERVES_FETCH_BD_ADDRESSES THEN
AIRTAC THEN
ETAC stateTheory.FETCH_BD_ADDRESSES_EQ THEN
ALL_LRTAC THEN
RECORD_TAC THEN
INTRO_TAC THEN
AIRTAC THEN
STAC
QED



Theorem SCHEDULER_OPERATION_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA:
!device_characteristics memory device1 device2 channel_id operation environment.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH device_characteristics /\ (*
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_SCRATCHPAD device_characteristics /\*)
  (device2, channel_id, operation) = scheduler_operation device_characteristics device1 environment /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device1
  ==>
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device2
Proof
INTRO_TAC THEN
ITAC SCHEDULER_OPERATION_IMPLIES_CHANNELS_EQ_LEMMA THEN
ITAC SCHEDULER_OPERATION_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
(*IRTAC SCHEDULER_OPERATION_IMPLIES_SCRATCHPAD_ADDRESSES_EQ_LEMMA THEN*)
IRTAC invariant_l3_lemmasTheory.CHANNELS_EQ_BDS_TO_FETCH_EQ_SCRATCHPAD_ADDRESSES_EQ_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA THEN
STAC
QED

Theorem SCHEDULER_OPERATION_PRESERVES_NOT_DMA_BDS_LEMMA:
!device_characteristics memory device1 device2 channel_id operation environment.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION device_characteristics /\
  (device2, channel_id, operation) = scheduler_operation device_characteristics device1 environment /\
  NOT_DMA_BDS device_characteristics memory device1
  ==>
  NOT_DMA_BDS device_characteristics memory device2
Proof
INTRO_TAC THEN
ITAC SCHEDULER_OPERATION_IMPLIES_CHANNEL_BDS_EQ_LEMMA THEN
ITAC SCHEDULER_OPERATION_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA THEN
ITAC invariant_l3_lemmasTheory.CHANNEL_BDS_EQ_BD_TRANSFER_RAS_WAS_EQ_PRESERVES_NOT_DMA_BDS_LEMMA THEN
STAC
QED

(*
Theorem SCHEDULER_OPERATION_PRESERVES_NOT_DMA_SCRATCHPAD_LEMMA:
!device_characteristics memory device1 device2 channel_id operation environment.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_SCRATCHPAD device_characteristics /\
  (device2, channel_id, operation) = scheduler_operation device_characteristics device1 environment /\
  NOT_DMA_SCRATCHPAD device_characteristics memory device1
  ==>
  NOT_DMA_SCRATCHPAD device_characteristics memory device2
Proof
INTRO_TAC THEN
ITAC SCHEDULER_OPERATION_IMPLIES_CHANNEL_BDS_EQ_LEMMA THEN
ITAC SCHEDULER_OPERATION_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA THEN
IRTAC SCHEDULER_OPERATION_IMPLIES_SCRATCHPAD_ADDRESSES_EQ_LEMMA THEN
IRTAC invariant_l3_lemmasTheory.CHANNEL_BDS_EQ_BD_TRANSFER_RAS_WAS_EQ_SCRATCHPAD_ADDRESSES_EQ_LEMMA THEN
STAC
QED
*)

Theorem SCHEDULER_OPERATION_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics device1 device2 channel_id operation environment.
  (device2, channel_id, operation) = scheduler_operation device_characteristics device1 environment /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device1
  ==>
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device2
Proof
INTRO_TAC THEN
ETAC MEMORY_WRITES_PRESERVES_BDS_TO_FETCH THEN
PTAC operationsTheory.scheduler_operation THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 3 THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem SCHEDULER_OPERATION_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA:
!device_characteristics memory device1 device2 channel_id operation environment.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  (device2, channel_id, operation) = scheduler_operation device_characteristics device1 environment /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device1
  ==>
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device2
Proof
INTRO_TAC THEN
ITAC SCHEDULER_OPERATION_IMPLIES_CHANNELS_EQ_LEMMA THEN
IRTAC SCHEDULER_OPERATION_IMPLIES_FETCH_BD_ADDRESSES_EQ_LEMMA THEN
IRTAC invariant_l3_lemmasTheory.FETCH_BD_ADDRESSES_EQ_CHANNELS_EQ_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA THEN
STAC
QED

Theorem SCHEDULER_OPERATION_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA:
!device_characteristics memory device1 device2 channel_id operation environment.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  (device2, channel_id, operation) = scheduler_operation device_characteristics device1 environment /\
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device1
  ==>
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ITAC SCHEDULER_OPERATION_IMPLIES_CHANNELS_EQ_LEMMA THEN
IRTAC SCHEDULER_OPERATION_IMPLIES_FETCH_BD_ADDRESSES_EQ_LEMMA THEN
IRTAC invariant_l3_lemmasTheory.CHANNELS_EQ_FETCH_BD_ADDRESSES_EQ_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA THEN
STAC
QED

Theorem SCHEDULER_OPERATION_PRESERVES_DEFINED_CHANNELS_LEMMA:
!device_characteristics device1 device2 channel_id operation environment.
  (device2, channel_id, operation) = scheduler_operation device_characteristics device1 environment /\
  DEFINED_CHANNELS device_characteristics device1
  ==>
  DEFINED_CHANNELS device_characteristics device2
Proof
INTRO_TAC THEN
ETAC stateTheory.DEFINED_CHANNELS THEN
PTAC operationsTheory.scheduler_operation THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 2 THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem SCHEDULER_OPERATION_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA:
!device_characteristics memory environment device1 device2 channel_id operation.
  PROOF_OBLIGATION_SCHEDULER device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH device_characteristics /\ (*
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_SCRATCHPAD device_characteristics /\*)
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  (device2, channel_id, operation) = scheduler_operation device_characteristics device1 environment /\
  INVARIANT_CONCRETE_L3 device_characteristics memory device1 /\
  DEFINED_CHANNELS device_characteristics device1
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory device2 /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  DEFINED_CHANNELS device_characteristics device2
Proof
INTRO_TAC THEN
CONJS_TAC THEN (TRY (IRTAC SCHEDULER_OPERATION_IMPLIES_VALID_CHANNEL_ID_LEMMA THEN STAC)) THEN
ETAC INVARIANT_CONCRETE_L3 THEN
CONJS_TAC THENL
[
 ITAC SCHEDULER_OPERATION_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
 ETAC invariant_l3Theory.INVARIANT_BDS_TO_FETCH_DISJOINT THEN
 INTRO_TAC THEN
 AITAC THEN
 PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (Q.SPEC ‘memory’ thm)) THEN
 ETAC stateTheory.BDS_TO_FETCH_EQ THEN
 AIRTAC THEN
 STAC
 ,
 ITAC SCHEDULER_OPERATION_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA THEN STAC
 ,
(* ITAC SCHEDULER_OPERATION_PRESERVES_NOT_DMA_BDS_LEMMA THEN STAC ,*)
(* ITAC SCHEDULER_OPERATION_PRESERVES_NOT_DMA_SCRATCHPAD_LEMMA THEN STAC ,*)
 ITAC SCHEDULER_OPERATION_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA THEN STAC
 ,
 ITAC SCHEDULER_OPERATION_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA THEN STAC
 ,
 ITAC SCHEDULER_OPERATION_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA THEN STAC
 ,
 ITAC SCHEDULER_OPERATION_PRESERVES_DEFINED_CHANNELS_LEMMA THEN STAC
]
QED

Theorem DMA_OPERATION_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA:
!device_characteristics memory environment device1 device2 channel_id operation.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics ∧
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  PROOF_OBLIGATION_FETCHING_BD_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCH_BD_PRESERVES_OTHER_FETCH_BD_ADDRESSES device_characteristics /\
  PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS device_characteristics /\
  PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ device_characteristics /\
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  PROOF_OBLIGATION_UPDATE_WRITES_DECLARED device_characteristics /\
  PROOF_OBLIGATION_UPDATING_BD_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_UPDATE_BD_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_WRITES_DECLARED device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_BD_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  DEFINED_CHANNELS device_characteristics device1 /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  device2 = dma_operation device_characteristics channel_operation_l3 (SOME memory) environment (device1, channel_id, operation) /\
  INVARIANT_CONCRETE_L3 device_characteristics memory device1
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_operation THEN
PTAC l3Theory.channel_operation_l3 THEN
EQ_PAIR_ASM_TAC THEN
NLRTAC 2 THEN
PTAC l3Theory.channel_operation_case_l3 THENL
[
 IRTAC fetching_bd_l3_preserves_invariant_concrete_l3_lemmasTheory.FETCHING_BD_L3_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA THEN STAC
 ,
 IRTAC updating_bd_l3_preserves_invariant_concrete_l3_lemmasTheory.UPDATING_BD_L3_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA THEN STAC
 ,
 IRTAC transferring_data_l3_preserves_invariant_concrete_l3_lemmasTheory.TRANSFERRING_DATA_L3_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA THEN STAC
 ,
 IRTAC writing_back_bd_l3_preserves_invariant_concrete_l3_lemmasTheory.WRITING_BACK_BD_L3_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA THEN STAC
]
QED

Theorem INTERNAL_DMA_OPERATION_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA:
!device_characteristics memory environment device1 device2.
  PROOF_OBLIGATION_SCHEDULER device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics ∧
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  PROOF_OBLIGATION_FETCHING_BD_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCH_BD_PRESERVES_OTHER_FETCH_BD_ADDRESSES device_characteristics /\
  PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS device_characteristics /\
  PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ device_characteristics /\
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  PROOF_OBLIGATION_UPDATE_WRITES_DECLARED device_characteristics /\
  PROOF_OBLIGATION_UPDATING_BD_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_UPDATE_BD_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_WRITES_DECLARED device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_BD_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  DEFINED_CHANNELS device_characteristics device1 /\
  device2 = internal_dma_operation device_characteristics channel_operation_l3 (SOME memory) environment device1 /\
  INVARIANT_CONCRETE_L3 device_characteristics memory device1
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC internal_operation_lemmasTheory.SCHEDULER_DMA_OPERATION_EQ_INTERNAL_DMA_OPERATION_LEMMA THEN
PTAC operationsTheory.scheduler_dma_operation THEN
RLTAC THEN
ITAC SCHEDULER_OPERATION_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA THEN
IRTAC DMA_OPERATION_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA THEN
STAC
QED

(*******************************************************************************)

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA:
!device_characteristics memory device1 device2.
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLY_PRESERVES_BDS_TO_FETCH device_characteristics /\
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1 /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device1
  ==>
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device2
Proof
INTRO_TAC THEN
ITAC invariant_l3_lemmasTheory.PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_CHANNELS_LEMMA THEN
ETAC NO_MEMORY_WRITES_TO_BDS THEN
RW_HYPS_TAC operationsTheory.channel_requests THEN
REWRITE_TAC [operationsTheory.channel_requests] THEN
LRTAC THEN
INTRO_TAC THEN
AIRTAC THEN
ETAC bd_queuesTheory.CONSISTENT_DMA_WRITE THEN
INTRO_TAC THEN
AIRTAC THEN
 ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
 INTRO_TAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLY_PRESERVES_BDS_TO_FETCH THEN
 PTAC operationsTheory.process_register_related_memory_access THEN
 AIRTAC THEN
 AITAC THEN
 LRTAC THEN
 RECORD_TAC THEN
 RLTAC THEN
 AIRTAC THEN
 STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_NOT_DMA_BDS_LEMMA:
!device_characteristics device1 device2 memory.
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLY_PRESERVES_BDS_TO_FETCH device_characteristics /\
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1 /\
  NOT_DMA_BDS device_characteristics memory device1
  ==>
  NOT_DMA_BDS device_characteristics memory device2
Proof
INTRO_TAC THEN
REWRITE_TAC [NOT_DMA_BDS] THEN
INTRO_TAC THEN
ITAC invariant_l3_lemmasTheory.PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_CHANNEL_BDS_LEMMA THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC “channel_id_bd : 'b channel_id_type” thm)) THEN
AITAC THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC “memory : 'e memory_type” thm)) THEN
LRTAC THEN
ITAC invariant_l3_lemmasTheory.PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_CHANNEL_BDS_LEMMA THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC “channel_id_dma_bd : 'b channel_id_type” thm)) THEN
AITAC THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC “memory : 'e memory_type” thm)) THEN
LRTAC THEN
IRTAC internal_operation_lemmasTheory.PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_BD_TRANSFER_RAS_WAS_LEMMA THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC “channel_id_dma_bd : 'b channel_id_type” thm)) THEN
AITAC THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC “dma_bd : 'a” thm)) THEN
LRTAC THEN
ETAC NOT_DMA_BDS THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC_ALL thm)) THEN
PAT_X_ASSUM “P ==> Q” (fn thm => MATCH_MP_TAC thm) THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA:
!device_characteristics device1 device2 memory.
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_REPLIES_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1 /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device1
  ==>
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_EXTERNAL_FETCH_BD_REPLY THEN
RW_HYPS_TAC stateTheory.schannel THEN
REWRITE_TAC [stateTheory.schannel] THEN
ITAC invariant_l3_lemmasTheory.PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_CHANNELS_LEMMA THEN
LRTAC THEN
IRTAC internal_operation_lemmasTheory.PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_FETCH_BD_ADDRESSES_LEMMA THEN
INTRO_TAC THEN
AITAC THEN
AIRTAC THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA:
!device_characteristics device1 device2 memory.
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_REPLIES_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1 /\
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device1
  ==>
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES THEN
RW_HYPS_TAC stateTheory.schannel THEN
REWRITE_TAC [stateTheory.schannel] THEN
ITAC invariant_l3_lemmasTheory.PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_CHANNELS_LEMMA THEN
LRTAC THEN
IRTAC internal_operation_lemmasTheory.PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_FETCH_BD_ADDRESSES_LEMMA THEN
INTRO_TAC THEN
AITAC THEN
AIRTAC THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA:
!device_characteristics memory device1 device2.
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLY_PRESERVES_BDS_TO_FETCH device_characteristics /\ (*
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_SCRATCHPAD device_characteristics /\*)
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_REPLIES_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1 /\
  INVARIANT_CONCRETE_L3 device_characteristics memory device1
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_CONCRETE_L3 THEN
CONJS_TAC THENL
[
 ETAC invariant_l3Theory.INVARIANT_BDS_TO_FETCH_DISJOINT THEN
 INTRO_TAC THEN
 AITAC THEN
 IRTAC process_register_related_memory_access_lemmasTheory.PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_CONCRETE_BDS_TO_FETCH_LEMMA THEN
 PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (Q.SPEC ‘memory’ thm)) THEN
 ETAC stateTheory.CONCRETE_BDS_TO_FETCH_EQ THEN
 AIRTAC THEN
 STAC
 ,
 IRTAC PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA THEN STAC
 ,
 IRTAC internal_operation_lemmasTheory.PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA THEN ETAC MEMORY_WRITES_PRESERVES_BDS_TO_FETCH THEN STAC
 ,
 IRTAC PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA THEN STAC
 ,
 IRTAC PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA THEN STAC
]
QED

(*******************************************************************************)

Theorem INTERNAL_FUNCTION_OPERATION_PRESERVES_DMA_STATE_LEMMA:
!device_characteristics environment device1 device2.
  device2 = internal_function_operation (THE device_characteristics.function_characteristics) environment device1
  ==>
  device2.dma_state = device1.dma_state
Proof
INTRO_TAC THEN
PTAC operationsTheory.internal_function_operation THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem INTERNAL_FUNCTION_OPERATION_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA:
!device_characteristics memory environment device1 device2.
  device2 = internal_function_operation (THE device_characteristics.function_characteristics) environment device1 /\
  INVARIANT_CONCRETE_L3 device_characteristics memory device1
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory device2
Proof
INTRO_TAC THEN
IRTAC INTERNAL_FUNCTION_OPERATION_PRESERVES_DMA_STATE_LEMMA THEN
ETAC INVARIANT_CONCRETE_L3 THEN
CONJS_TAC THENL
[
 ETAC invariant_l3Theory.INVARIANT_BDS_TO_FETCH_DISJOINT THEN STAC
 ,
 ETAC NO_MEMORY_WRITES_TO_BDS THEN RW_HYPS_TAC operationsTheory.channel_requests THEN REWRITE_TAC [operationsTheory.channel_requests] THEN STAC
 ,
 ETAC MEMORY_WRITES_PRESERVES_BDS_TO_FETCH THEN STAC
 ,
 ETAC INVARIANT_EXTERNAL_FETCH_BD_REPLY THEN RW_HYPS_TAC stateTheory.schannel THEN REWRITE_TAC [stateTheory.schannel] THEN STAC
 ,
 ETAC FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES THEN RW_HYPS_TAC stateTheory.schannel THEN REWRITE_TAC [stateTheory.schannel] THEN STAC
]
QED

(*******************************************************************************)

Theorem INTERNAL_DEVICE_OPERATION_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA:
!device_characteristics memory environment device1 device2.
  PROOF_OBLIGATION_SCHEDULER device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLY_PRESERVES_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_REPLIES_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  PROOF_OBLIGATION_FETCHING_BD_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCH_BD_PRESERVES_OTHER_FETCH_BD_ADDRESSES device_characteristics /\
  PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS device_characteristics /\
  PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ device_characteristics /\
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  PROOF_OBLIGATION_UPDATE_WRITES_DECLARED device_characteristics /\
  PROOF_OBLIGATION_UPDATING_BD_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_UPDATE_BD_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_WRITES_DECLARED device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_BD_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  device2 = internal_device_operation_l3 device_characteristics memory environment device1 /\
  INVARIANT_CONCRETE_L3 device_characteristics memory device1 /\
  DEFINED_CHANNELS device_characteristics device1
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC internal_device_operation_l3 THEN
PTAC operationsTheory.internal_device_operation THENL
[
 STAC
 ,
 IRTAC INTERNAL_DMA_OPERATION_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA THEN STAC
 ,
 IRTAC PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA THEN STAC
 ,
 IRTAC INTERNAL_FUNCTION_OPERATION_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA THEN STAC
]
QED

val _ = export_theory();

