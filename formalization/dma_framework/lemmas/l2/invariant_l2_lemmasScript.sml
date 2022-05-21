open HolKernel Parse boolLib bossLib helper_tactics;
open invariant_l2Theory operationsTheory;

val _ = new_theory "invariant_l2_lemmas";

Theorem INVARIANT_L2_IMPLIES_UPDATE_BD_LEMMA:
!device_characteristics memory device.
  INVARIANT_L2 device_characteristics memory device
  ==>
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device
Proof
INTRO_TAC THEN
PTAC INVARIANT_L2 THEN
STAC
QED

Theorem INVARIANT_L2_IMPLIES_INVARIANT_TRANSFER_DATA_L2_LEMMA:
!device_characteristics memory device.
  INVARIANT_L2 device_characteristics memory device
  ==>
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device
Proof
INTRO_TAC THEN
PTAC INVARIANT_L2 THEN
STAC
QED

Theorem INVARIANT_L2_IMPLIES_WRITE_BACK_BD_LEMMA:
!device_characteristics memory device.
  INVARIANT_L2 device_characteristics memory device
  ==>
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device
Proof
INTRO_TAC THEN
PTAC INVARIANT_L2 THEN
STAC
QED

Theorem INVARIANT_L2_IMPLIES_DEFINED_CHANNELS_LEMMA:
!device_characteristics memory device.
  INVARIANT_L2 device_characteristics memory device
  ==>
  DEFINED_CHANNELS device_characteristics device
Proof
INTRO_TAC THEN
PTAC INVARIANT_L2 THEN
STAC
QED








Definition FETCH_BD_TRANSITION:
FETCH_BD_TRANSITION operation_fetch_bd internal_state1 internal_state2 =
  ?reply fetched_bd. (internal_state2, fetched_bd) = operation_fetch_bd internal_state1 reply
End

Definition UPDATE_BD_TRANSITION:
UPDATE_BD_TRANSITION operation_update_bd internal_state1 internal_state2 =
  ?bytes tag update_status bd_ras_was. (internal_state2, bytes, tag, update_status) = operation_update_bd internal_state1 bd_ras_was
End

Definition BDS_TO_FETCH_UNEXPANDED:
BDS_TO_FETCH_UNEXPANDED channel1 channel2 =
!bd_entry.
  MEM bd_entry channel2.queue.bds_to_fetch
  ==>
  MEM bd_entry channel1.queue.bds_to_fetch
End

Definition BDS_TO_UPDATE_UNEXPANDED:
BDS_TO_UPDATE_UNEXPANDED channel1 channel2 =
!bd_entry.
  MEM bd_entry channel2.queue.bds_to_update
  ==>
  MEM bd_entry channel1.queue.bds_to_update
End

Definition BDS_TO_PROCESS_UNEXPANDED:
BDS_TO_PROCESS_UNEXPANDED channel1 channel2 =
!bd_entry.
  MEM bd_entry channel2.queue.bds_to_process
  ==>
  MEM bd_entry channel1.queue.bds_to_process
End

Definition BDS_TO_WRITE_BACK_UNEXPANDED:
BDS_TO_WRITE_BACK_UNEXPANDED channel1 channel2 =
!bd_entry.
  MEM bd_entry channel2.queue.bds_to_write_back
  ==>
  MEM bd_entry channel1.queue.bds_to_write_back
End

Definition BD_QUEUES_UNEXPANDED:
BD_QUEUES_UNEXPANDED channel1 channel2 = (
  BDS_TO_FETCH_UNEXPANDED channel1 channel2 /\
  BDS_TO_UPDATE_UNEXPANDED channel1 channel2 /\
  BDS_TO_PROCESS_UNEXPANDED channel1 channel2 /\
  BDS_TO_WRITE_BACK_UNEXPANDED channel1 channel2
)
End

Definition CHANNELS_BD_QUEUES_UNEXPANDED:
CHANNELS_BD_QUEUES_UNEXPANDED
  (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
  (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
  (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) =
!channel_id channel1 channel2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channel1 = THE (device1.dma_state.channels channel_id) /\
  channel2 = THE (device2.dma_state.channels channel_id)
  ==>
  BD_QUEUES_UNEXPANDED channel1 channel2
End

Definition PROCESS_REPLIES_GENERATE_REQUESTS_TRANSITION:
PROCESS_REPLIES_GENERATE_REQUESTS_TRANSITION process_replies_generate_requests internal_state1 internal_state2 = (
  internal_state1 = internal_state2 \/
  ?new_requests complete bd replies.
    (internal_state2, new_requests, complete) = process_replies_generate_requests internal_state1 bd replies
)
End

Definition INTERNAL_PROCESS_REPLIES_GENERATE_REQUESTS_TRANSITION:
INTERNAL_PROCESS_REPLIES_GENERATE_REQUESTS_TRANSITION device_characteristics device1 device2 =
!channel_id internal_state1 internal_state2 process_replies_generate_requests.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  internal_state2 = device2.dma_state.internal_state /\
  process_replies_generate_requests = (coperation device_characteristics channel_id).process_replies_generate_requests
  ==>
  PROCESS_REPLIES_GENERATE_REQUESTS_TRANSITION process_replies_generate_requests internal_state1 internal_state2
End

(* Predicate implying preservation of the Layer 2 invariant predicates of BD
 * queues.
 *)
Definition CHANNELS_BD_QUEUES_UNEXPANDED_PROCESSED_REPLIES_GENERATED_REQUESTS:
CHANNELS_BD_QUEUES_UNEXPANDED_PROCESSED_REPLIES_GENERATED_REQUESTS device_characteristics device1 device2 = (
  CHANNELS_BD_QUEUES_UNEXPANDED device_characteristics device1 device2 /\
  INTERNAL_PROCESS_REPLIES_GENERATE_REQUESTS_TRANSITION device_characteristics device1 device2
)
End

Definition WRITE_BACK_BD_TRANSITION:
WRITE_BACK_BD_TRANSITION operation_write_back_bd internal_state1 internal_state2 =
  ?write_address_bytes tag released_bds environment bds_to_write_back.
    (internal_state2, write_address_bytes, tag, released_bds) = operation_write_back_bd environment internal_state1 bds_to_write_back
End

Definition REGISTER_READ_TRANSITION:
REGISTER_READ_TRANSITION register_read internal_state1 internal_state2 =
  ?read_bytes requests register_read_addresses.
    (internal_state2, read_bytes, requests) = register_read internal_state1 register_read_addresses
End

Definition REGISTER_WRITE_TRANSITION:
REGISTER_WRITE_TRANSITION register_write internal_state1 internal_state2 register_write_address_bytes =
  ?requests.
    (internal_state2, requests) = register_write internal_state1 register_write_address_bytes
End

Definition INTERNAL_TRANSITIONS:
INTERNAL_TRANSITIONS device_characteristics channel_id internal_state1 internal_state2 =
  !operation_fetch_bd operation_update_bd process_replies_generate_requests operation_write_back_bd.
    VALID_CHANNEL_ID device_characteristics channel_id /\
    operation_fetch_bd = (coperation device_characteristics channel_id).fetch_bd /\
    operation_update_bd = (coperation device_characteristics channel_id).update_bd /\
    process_replies_generate_requests = (coperation device_characteristics channel_id).process_replies_generate_requests /\
    operation_write_back_bd = (coperation device_characteristics channel_id).write_back_bd
    ==>
    internal_state2 = internal_state1 \/
    FETCH_BD_TRANSITION operation_fetch_bd internal_state1 internal_state2 \/
    UPDATE_BD_TRANSITION operation_update_bd internal_state1 internal_state2 \/
    PROCESS_REPLIES_GENERATE_REQUESTS_TRANSITION process_replies_generate_requests internal_state1 internal_state2 \/
    WRITE_BACK_BD_TRANSITION operation_write_back_bd internal_state1 internal_state2
End







Theorem PROCESS_REPLIES_GENERATE_REQUESTS_TRANSITION_PRESERVES_SCRATCHPAD_LEMMA:
!device_characteristics channel_id process_replies_generate_requests internal_state1 internal_state2.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_SCRATCHPAD device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  process_replies_generate_requests = (coperation device_characteristics channel_id).process_replies_generate_requests /\
  PROCESS_REPLIES_GENERATE_REQUESTS_TRANSITION process_replies_generate_requests internal_state1 internal_state2
  ==>
  device_characteristics.dma_characteristics.scratchpad_addresses internal_state2 =
  device_characteristics.dma_characteristics.scratchpad_addresses internal_state1
Proof
INTRO_TAC THEN
PTAC PROCESS_REPLIES_GENERATE_REQUESTS_TRANSITION THEN
SPLIT_ASM_DISJS_TAC THENL
[
 STAC
 ,
 AXTAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_SCRATCHPAD THEN 
 AITAC THEN
 STAC
]
QED





Theorem BD_TO_PROCESS_RAS_R_W_LEMMA:
!device_characteristics memory device1 environment internal_state_pre_scheduling
 internal_state1 channel1 function_state scheduler pipelines
 pending_register_memory_accesses channel_id dma_channel_operation bd bd_ras
 bd_was bd_ras_wass ras_was.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION device_characteristics /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device1 /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (bd, bd_ras, bd_was)::bd_ras_wass = channel1.queue.bds_to_process /\
  ras_was = (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state1 bd
  ==>
  BD_DATA (device_characteristics.dma_characteristics.R memory) (device_characteristics.dma_characteristics.W memory) ras_was
Proof
INTRO_TAC THEN
PTAC INVARIANT_TRANSFER_DATA_L2 THEN
ITAC internal_operation_lemmasTheory.INTERNAL_DMA_OPERATION_IMPLIES_CHANNEL_STATE_LEMMA THEN
LRTAC THEN
IRTAC lists_lemmasTheory.MEM_HD_LEMMA THEN
ITAC internal_operation_lemmasTheory.INTERNAL_DMA_OPERATION_SCHEDULER_PRESERVES_BD_INTERPRETATION_LEMMA THEN
AITAC THEN
AIRTAC THEN
ALL_RLTAC THEN
STAC
QED

Theorem INVARIANT_L2_PROCESS_REPLIES_GENERATE_REQUESTS_R_LEMMA:
!device_characteristics memory device1 environment internal_state_pre_scheduling
 internal_state1 internal_state2 channel1 function_state scheduler pipelines
 pending_register_memory_accesses channel_id dma_channel_operation bd bd_ras
 bd_was bd_ras_wass new_requests complete replies.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  INVARIANT_L2 device_characteristics memory device1 /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation /\
  (bd, bd_ras, bd_was)::bd_ras_wass = channel1.queue.bds_to_process /\
  (internal_state2, new_requests, complete) = (coperation device_characteristics channel_id).process_replies_generate_requests internal_state1 bd replies
  ==>
  !read_addresses tag.
    MEM (request_read read_addresses tag) new_requests
    ==>
    EVERY (device_characteristics.dma_characteristics.R memory) read_addresses
Proof
INTRO_TAC THEN
INTRO_TAC THEN
ITAC proof_obligations_dma_l2_lemmasTheory.PROOF_OBLIGATIONS_DMA_L2_IMPLIES_READ_REQUESTS_CONSISTENT_WITH_BD_LEMMA THEN
ITAC proof_obligations_dma_l2_lemmasTheory.PROOF_OBLIGATIONS_DMA_L2_IMPLIES_SCHEDULER_PRESERVES_BD_INTERPRETATION_LEMMA THEN
ITAC proof_obligations_dma_l2_lemmasTheory.PROOF_OBLIGATIONS_DMA_L2_INTERNAL_DMA_OPERATION_IMPLIES_VALID_CHANNEL_ID_LEMMA THEN
ITAC internal_operation_lemmasTheory.PROCESS_REPLIES_GENERATE_REQUESTS_IMPLIES_READ_ADDRESSES_IN_RAS_LEMMA THEN
AXTAC THEN
AIRTAC THEN
ITAC INVARIANT_L2_IMPLIES_INVARIANT_TRANSFER_DATA_L2_LEMMA THEN
ITAC BD_TO_PROCESS_RAS_R_W_LEMMA THEN
PTAC stateTheory.BD_DATA THEN
IRTAC lists_lemmasTheory.EVERY_SUBLIST_LEMMA THEN
STAC
QED

Theorem INVARIANT_L2_PROCESS_REPLIES_GENERATE_REQUESTS_W_LEMMA:
!device_characteristics memory device1 environment internal_state_pre_scheduling
 internal_state1 internal_state2 channel1 function_state scheduler channel_id
 dma_channel_operation bd bd_ras bd_was bd_ras_wass new_requests complete replies
 pipelines pending_register_memory_accesses.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  INVARIANT_L2 device_characteristics memory device1 /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation /\
  (bd, bd_ras, bd_was)::bd_ras_wass = channel1.queue.bds_to_process /\
  (internal_state2, new_requests, complete) =
  (coperation device_characteristics channel_id).process_replies_generate_requests internal_state1 bd replies
  ==>
  !write_address_bytes tag.
    MEM (request_write write_address_bytes tag) new_requests
    ==>
    EVERY (device_characteristics.dma_characteristics.W memory) (MAP FST write_address_bytes)
Proof
INTRO_TAC THEN
INTRO_TAC THEN
ITAC proof_obligations_dma_l2_lemmasTheory.PROOF_OBLIGATIONS_DMA_L2_IMPLIES_WRITE_REQUESTS_CONSISTENT_WITH_BD_LEMMA THEN
ITAC proof_obligations_dma_l2_lemmasTheory.PROOF_OBLIGATIONS_DMA_L2_IMPLIES_SCHEDULER_PRESERVES_BD_INTERPRETATION_LEMMA THEN
ITAC proof_obligations_dma_l2_lemmasTheory.PROOF_OBLIGATIONS_DMA_L2_INTERNAL_DMA_OPERATION_IMPLIES_VALID_CHANNEL_ID_LEMMA THEN
ITAC internal_operation_lemmasTheory.PROCESS_REPLIES_GENERATE_REQUESTS_IMPLIES_WRITE_ADDRESSES_IN_WAS_LEMMA THEN
AXTAC THEN
AIRTAC THEN
IRTAC INVARIANT_L2_IMPLIES_INVARIANT_TRANSFER_DATA_L2_LEMMA THEN
IRTAC BD_TO_PROCESS_RAS_R_W_LEMMA THEN
PTAC stateTheory.BD_DATA THEN
FIRTAC lists_lemmasTheory.EVERY_SUBLIST_LEMMA THEN
STAC
QED

Theorem INVARIANT_L2_NEW_REQUESTS_R_LEMMA:
!device_characteristics environment device1 internal_state_pre_scheduling
 internal_state1 internal_state2 channel1 channel2 function_state scheduler
 channel_id pipelines pending_register_memory_accesses dma_channel_operation new_requests
 complete memory bd bd_ras bd_was bd_ras_wass.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  INVARIANT_L2 device_characteristics memory device1 /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation /\
  ((bd, bd_ras, bd_was)::bd_ras_wass = channel1.queue.bds_to_process) /\
  ((internal_state2, channel2, new_requests, complete) = transferring_data_replies_requests channel1.pending_accesses.replies.transferring_data (coperation device_characteristics channel_id).process_replies_generate_requests internal_state1 channel1 bd)
  ==>
  !read_addresses tag.
    MEM (request_read read_addresses tag) new_requests
    ==>
    EVERY (device_characteristics.dma_characteristics.R memory) read_addresses
Proof
INTRO_TAC THEN
PTAC transferring_data_replies_requests THEN
EQ_PAIR_ASM_TAC THEN
RLTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN
ITAC INVARIANT_L2_PROCESS_REPLIES_GENERATE_REQUESTS_R_LEMMA THEN
STAC
QED

Theorem INVARIANT_L2_NEW_REQUESTS_W_LEMMA:
!device_characteristics environment device1 internal_state_pre_scheduling
 internal_state1 internal_state2 channel1 channel2 function_state scheduler
 channel_id dma_channel_operation new_requests complete memory bd
 bd_ras bd_was bd_ras_wass pipelines pending_register_memory_accesses.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  INVARIANT_L2 device_characteristics memory device1 /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation /\
  ((bd, bd_ras, bd_was)::bd_ras_wass = channel1.queue.bds_to_process) /\
  ((internal_state2, channel2, new_requests, complete) = transferring_data_replies_requests channel1.pending_accesses.replies.transferring_data (coperation device_characteristics channel_id).process_replies_generate_requests internal_state1 channel1 bd)
  ==>
  !write_address_bytes tag.
    MEM (request_write write_address_bytes tag) new_requests
    ==>
    EVERY (device_characteristics.dma_characteristics.W memory) (MAP FST write_address_bytes)
Proof
INTRO_TAC THEN
PTAC transferring_data_replies_requests THEN
EQ_PAIR_ASM_TAC THEN
RLTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN
ITAC INVARIANT_L2_PROCESS_REPLIES_GENERATE_REQUESTS_W_LEMMA THEN
STAC
QED

Theorem INVARIANT_L2_NEW_REQUESTS_R_W_LEMMA:
!device_characteristics device1 internal_state_pre_scheduling internal_state1
 internal_state2 channel1 channel2 channel_id memory bd bd_ras
 bd_was bd_ras_wass new_requests complete environment function_state
 scheduler dma_channel_operation pipelines pending_register_memory_accesses.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  INVARIANT_L2 device_characteristics memory device1 /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation /\
  ((bd, bd_ras, bd_was)::bd_ras_wass = channel1.queue.bds_to_process) /\
  ((internal_state2, channel2, new_requests, complete) = transferring_data_replies_requests channel1.pending_accesses.replies.transferring_data (coperation device_characteristics channel_id).process_replies_generate_requests internal_state1 channel1 bd)
  ==>
  READABLE_WRITABLE device_characteristics.dma_characteristics.R device_characteristics.dma_characteristics.W memory new_requests
Proof
INTRO_TAC THEN
ITAC INVARIANT_L2_NEW_REQUESTS_R_LEMMA THEN
IRTAC INVARIANT_L2_NEW_REQUESTS_W_LEMMA THEN
ASM_REWRITE_TAC [access_properties_lemmasTheory.READABLE_WRITABLE_EQ_REQUEST_MEMBERS_R_W_LEMMA]
QED



(******************************************************************************)
(******************************************************************************)
(******************************************************************************)
(******************************************************************************)
(******************************************************************************)
(******************************************************************************)
(******************************************************************************)
(******************************************************************************)

Definition BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ:
BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2 = (
!channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  (cverification device_characteristics channel_id).bd_transfer_ras_was device1.dma_state.internal_state =
  (cverification device_characteristics channel_id).bd_transfer_ras_was device2.dma_state.internal_state
)
End

Definition bd_ras_was_update_cycle2bd_ras_was:
bd_ras_was_update_cycle2bd_ras_was (bd_ras_was, update_flag) = bd_ras_was
End

Definition BD_Q_PRESERVED:
BD_Q_PRESERVED bds1 bds2 = (bds1 = bds2)
End

Definition BD_Q_REMOVAL:
(BD_Q_REMOVAL [] bds2 = F) /\
(BD_Q_REMOVAL (bd::bds1) bds2 = (bds2 = bds1))
End

Definition BD_Q_CYCLIC:
(BD_Q_CYCLIC [] bds2 = F) /\
(BD_Q_CYCLIC (bd1::bds1) bds2 = (bds2 = bds1 ++ [bd1]))
End

Definition BD_Q_CYCLIC_REMOVAL:
BD_Q_CYCLIC_REMOVAL bds_a1 bds_a2 = (
 BD_Q_REMOVAL bds_a1 bds_a2 \/
 BD_Q_CYCLIC bds_a1 bds_a2
)
End

Definition BD_Q_CYCLIC_REMOVAL_PRESERVED:
BD_Q_CYCLIC_REMOVAL_PRESERVED bds_a1 bds_a2 bds_b1 bds_b2 = (
  BD_Q_CYCLIC_REMOVAL bds_a1 bds_a2 /\
  BD_Q_PRESERVED bds_b1 bds_b2
)
End

Definition BD_Q_PRESERVED_OR_REMOVAL:
BD_Q_PRESERVED_OR_REMOVAL q1 q2 = (
  BD_Q_PRESERVED q1 q2 \/
  BD_Q_REMOVAL q1 q2
)
End

Definition BD_Q_PRESERVED_OR_REMOVAL_OR_CYCLIC:
BD_Q_PRESERVED_OR_REMOVAL_OR_CYCLIC q1 q2 = (
  BD_Q_PRESERVED q1 q2 \/
  BD_Q_REMOVAL q1 q2 \/
  BD_Q_CYCLIC q1 q2
)
End

Definition BD_Q_PRESERVED_PRESERVED:
BD_Q_PRESERVED_PRESERVED bds_a1 bds_a2 bds_b1 bds_b2 = (
  BD_Q_PRESERVED bds_a1 bds_a2 /\
  BD_Q_PRESERVED bds_b1 bds_b2
)
End

Definition BD_Q_TRANSITION:
(BD_Q_TRANSITION f []           bds_a2 bds_b1 bds_b2 = F) /\
(BD_Q_TRANSITION f (bd::bds_a1) bds_a2 bds_b1 bds_b2 = (
 (bds_a2 = bds_a1         /\ bds_b2 = bds_b1 ++ [f bd]) \/ (* Not cyclic. *)
 (bds_a2 = bds_a1 ++ [bd] /\ bds_b2 = bds_b1 ++ [f bd]))   (* Cyclic. *)
)
End

Definition BD_Q_TRANSITION_BD_RAS_WAS:
BD_Q_TRANSITION_BD_RAS_WAS qa1 qa2 qb1 qb2 = 
  BD_Q_TRANSITION I qa1 qa2 qb1 qb2
End

Definition BD_Q_TRANSITION_BD_RAS_WAS_UPDATE_CYCLE:
BD_Q_TRANSITION_BD_RAS_WAS_UPDATE_CYCLE qa1 qa2 qb1 qb2 = 
  BD_Q_TRANSITION bd_ras_was_update_cycle2bd_ras_was qa1 qa2 qb1 qb2
End

Definition BD_Q_TRANSITIONS_BD_RAS_WAS:
BD_Q_TRANSITIONS_BD_RAS_WAS qa1 qa2 qb1 qb2 = (
  BD_Q_TRANSITION_BD_RAS_WAS qa1 qa2 qb1 qb2 \/
  BD_Q_CYCLIC_REMOVAL_PRESERVED qa1 qa2 qb1 qb2 \/
  BD_Q_PRESERVED_PRESERVED qa1 qa2 qb1 qb2
)
End

Definition BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE:
BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE qa1 qa2 qb1 qb2 = (
  BD_Q_TRANSITION_BD_RAS_WAS_UPDATE_CYCLE qa1 qa2 qb1 qb2 \/
  BD_Q_CYCLIC_REMOVAL_PRESERVED qa1 qa2 qb1 qb2 \/
  BD_Q_PRESERVED_PRESERVED qa1 qa2 qb1 qb2
)
End



Theorem BD_Q_PRESERVED_IMPLIES_POST_MEMBER_PRE_LEMMA:
!q1 q2 bd.
  BD_Q_PRESERVED q1 q2 /\
  MEM bd q2
  ==>
  MEM bd q1
Proof
INTRO_TAC THEN
PTAC BD_Q_PRESERVED THEN
STAC
QED

Theorem BD_Q_TRANSITION_BD_RAS_WAS_IMPLIES_PRE_MEMBER_LEMMA:
!qa1 qa2 qb1 qb2 bd.
  BD_Q_TRANSITION_BD_RAS_WAS qa1 qa2 qb1 qb2 /\
  MEM bd qa2
  ==>
  MEM bd qa1
Proof
INTRO_TAC THEN
PTAC BD_Q_TRANSITION_BD_RAS_WAS THEN
PTAC BD_Q_TRANSITION THENL
[
 SOLVE_F_ASM_TAC
 ,
 SPLIT_ASM_DISJS_TAC THENL
 [
  ALL_LRTAC THEN
  ETAC listTheory.MEM THEN
  STAC
  ,
  ALL_LRTAC THEN
  ETAC listTheory.MEM_APPEND THEN
  ETAC listTheory.MEM THEN
  REMOVE_F_DISJUNCTS_TAC THEN
  SPLIT_ASM_DISJS_TAC THEN STAC
 ]
]
QED

Theorem BD_Q_CYCLIC_REMOVAL_PRESERVED_IMPLIES_PRE_MEMBER_LEMMA:
!qa1 qa2 qb1 qb2 bd.
  BD_Q_CYCLIC_REMOVAL_PRESERVED qa1 qa2 qb1 qb2 /\
  MEM bd qa2
  ==>
  MEM bd qa1
Proof
INTRO_TAC THEN
PTAC BD_Q_CYCLIC_REMOVAL_PRESERVED THEN
PTAC BD_Q_CYCLIC_REMOVAL THEN
SPLIT_ASM_DISJS_TAC THENL
[
 PTAC BD_Q_REMOVAL THENL
 [
  SOLVE_F_ASM_TAC
  ,
  ALL_LRTAC THEN
  ETAC listTheory.MEM THEN
  STAC
 ]
 ,
 PTAC BD_Q_CYCLIC THENL
 [
  SOLVE_F_ASM_TAC
  ,
  ALL_LRTAC THEN
  ETAC listTheory.MEM_APPEND THEN
  ETAC listTheory.MEM THEN
  REMOVE_F_DISJUNCTS_TAC THEN
  SPLIT_ASM_DISJS_TAC THEN STAC
 ]
]
QED

Theorem BD_Q_PRESERVED_OR_REMOVAL_IMPLIES_PRE_MEMBER_LEMMA:
!q1 q2 bd.
  BD_Q_PRESERVED_OR_REMOVAL q1 q2 /\
  MEM bd q2
  ==>
  MEM bd q1
Proof
INTRO_TAC THEN
PTAC BD_Q_PRESERVED_OR_REMOVAL THEN
SPLIT_ASM_DISJS_TAC THENL
[
 PTAC BD_Q_PRESERVED THEN
 STAC
 ,
 PTAC BD_Q_REMOVAL THENL
 [
  SOLVE_F_ASM_TAC
  ,
  ALL_LRTAC THEN
  ETAC listTheory.MEM THEN
  STAC
 ]
]
QED

Theorem BD_Q_PRESERVED_OR_REMOVAL_OR_CYCLIC_IMPLIES_PRE_MEMBER_LEMMA:
!q1 q2 bd.
  BD_Q_PRESERVED_OR_REMOVAL_OR_CYCLIC q1 q2 /\
  MEM bd q2
  ==>
  MEM bd q1
Proof
INTRO_TAC THEN
PTAC BD_Q_PRESERVED_OR_REMOVAL_OR_CYCLIC THEN
SPLIT_ASM_DISJS_TAC THENL
[
 PTAC BD_Q_PRESERVED THEN
 STAC
 ,
 PTAC BD_Q_REMOVAL THENL
 [
  SOLVE_F_ASM_TAC
  ,
  ALL_LRTAC THEN
  ASM_REWRITE_TAC [listTheory.MEM]
 ]
 ,
 PTAC BD_Q_CYCLIC THENL
 [
  SOLVE_F_ASM_TAC
  ,
  ALL_LRTAC THEN
  ETAC listTheory.MEM_APPEND THEN
  ETAC listTheory.MEM THEN
  REMOVE_F_DISJUNCTS_TAC THEN
  SPLIT_ASM_DISJS_TAC THEN STAC
 ]
]
QED

Theorem BD_Q_PRESERVED_PRESERVED_IMPLIES_PRE_MEMBER_LEMMA:
!qa1 qa2 qb1 qb2 bd.
  BD_Q_PRESERVED_PRESERVED qa1 qa2 qb1 qb2 /\
  MEM bd qa2
  ==>
  MEM bd qa1
Proof
INTRO_TAC THEN
PTAC BD_Q_PRESERVED_PRESERVED THEN
PTAC BD_Q_PRESERVED THEN
STAC
QED

Theorem BD_Q_TRANSITIONS_BD_RAS_WAS_IMPLIES_PRE_MEMBER_LEMMA:
!qa1 qa2 qb1 qb2 bd.
  BD_Q_TRANSITIONS_BD_RAS_WAS qa1 qa2 qb1 qb2 /\
  MEM bd qa2
  ==>
  MEM bd qa1
Proof
INTRO_TAC THEN
PTAC BD_Q_TRANSITIONS_BD_RAS_WAS THEN
SPLIT_ASM_DISJS_TAC THENL
[
 IRTAC BD_Q_TRANSITION_BD_RAS_WAS_IMPLIES_PRE_MEMBER_LEMMA THEN STAC
 ,
 IRTAC BD_Q_CYCLIC_REMOVAL_PRESERVED_IMPLIES_PRE_MEMBER_LEMMA THEN STAC
 ,
 IRTAC BD_Q_PRESERVED_PRESERVED_IMPLIES_PRE_MEMBER_LEMMA THEN STAC
]
QED



Theorem BD_Q_TRANSITION_BD_RAS_WAS_IMPLIES_POST_MEMBER_PRE_MEMBER_LEMMA:
!qa1 qa2 qb1 qb2 bd.
  BD_Q_TRANSITION_BD_RAS_WAS qa1 qa2 qb1 qb2 /\
  MEM bd qb2
  ==>
  MEM bd qb1 \/ MEM bd qa1
Proof
INTRO_TAC THEN
PTAC BD_Q_TRANSITION_BD_RAS_WAS THEN
PTAC BD_Q_TRANSITION THENL
[
 SOLVE_F_ASM_TAC
 ,
 SPLIT_ASM_DISJS_TAC THENL
 [
  ALL_LRTAC THEN
  ETAC listTheory.MEM_APPEND THEN
  ETAC listTheory.MEM THEN
  REMOVE_F_DISJUNCTS_TAC THEN
  ETAC combinTheory.I_THM THEN
  SPLIT_ASM_DISJS_TAC THEN STAC
  ,
  ALL_LRTAC THEN
  ETAC listTheory.MEM_APPEND THEN
  ETAC listTheory.MEM THEN
  REMOVE_F_DISJUNCTS_TAC THEN
  ETAC combinTheory.I_THM THEN
  SPLIT_ASM_DISJS_TAC THEN STAC
 ]
]
QED

Theorem BD_Q_CYCLIC_REMOVAL_PRESERVED_IMPLIES_POST_MEMBER_PRE_MEMBER_LEMMA:
!qa1 qa2 qb1 qb2 bd.
  BD_Q_CYCLIC_REMOVAL_PRESERVED qa1 qa2 qb1 qb2 /\
  MEM bd qb2
  ==>
  MEM bd qb1 \/ MEM bd qa1
Proof
INTRO_TAC THEN
PTAC BD_Q_CYCLIC_REMOVAL_PRESERVED THEN
PTAC BD_Q_PRESERVED THEN
STAC
QED

Theorem BD_Q_PRESERVED_PRESERVED_IMPLIES_POST_MEMBER_PRE_MEMBER_LEMMA:
!qa1 qa2 qb1 qb2 bd.
  BD_Q_PRESERVED_PRESERVED qa1 qa2 qb1 qb2 /\
  MEM bd qb2
  ==>
  MEM bd qb1 \/ MEM bd qa1
Proof
INTRO_TAC THEN
PTAC BD_Q_PRESERVED_PRESERVED THEN
ETAC BD_Q_PRESERVED THEN
STAC
QED

Theorem BD_Q_TRANSITIONS_BD_RAS_WAS_IMPLIES_POST_MEMBER_PRE_MEMBER_LEMMA:
!qa1 qa2 qb1 qb2 bd.
  BD_Q_TRANSITIONS_BD_RAS_WAS qa1 qa2 qb1 qb2 /\
  MEM bd qb2
  ==>
  MEM bd qb1 \/ MEM bd qa1
Proof
INTRO_TAC THEN
PTAC BD_Q_TRANSITIONS_BD_RAS_WAS THEN
SPLIT_ASM_DISJS_TAC THENL
[
 IRTAC BD_Q_TRANSITION_BD_RAS_WAS_IMPLIES_POST_MEMBER_PRE_MEMBER_LEMMA THEN STAC
 ,
 IRTAC BD_Q_CYCLIC_REMOVAL_PRESERVED_IMPLIES_POST_MEMBER_PRE_MEMBER_LEMMA THEN STAC
 ,
 IRTAC BD_Q_PRESERVED_PRESERVED_IMPLIES_POST_MEMBER_PRE_MEMBER_LEMMA THEN STAC
]
QED



Theorem BD_Q_TRANSITION_BD_RAS_WAS_UPDATE_CYCLE_IMPLIES_POST_MEMBER_PRE_MEMBER_LEMMA:
!qa1 qa2 qb1 qb2 bd_ras_was.
  BD_Q_TRANSITION_BD_RAS_WAS_UPDATE_CYCLE qa1 qa2 qb1 qb2 /\
  MEM bd_ras_was qb2
  ==>
  MEM bd_ras_was qb1 \/ (?update_flag. MEM (bd_ras_was, update_flag) qa1)
Proof
INTRO_TAC THEN
PTAC BD_Q_TRANSITION_BD_RAS_WAS_UPDATE_CYCLE THEN
PTAC BD_Q_TRANSITION THENL
[
 SOLVE_F_ASM_TAC
 ,
 SPLIT_ASM_DISJS_TAC THENL
 [
  ALL_LRTAC THEN
  ETAC listTheory.MEM_APPEND THEN
  SPLIT_ASM_DISJS_TAC THENL
  [
   STAC
   ,
   ETAC listTheory.MEM THEN
   REMOVE_F_DISJUNCTS_TAC THEN
   PTAC bd_ras_was_update_cycle2bd_ras_was THEN
   ALL_LRTAC THEN
   MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
   REWRITE_TAC [listTheory.MEM] THEN
   EXISTS_EQ_TAC
  ]
  ,
  ALL_LRTAC THEN
  ETAC listTheory.MEM_APPEND THEN
  SPLIT_ASM_DISJS_TAC THENL
  [
   STAC
   ,
   ETAC listTheory.MEM THEN
   REMOVE_F_DISJUNCTS_TAC THEN
   PTAC bd_ras_was_update_cycle2bd_ras_was THEN
   ALL_LRTAC THEN
   MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
   REWRITE_TAC [listTheory.MEM] THEN
   EXISTS_EQ_TAC
  ]
 ]
]
QED

Theorem BD_Q_CYCLIC_REMOVAL_PRESERVED_IMPLIES_POST_MEMBER_PRE_MEMBER_UPDATE_CYCLE_LEMMA:
!qa1 qa2 qb1 qb2 bd_ras_was.
  BD_Q_CYCLIC_REMOVAL_PRESERVED qa1 qa2 qb1 qb2 /\
  MEM bd_ras_was qb2
  ==>
  MEM bd_ras_was qb1 \/ (?update_flag. MEM (bd_ras_was, update_flag) qa1)
Proof
INTRO_TAC THEN
PTAC BD_Q_CYCLIC_REMOVAL_PRESERVED THEN
PTAC BD_Q_PRESERVED THEN
STAC
QED

Theorem BD_Q_PRESERVED_PRESERVED_IMPLIES_POST_MEMBER_PRE_MEMBER_UPDATE_CYCLE_LEMMA:
!qa1 qa2 qb1 qb2 bd_ras_was.
  BD_Q_PRESERVED_PRESERVED qa1 qa2 qb1 qb2 /\
  MEM bd_ras_was qb2
  ==>
  MEM bd_ras_was qb1 \/ (?update_flag. MEM (bd_ras_was, update_flag) qa1)
Proof
INTRO_TAC THEN
PTAC BD_Q_PRESERVED_PRESERVED THEN
ETAC BD_Q_PRESERVED THEN
STAC
QED

Theorem BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_IMPLIES_POST_MEMBER_PRE_MEMBER_LEMMA:
!qa1 qa2 qb1 qb2 bd_ras_was.
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE qa1 qa2 qb1 qb2 /\
  MEM bd_ras_was qb2
  ==>
  MEM bd_ras_was qb1 \/ (?update_flag. MEM (bd_ras_was, update_flag) qa1)
Proof
INTRO_TAC THEN
PTAC BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE THEN
SPLIT_ASM_DISJS_TAC THENL
[
 IRTAC BD_Q_TRANSITION_BD_RAS_WAS_UPDATE_CYCLE_IMPLIES_POST_MEMBER_PRE_MEMBER_LEMMA THEN STAC
 ,
 IRTAC BD_Q_CYCLIC_REMOVAL_PRESERVED_IMPLIES_POST_MEMBER_PRE_MEMBER_UPDATE_CYCLE_LEMMA THEN STAC
 ,
 IRTAC BD_Q_PRESERVED_PRESERVED_IMPLIES_POST_MEMBER_PRE_MEMBER_UPDATE_CYCLE_LEMMA THEN STAC
]
QED



Theorem BD_Q_TRANSITION_BD_RAS_WAS_UPDATE_CYCLE_IMPLIES_PRE_MEMBER_LEMMA:
!qa1 qa2 qb1 qb2 bd_ras_was.
  BD_Q_TRANSITION_BD_RAS_WAS_UPDATE_CYCLE qa1 qa2 qb1 qb2 /\
  MEM bd_ras_was qa2
  ==>
  MEM bd_ras_was qa1
Proof
INTRO_TAC THEN
PTAC BD_Q_TRANSITION_BD_RAS_WAS_UPDATE_CYCLE THEN
PTAC BD_Q_TRANSITION THENL
[
 SOLVE_F_ASM_TAC
 ,
 SPLIT_ASM_DISJS_TAC THENL
 [
  ALL_LRTAC THEN
  ETAC listTheory.MEM THEN
  STAC
  ,
  ALL_LRTAC THEN
  ETAC listTheory.MEM_APPEND THEN
  ETAC listTheory.MEM THEN
  REMOVE_F_DISJUNCTS_TAC THEN
  SPLIT_ASM_DISJS_TAC THEN STAC
 ]
]
QED

Theorem BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_IMPLIES_PRE_MEMBER_LEMMA:
!qa1 qa2 qb1 qb2 bd_ras_was.
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE qa1 qa2 qb1 qb2 /\
  MEM bd_ras_was qa2
  ==>
  MEM bd_ras_was qa1
Proof
INTRO_TAC THEN
PTAC BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE THEN
SPLIT_ASM_DISJS_TAC THENL
[
 IRTAC BD_Q_TRANSITION_BD_RAS_WAS_UPDATE_CYCLE_IMPLIES_PRE_MEMBER_LEMMA THEN STAC
 ,
 IRTAC BD_Q_CYCLIC_REMOVAL_PRESERVED_IMPLIES_PRE_MEMBER_LEMMA THEN STAC
 ,
 IRTAC BD_Q_PRESERVED_PRESERVED_IMPLIES_PRE_MEMBER_LEMMA THEN STAC
]
QED

Theorem BD_Q_PRESERVED_REFL_LEMMA:
!q.
  BD_Q_PRESERVED q q
Proof
REWRITE_TAC [BD_Q_PRESERVED]
QED

Theorem BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_SAME_QS_LEMMA:
!qa qb.
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE qa qa qb qb
Proof
REPEAT GEN_TAC THEN
PTAC BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
PTAC BD_Q_PRESERVED_PRESERVED THEN
ETAC BD_Q_PRESERVED THEN
STAC
QED

Theorem BD_QS_PRESERVED_PRESERVES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_LEMMA:
!qa1 qa2 qa3 qb1 qb2 qb3.
  BD_Q_PRESERVED qa1 qa2 /\
  BD_Q_PRESERVED qb1 qb2 /\
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE qa2 qa3 qb2 qb3
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE qa1 qa3 qb1 qb3
Proof
INTRO_TAC THEN
ETAC BD_Q_PRESERVED THEN
ASM_REWRITE_TAC [BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_SAME_QS_LEMMA]
QED

Theorem BD_Q_TRANSITIONS_BD_RAS_WAS_SAME_QS_LEMMA:
!q1 q2.
  BD_Q_TRANSITIONS_BD_RAS_WAS q1 q1 q2 q2
Proof
REPEAT GEN_TAC THEN
PTAC BD_Q_TRANSITIONS_BD_RAS_WAS THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
PTAC BD_Q_PRESERVED_PRESERVED THEN
REWRITE_TAC [BD_Q_PRESERVED]
QED

Theorem BD_PRESERVED_TRANSITIVITY_LEMMA:
!q1 q2 q3.
  BD_Q_PRESERVED q1 q2 /\
  BD_Q_PRESERVED q2 q3
  ==>
  BD_Q_PRESERVED q1 q3
Proof
INTRO_TAC THEN
ETAC BD_Q_PRESERVED THEN
STAC
QED

Theorem BD_Q_PRESERVED_BD_Q_TRANSITIONS_BD_RAS_WAS_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_LEMMA:
!q1a q1b qa qb q2a q2b.
  BD_Q_PRESERVED q1a qa /\
  BD_Q_PRESERVED q1b qb /\
  BD_Q_TRANSITIONS_BD_RAS_WAS qa q2a qb q2b
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS q1a q2a q1b q2b
Proof
INTRO_TAC THEN
ETAC BD_Q_PRESERVED THEN
ALL_RLTAC THEN
STAC
QED

Theorem UPDATE_DEVICE_PRESERVES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_UPDATE_BDS_TO_PROCESS_LEMMA:
!q1 q2 device1 device2 channel1 channel2 channel_id' channel_id internal_state.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  channel1 = schannel device1 channel_id /\
  device2 = update_device_state device1 channel_id internal_state channel2 /\
  BD_Q_TRANSITIONS_BD_RAS_WAS channel1.queue.bds_to_update  channel2.queue.bds_to_update
                              channel1.queue.bds_to_process channel2.queue.bds_to_process
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS q1.bds_to_update q2.bds_to_update q1.bds_to_process q2.bds_to_process
Proof
INTRO_TAC THEN
ETAC operationsTheory.update_device_state THEN
ETAC combinTheory.UPDATE_def THEN
ALL_LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 LRTAC THEN
 ASM_REWRITE_TAC [optionTheory.THE_DEF]
 ,
 PTAC BD_Q_TRANSITIONS_BD_RAS_WAS THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 REWRITE_TAC [BD_Q_PRESERVED_PRESERVED, BD_Q_PRESERVED]
]
QED

Theorem UPDATE_DEVICE_PRESERVES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_PROCESS_WRITE_BACK_LEMMA:
!q1 q2 device1 device2 channel1 channel2 channel_id' channel_id internal_state.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  channel1 = schannel device1 channel_id /\
  device2 = update_device_state device1 channel_id internal_state channel2 /\
  BD_Q_TRANSITIONS_BD_RAS_WAS channel1.queue.bds_to_process channel2.queue.bds_to_process
                              channel1.queue.bds_to_write_back  channel2.queue.bds_to_write_back
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS q1.bds_to_process q2.bds_to_process q1.bds_to_write_back q2.bds_to_write_back
Proof
INTRO_TAC THEN
ETAC operationsTheory.update_device_state THEN
ETAC combinTheory.UPDATE_def THEN
ALL_LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 LRTAC THEN
 ASM_REWRITE_TAC [optionTheory.THE_DEF]
 ,
 PTAC BD_Q_TRANSITIONS_BD_RAS_WAS THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 REWRITE_TAC [BD_Q_PRESERVED_PRESERVED, BD_Q_PRESERVED]
]
QED

Theorem UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA:
!q1 q2 device1 device2 channel1 channel2 channel_id' channel_id internal_state.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  channel1 = schannel device1 channel_id /\
  device2 = update_device_state device1 channel_id internal_state channel2 /\
  BD_Q_PRESERVED channel1.queue.bds_to_fetch channel2.queue.bds_to_fetch
  ==>
  BD_Q_PRESERVED q1.bds_to_fetch q2.bds_to_fetch
Proof
INTRO_TAC THEN
ETAC BD_Q_PRESERVED THEN
ETAC operationsTheory.update_device_state THEN
ALL_LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 ETAC optionTheory.THE_DEF THEN
 STAC
 ,
 STAC
]
QED

Theorem UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_UPDATE_LEMMA:
!q1 q2 device1 device2 channel1 channel2 channel_id' channel_id internal_state.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  channel1 = schannel device1 channel_id /\
  device2 = update_device_state device1 channel_id internal_state channel2 /\
  BD_Q_PRESERVED channel1.queue.bds_to_update channel2.queue.bds_to_update
  ==>
  BD_Q_PRESERVED q1.bds_to_update q2.bds_to_update
Proof
INTRO_TAC THEN
ETAC BD_Q_PRESERVED THEN
ETAC operationsTheory.update_device_state THEN
ALL_LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 ETAC optionTheory.THE_DEF THEN
 STAC
 ,
 STAC
]
QED

Theorem UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_PROCESS_LEMMA:
!q1 q2 device1 device2 channel1 channel2 channel_id' channel_id internal_state.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  channel1 = schannel device1 channel_id /\
  device2 = update_device_state device1 channel_id internal_state channel2 /\
  BD_Q_PRESERVED channel1.queue.bds_to_process channel2.queue.bds_to_process
  ==>
  BD_Q_PRESERVED q1.bds_to_process q2.bds_to_process
Proof
INTRO_TAC THEN
ETAC BD_Q_PRESERVED THEN
ETAC operationsTheory.update_device_state THEN
ALL_LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 ETAC optionTheory.THE_DEF THEN
 STAC
 ,
 STAC
]
QED

Theorem UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA:
!q1 q2 device1 device2 channel1 channel2 channel_id' channel_id internal_state.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  channel1 = schannel device1 channel_id /\
  device2 = update_device_state device1 channel_id internal_state channel2 /\
  BD_Q_PRESERVED channel1.queue.bds_to_write_back channel2.queue.bds_to_write_back
  ==>
  BD_Q_PRESERVED q1.bds_to_write_back q2.bds_to_write_back
Proof
INTRO_TAC THEN
ETAC BD_Q_PRESERVED THEN
ETAC operationsTheory.update_device_state THEN
ALL_LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 ETAC optionTheory.THE_DEF THEN
 STAC
 ,
 STAC
]
QED

Theorem ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_LEMMA:
!q1 q2 device1 device2 channel_id' channel_id channel internal_state.
  channel = (schannel device1 channel_id) /\
  device2 = update_device_state device1 channel_id internal_state channel /\
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue
  ==>
  BD_Q_PRESERVED q1.bds_to_fetch      q2.bds_to_fetch /\
  BD_Q_PRESERVED q1.bds_to_update     q2.bds_to_update /\
  BD_Q_PRESERVED q1.bds_to_process    q2.bds_to_process /\
  BD_Q_PRESERVED q1.bds_to_write_back q2.bds_to_write_back
Proof
INTRO_TAC THEN
ALL_LRTAC THEN
ETAC BD_Q_PRESERVED THEN
ETAC stateTheory.schannel THEN
ETAC operationsTheory.update_device_state THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 LRTAC THEN
 ETAC optionTheory.THE_DEF THEN
 STAC
 ,
 STAC
]
QED

Theorem ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA:
!q1 q2 device1 device2 channel_id' channel_id channel internal_state.
  channel = (schannel device1 channel_id) /\
  device2 = update_device_state device1 channel_id internal_state channel /\
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue
  ==>
  BD_Q_PRESERVED q1.bds_to_fetch q2.bds_to_fetch
Proof
INTRO_TAC THEN
FIRTAC ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_LEMMA THEN
STAC
QED

Theorem ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_UPDATE_LEMMA:
!q1 q2 device1 device2 channel_id' channel_id channel internal_state.
  channel = (schannel device1 channel_id) /\
  device2 = update_device_state device1 channel_id internal_state channel /\
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue
  ==>
  BD_Q_PRESERVED q1.bds_to_update q2.bds_to_update
Proof
INTRO_TAC THEN
FIRTAC ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_LEMMA THEN
STAC
QED

Theorem ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_PROCESS_LEMMA:
!q1 q2 device1 device2 channel_id' channel_id channel internal_state.
  channel = (schannel device1 channel_id) /\
  device2 = update_device_state device1 channel_id internal_state channel /\
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue
  ==>
  BD_Q_PRESERVED q1.bds_to_process q2.bds_to_process
Proof
INTRO_TAC THEN
FIRTAC ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_LEMMA THEN
STAC
QED

Theorem ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA:
!q1 q2 device1 device2 channel_id' channel_id channel internal_state.
  channel = (schannel device1 channel_id) /\
  device2 = update_device_state device1 channel_id internal_state channel /\
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue
  ==>
  BD_Q_PRESERVED q1.bds_to_write_back q2.bds_to_write_back
Proof
INTRO_TAC THEN
FIRTAC ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_LEMMA THEN
STAC
QED

Theorem UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA:
!q1 q2 device1 device2 channel1 channel2 channel_id channel_id' internal_state1.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  channel1 = schannel device1 channel_id /\
  device2 = update_device_state device1 channel_id internal_state1 channel2 /\
  BD_Q_PRESERVED channel1.queue.bds_to_write_back channel2.queue.bds_to_write_back
  ==>
  BD_Q_PRESERVED q1.bds_to_write_back q2.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC operationsTheory.update_device_state THEN
ETAC combinTheory.UPDATE_def THEN
LRTAC THEN
LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 RLTAC THEN
 LRTAC THEN
 LRTAC THEN
 ASM_REWRITE_TAC [optionTheory.THE_DEF]
 ,
 LRTAC THEN
 REWRITE_TAC [BD_Q_PRESERVED]
]
QED



Theorem BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_IMPLIES_EQ_BD_TRANSFER_RAS_WAS_LEMMA:
!device_characteristics device1 device2.
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2
  ==>
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (cverification device_characteristics channel_id).bd_transfer_ras_was device1.dma_state.internal_state =
    (cverification device_characteristics channel_id).bd_transfer_ras_was device2.dma_state.internal_state 
Proof
INTRO_TAC THEN
PTAC BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ THEN
STAC
QED

Theorem BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_PRESERVES_BD_DATA_LEMMA:
!device_characteristics device1 device2 channel_id bd R W ras_was1 ras_was2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2 /\
  ras_was1 = (cverification device_characteristics channel_id).bd_transfer_ras_was device1.dma_state.internal_state bd /\
  ras_was2 = (cverification device_characteristics channel_id).bd_transfer_ras_was device2.dma_state.internal_state bd /\
  BD_DATA R W ras_was1
  ==>
  BD_DATA R W ras_was2
Proof
INTRO_TAC THEN
ALL_LRTAC THEN
IRTAC BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_IMPLIES_EQ_BD_TRANSFER_RAS_WAS_LEMMA THEN
AIRTAC THEN
QLRTAC THEN
STAC
QED

Theorem SCRATCHPAD_ADDRESSES_EQ_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA:
!device_characteristics memory device1 device2.
  SCRATCHPAD_ADDRESSES_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state /\
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device1
  ==>
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_SCRATCHPAD_R_L2 THEN
ETAC stateTheory.SCRATCHPAD_ADDRESSES_EQ THEN
STAC
QED

Theorem SCRATCHPAD_ADDRESSES_EQ_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA:
!device_characteristics memory device1 device2.
  SCRATCHPAD_ADDRESSES_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device1
  ==>
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_SCRATCHPAD_W_L2 THEN
ETAC stateTheory.SCRATCHPAD_ADDRESSES_EQ THEN
STAC
QED

Theorem INVARIANT_SCRATCHPAD_R_W_L2_IMPLIES_SCRATCHPAD_R_W_LEMMA:
!device_characteristics memory device.
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device
  ==>
  SCRATCHPAD_R_W device_characteristics memory device.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC INVARIANT_SCRATCHPAD_W_L2 THEN
PTAC INVARIANT_SCRATCHPAD_R_L2 THEN
ETAC proof_obligationsTheory.SCRATCHPAD_R_W THEN
ETAC proof_obligationsTheory.SCRATCHPAD_W THEN
ETAC proof_obligationsTheory.SCRATCHPAD_R THEN
STAC
QED

val _ = export_theory();

