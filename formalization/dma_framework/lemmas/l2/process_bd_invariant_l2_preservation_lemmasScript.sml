open HolKernel Parse boolLib bossLib helper_tactics;
open l2Theory invariant_l2Theory invariant_l2_lemmasTheory;

val _ = new_theory "process_bd_invariant_l2_preservation_lemmas";

Definition CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_BD_RAS_WAS:
           CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_BD_RAS_WAS
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
(device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
(device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) =
  !channel_id q1 q2.
    VALID_CHANNEL_ID device_characteristics channel_id /\
    q1 = (schannel device1 channel_id).queue /\
    q2 = (schannel device2 channel_id).queue
    ==>
    BD_Q_PRESERVED                                                  q1.bds_to_fetch      q2.bds_to_fetch /\
    BD_Q_PRESERVED                                                  q1.bds_to_update     q2.bds_to_update /\
    BD_Q_TRANSITIONS_BD_RAS_WAS q1.bds_to_process q2.bds_to_process q1.bds_to_write_back q2.bds_to_write_back
End

Theorem CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA:
!device_characteristics device1 device2 memory.
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2 /\
  CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_BD_RAS_WAS device_characteristics device1 device2 /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_FETCH_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_FETCH_BD_L2 THEN
INTRO_TAC THEN
PTAC CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_BD_RAS_WAS THEN
AITAC THEN
ITAC BD_Q_PRESERVED_IMPLIES_POST_MEMBER_PRE_LEMMA THEN
AITAC THEN
IRTAC BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_PRESERVES_BD_DATA_LEMMA THEN
STAC
QED

Theorem CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA:
!device_characteristics device1 device2 memory.
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2 /\
  CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_BD_RAS_WAS device_characteristics device1 device2 /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_UPDATE_BD_L2 THEN
INTRO_TAC THEN
PTAC CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_BD_RAS_WAS THEN
AITAC THEN
FITAC BD_Q_PRESERVED_IMPLIES_POST_MEMBER_PRE_LEMMA THEN
AITAC THEN
IRTAC BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_PRESERVES_BD_DATA_LEMMA THEN
STAC
QED

Theorem CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA:
!device_characteristics device1 device2 memory.
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2 /\
  CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_BD_RAS_WAS device_characteristics device1 device2 /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device1
  ==>
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_TRANSFER_DATA_L2 THEN
INTRO_TAC THEN
PTAC CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_BD_RAS_WAS THEN
AITAC THEN
IRTAC BD_Q_TRANSITIONS_BD_RAS_WAS_IMPLIES_PRE_MEMBER_LEMMA THEN
AITAC THEN
IRTAC BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_PRESERVES_BD_DATA_LEMMA THEN
STAC
QED

Theorem CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA:
!device_characteristics device1 device2 memory.
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2 /\
  CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_BD_RAS_WAS device_characteristics device1 device2 /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device1 /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_WRITE_BACK_BD_L2 THEN
INTRO_TAC THEN
PTAC CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_BD_RAS_WAS THEN
AITAC THEN
IRTAC BD_Q_TRANSITIONS_BD_RAS_WAS_IMPLIES_POST_MEMBER_PRE_MEMBER_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AITAC THEN
 STAC
 ,
 PTAC INVARIANT_TRANSFER_DATA_L2 THEN
 AITAC THEN
 STAC
]
QED




















Theorem TRANSFERRING_DATA_REPLIES_REQUESTS_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_UPDATE_PROCESS_WRITE_BACK_LEMMA:
!internal_state2 channel2 requests complete pending_reqplies p internal_state1 channel1 bd.
  (internal_state2, channel2, requests, complete) = transferring_data_replies_requests pending_reqplies p internal_state1 channel1 bd
  ==>
  BD_Q_PRESERVED channel1.queue.bds_to_fetch channel2.queue.bds_to_fetch /\
  BD_Q_PRESERVED channel1.queue.bds_to_update channel2.queue.bds_to_update /\
  BD_Q_PRESERVED channel1.queue.bds_to_process channel2.queue.bds_to_process /\
  BD_Q_PRESERVED channel1.queue.bds_to_write_back channel2.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_replies_requests THEN
EQ_PAIR_ASM_TAC THEN
ALL_RLTAC THEN
PTAC operationsTheory.transferring_data_clear_replies THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [BD_Q_PRESERVED_REFL_LEMMA]
QED

Theorem TRANSFERRING_DATA_UPDATE_QS_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_UPDATE_LEMMA:
!channel1 channel2 bd bds.
  channel2 = transferring_data_update_qs channel1 bd bds
  ==>
  BD_Q_PRESERVED channel1.queue.bds_to_fetch channel2.queue.bds_to_fetch /\
  BD_Q_PRESERVED channel1.queue.bds_to_update channel2.queue.bds_to_update
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_update_qs THEN
ETAC operationsTheory.update_channel_qs THEN
ETAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [BD_Q_PRESERVED_REFL_LEMMA]
QED

Theorem TRANSFERRING_DATA_UPDATE_QS_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_PROCESS_WRITE_BACK_LEMMA:
!channel1 channel2 bd bds.
  bd::bds = channel1.queue.bds_to_process /\
  channel2 = transferring_data_update_qs channel1 bd bds
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS
    channel1.queue.bds_to_process channel2.queue.bds_to_process
    channel1.queue.bds_to_write_back channel2.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_update_qs THEN
ETAC operationsTheory.update_channel_qs THEN
ETAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
LRTAC THEN
RLTAC THEN
RECORD_TAC THEN
PTAC BD_Q_TRANSITIONS_BD_RAS_WAS THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
PTAC BD_Q_TRANSITION_BD_RAS_WAS THEN
PTAC BD_Q_TRANSITION THEN
REWRITE_TAC [combinTheory.I_THM]
QED

Theorem TRANSFERRING_DATA_APPEND_REQUESTS_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_UPDATE_PROCESS_WRITE_BACK_LEMMA:
!channel1 channel2 requests.
  channel2 = transferring_data_append_requests channel1 requests
  ==>
  BD_Q_PRESERVED channel1.queue.bds_to_fetch channel2.queue.bds_to_fetch /\
  BD_Q_PRESERVED channel1.queue.bds_to_update channel2.queue.bds_to_update /\
  BD_Q_PRESERVED channel1.queue.bds_to_process channel2.queue.bds_to_process /\
  BD_Q_PRESERVED channel1.queue.bds_to_write_back channel2.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_append_requests THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [BD_Q_PRESERVED_REFL_LEMMA]
QED

Theorem TRANSFERRING_DATA_L2_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_UPDATE_LEMMA:
!device_characteristics device1 device2 internal_state1 internal_state2 channel1
 channel2 channel_id channel_id' q1 q2 memory.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = (schannel device1 channel_id) /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = transferring_data_l2 device_characteristics channel_id memory internal_state1 channel1 /\
  VALID_CHANNEL_ID device_characteristics channel_id' /\
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue
  ==>
  BD_Q_PRESERVED q1.bds_to_fetch q2.bds_to_fetch /\
  BD_Q_PRESERVED q1.bds_to_update q2.bds_to_update
Proof
INTRO_TAC THEN
PTAC transferring_data_l2 THENL
[
 FIRTAC TRANSFERRING_DATA_REPLIES_REQUESTS_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_UPDATE_PROCESS_WRITE_BACK_LEMMA THEN
 IF_SPLIT_TAC THENL
 [
  IRTAC TRANSFERRING_DATA_UPDATE_QS_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_UPDATE_LEMMA THEN
  EQ_PAIR_ASM_TAC THEN
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_UPDATE_PROCESS_WRITE_BACK_LEMMA THEN
  FIRTAC BD_PRESERVED_TRANSITIVITY_LEMMA THEN
  FIRTAC BD_PRESERVED_TRANSITIVITY_LEMMA THEN
  FIRTAC BD_PRESERVED_TRANSITIVITY_LEMMA THEN
  FIRTAC BD_PRESERVED_TRANSITIVITY_LEMMA THEN
  FITAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA THEN
  FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_UPDATE_LEMMA THEN
  STAC
  ,
  EQ_PAIR_ASM_TAC THEN
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_UPDATE_PROCESS_WRITE_BACK_LEMMA THEN
  FIRTAC BD_PRESERVED_TRANSITIVITY_LEMMA THEN
  FIRTAC BD_PRESERVED_TRANSITIVITY_LEMMA THEN
  FITAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA THEN
  FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_UPDATE_LEMMA THEN
  STAC
 ]
 ,
 EQ_PAIR_ASM_TAC THEN
 FIRTAC TRANSFERRING_DATA_REPLIES_REQUESTS_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_UPDATE_PROCESS_WRITE_BACK_LEMMA THEN
 IF_SPLIT_TAC THENL
 [
  IRTAC TRANSFERRING_DATA_UPDATE_QS_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_UPDATE_LEMMA THEN
  FIRTAC BD_PRESERVED_TRANSITIVITY_LEMMA THEN
  FIRTAC BD_PRESERVED_TRANSITIVITY_LEMMA THEN
  RLTAC THEN
  RLTAC THEN
  FITAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA THEN
  FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_UPDATE_LEMMA THEN
  STAC
  ,
  RLTAC THEN
  RLTAC THEN
  RLTAC THEN
  FITAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA THEN
  FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_UPDATE_LEMMA THEN
  STAC
 ]
 ,
 EQ_PAIR_ASM_TAC THEN
 FITAC (REWRITE_RULE [BD_Q_PRESERVED] UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA) THEN
 FIRTAC (REWRITE_RULE [BD_Q_PRESERVED] UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_UPDATE_LEMMA) THEN
 ASM_REWRITE_TAC [BD_Q_PRESERVED]
]
QED

Theorem BD_Q_PRESERVED_IMPLIES_SAME_Q_LEMMA:
!channel1 channel bd bds.
  bd::bds = channel1.queue.bds_to_process /\
  BD_Q_PRESERVED channel1.queue.bds_to_process channel.queue.bds_to_process
  ==>
  bd::bds = channel.queue.bds_to_process
Proof
INTRO_TAC THEN
ETAC BD_Q_PRESERVED THEN
STAC
QED

Theorem TRANSFERRING_DATA_L2_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_PROCESS_WRITE_BACK_LEMMA:
!internal_state2 channel2 device_characteristics channel_id memory
 internal_state1 channel1 q1 q2 device2 device1 channel_id'.
  (internal_state2, channel2) = transferring_data_l2 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  channel1 = schannel device1 channel_id /\
  q2 = (schannel device2 channel_id').queue /\
  q1 = (schannel device1 channel_id').queue
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS q1.bds_to_process q2.bds_to_process q1.bds_to_write_back q2.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC transferring_data_l2 THENL
[
 IRTAC TRANSFERRING_DATA_REPLIES_REQUESTS_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_UPDATE_PROCESS_WRITE_BACK_LEMMA THEN
 IF_SPLIT_TAC THENL
 [
  ITAC BD_Q_PRESERVED_IMPLIES_SAME_Q_LEMMA THEN
  FIRTAC TRANSFERRING_DATA_UPDATE_QS_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_PROCESS_WRITE_BACK_LEMMA THEN
  EQ_PAIR_ASM_TAC THEN
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_UPDATE_PROCESS_WRITE_BACK_LEMMA THEN
  ETAC BD_Q_PRESERVED THEN
  LRTAC THEN
  LRTAC THEN
  RLTAC THEN
  RLTAC THEN
  FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_PROCESS_WRITE_BACK_LEMMA THEN
  STAC
  ,
  EQ_PAIR_ASM_TAC THEN
  IRTAC TRANSFERRING_DATA_APPEND_REQUESTS_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_UPDATE_PROCESS_WRITE_BACK_LEMMA THEN
  FIRTAC BD_PRESERVED_TRANSITIVITY_LEMMA THEN
  FIRTAC BD_PRESERVED_TRANSITIVITY_LEMMA THEN
  FIRTAC BD_PRESERVED_TRANSITIVITY_LEMMA THEN
  FIRTAC BD_PRESERVED_TRANSITIVITY_LEMMA THEN
  PTAC BD_Q_TRANSITIONS_BD_RAS_WAS THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  PTAC BD_Q_PRESERVED_PRESERVED THEN
  CONJS_TAC THENL
  [
   FITAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_PROCESS_LEMMA THEN
   STAC
   ,
   FITAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN
   STAC
  ]
 ]
 ,
 EQ_PAIR_ASM_TAC THEN
 IRTAC TRANSFERRING_DATA_REPLIES_REQUESTS_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_UPDATE_PROCESS_WRITE_BACK_LEMMA THEN
 IF_SPLIT_TAC THENL
 [
  ITAC BD_Q_PRESERVED_IMPLIES_SAME_Q_LEMMA THEN
  FIRTAC TRANSFERRING_DATA_UPDATE_QS_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_PROCESS_WRITE_BACK_LEMMA THEN
  FIRTAC BD_Q_PRESERVED_BD_Q_TRANSITIONS_BD_RAS_WAS_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_LEMMA THEN
  FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_PROCESS_WRITE_BACK_LEMMA THEN
  STAC
  ,
  RLTAC THEN RLTAC THEN RLTAC THEN
  PTAC BD_Q_TRANSITIONS_BD_RAS_WAS THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  PTAC BD_Q_PRESERVED_PRESERVED THEN
  CONJS_TAC THENL
  [
   FITAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_PROCESS_LEMMA THEN
   STAC
   ,
   FITAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN
   STAC
  ]
 ]
 ,
 EQ_PAIR_ASM_TAC THEN
 ITAC ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_LEMMA THEN
 PTAC BD_Q_TRANSITIONS_BD_RAS_WAS THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 PTAC BD_Q_PRESERVED_PRESERVED THEN
 CONJS_TAC THENL
 [
  FITAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_PROCESS_LEMMA THEN
  STAC
  ,
  FITAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN
  STAC
 ]
]
QED

Theorem TRANSFERRING_DATA_L2_IMPLIES_CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_BD_RAS_WAS_LEMMA:
!device_characteristics device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id memory.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = (schannel device1 channel_id) /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = transferring_data_l2 device_characteristics channel_id memory internal_state1 channel1
  ==>
  CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_BD_RAS_WAS device_characteristics device1 device2
Proof
INTRO_TAC THEN
PTAC CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_BD_RAS_WAS THEN
INTRO_TAC THEN
CONJS_TAC THENL
[
 FIRTAC TRANSFERRING_DATA_L2_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_UPDATE_LEMMA THEN STAC
 ,
 FIRTAC TRANSFERRING_DATA_L2_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_UPDATE_LEMMA THEN STAC
 ,
 FIRTAC TRANSFERRING_DATA_L2_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_PROCESS_WRITE_BACK_LEMMA THEN STAC
]
QED



Theorem PROCESSING_BD_L2_IMPLIES_SCRATCHPAD_ADDRESSES_EQ_LEMMA:
!device_characteristics channel_id device1 device2 internal_state1 internal_state2 channel1 channel2 memory.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_SCRATCHPAD device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = transferring_data_l2 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  SCRATCHPAD_ADDRESSES_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
ETAC stateTheory.SCRATCHPAD_ADDRESSES_EQ THEN
PTAC l2Theory.transferring_data_l2 THENL
[
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 PTAC operationsTheory.transferring_data_replies_requests THEN
 EQ_PAIR_ASM_TAC THEN
 NLRTAC 4 THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_SCRATCHPAD THEN
 AIRTAC THEN
 PTAC operationsTheory.update_device_state THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 PTAC operationsTheory.transferring_data_replies_requests THEN
 EQ_PAIR_ASM_TAC THEN
 NLRTAC 4 THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_SCRATCHPAD THEN
 AIRTAC THEN
 PTAC operationsTheory.update_device_state THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 PTAC operationsTheory.update_device_state THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
]
QED

Theorem PROCESSING_BD_L2_IMPLIES_BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_LEMMA:
!device_characteristics channel_id device1 device2 internal_state1 internal_state2 channel1 channel2 memory.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = transferring_data_l2 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2
Proof
INTRO_TAC THEN
ETAC BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ THEN
INTRO_TAC THEN
REWRITE_TAC [boolTheory.FUN_EQ_THM] THEN
GEN_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION THEN
PTAC l2Theory.transferring_data_l2 THENL
[
 EQ_PAIR_ASM_TAC THEN
 PTAC operationsTheory.transferring_data_replies_requests THEN
 EQ_PAIR_ASM_TAC THEN
 NLRTAC 4 THEN
 AIRTAC THEN
 AIRTAC THEN
 RLTAC THEN
 PTAC operationsTheory.update_device_state THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 PTAC operationsTheory.transferring_data_replies_requests THEN
 EQ_PAIR_ASM_TAC THEN
 NLRTAC 4 THEN
 AIRTAC THEN
 AIRTAC THEN
 RLTAC THEN
 PTAC operationsTheory.update_device_state THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 PTAC operationsTheory.update_device_state THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
]
QED

Theorem PROCESSING_BD_L2_PRESERVES_FETCH_UPDATE_PROCESS_WRITE_BACK_SCRATCHPAD_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION device_characteristics /\

  INVARIANT_FETCH_BD_L2 device_characteristics memory device1 /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device1 /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device1 /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device1 /\
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device1 /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device1 /\

  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = (schannel device1 channel_id) /\
  (internal_state2, channel2) = transferring_data_l2 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  INVARIANT_FETCH_BD_L2 device_characteristics memory device2 /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device2 /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device2 /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device2 /\
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device2 /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ITAC PROCESSING_BD_L2_IMPLIES_SCRATCHPAD_ADDRESSES_EQ_LEMMA THEN
ITAC PROCESSING_BD_L2_IMPLIES_BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_LEMMA THEN
ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_IMPLIES_PENDING_REGISTER_RELEATED_MEMORY_REQUESTS_IN_POST_STATE_LEMMA THEN
ITAC SCRATCHPAD_ADDRESSES_EQ_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA THEN
ITAC SCRATCHPAD_ADDRESSES_EQ_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA THEN
IRTAC TRANSFERRING_DATA_L2_IMPLIES_CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_BD_RAS_WAS_LEMMA THEN
ITAC CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA THEN
ITAC CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA THEN
ITAC CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA THEN
ITAC CHANNELS_TRANSFER_DATA_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA THEN
STAC
QED

val _ = export_theory();

