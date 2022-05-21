open HolKernel Parse boolLib bossLib helper_tactics;
open invariant_l2Theory invariant_l2_lemmasTheory;

val _ = new_theory "update_bd_invariant_l2_preservation_lemmas";

Definition CHANNELS_UPDATE_BD_Q_TRANSITIONS_BD_RAS_WAS:
           CHANNELS_UPDATE_BD_Q_TRANSITIONS_BD_RAS_WAS
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
(device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
(device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) =
  !channel_id q1 q2.
    VALID_CHANNEL_ID device_characteristics channel_id /\
    q1 = (schannel device1 channel_id).queue /\
    q2 = (schannel device2 channel_id).queue
    ==>
    BD_Q_PRESERVED                                                q1.bds_to_fetch      q2.bds_to_fetch /\
    BD_Q_TRANSITIONS_BD_RAS_WAS q1.bds_to_update q2.bds_to_update q1.bds_to_process    q2.bds_to_process /\
    BD_Q_PRESERVED                                                q1.bds_to_write_back q2.bds_to_write_back
End

Theorem CHANNELS_UPDATE_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA:
!device_characteristics device1 device2 memory.
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2 /\
  CHANNELS_UPDATE_BD_Q_TRANSITIONS_BD_RAS_WAS device_characteristics device1 device2 /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_FETCH_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_FETCH_BD_L2 THEN
INTRO_TAC THEN
PTAC CHANNELS_UPDATE_BD_Q_TRANSITIONS_BD_RAS_WAS THEN
AITAC THEN
ITAC BD_Q_PRESERVED_IMPLIES_POST_MEMBER_PRE_LEMMA THEN
AITAC THEN
IRTAC BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_PRESERVES_BD_DATA_LEMMA THEN
STAC
QED

Theorem CHANNELS_UPDATE_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA:
!device_characteristics device1 device2 memory.
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2 /\
  CHANNELS_UPDATE_BD_Q_TRANSITIONS_BD_RAS_WAS device_characteristics device1 device2 /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_UPDATE_BD_L2 THEN
INTRO_TAC THEN
PTAC CHANNELS_UPDATE_BD_Q_TRANSITIONS_BD_RAS_WAS THEN
AITAC THEN
IRTAC BD_Q_TRANSITIONS_BD_RAS_WAS_IMPLIES_PRE_MEMBER_LEMMA THEN
AITAC THEN
IRTAC BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_PRESERVES_BD_DATA_LEMMA THEN
STAC
QED

Theorem CHANNELS_UPDATE_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA:
!device_characteristics device1 device2 memory.
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2 /\
  CHANNELS_UPDATE_BD_Q_TRANSITIONS_BD_RAS_WAS device_characteristics device1 device2 /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device1 /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device1
  ==>
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_TRANSFER_DATA_L2 THEN
INTRO_TAC THEN
PTAC CHANNELS_UPDATE_BD_Q_TRANSITIONS_BD_RAS_WAS THEN
AITAC THEN
IRTAC BD_Q_TRANSITIONS_BD_RAS_WAS_IMPLIES_POST_MEMBER_PRE_MEMBER_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AITAC THEN
 IRTAC BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_PRESERVES_BD_DATA_LEMMA THEN
 STAC
 ,
 PTAC INVARIANT_UPDATE_BD_L2 THEN
 AITAC THEN
 ITAC BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_PRESERVES_BD_DATA_LEMMA THEN
 STAC
]
QED

Theorem CHANNELS_UPDATE_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA:
!device_characteristics device1 device2 memory.
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2 /\
  CHANNELS_UPDATE_BD_Q_TRANSITIONS_BD_RAS_WAS device_characteristics device1 device2 /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_WRITE_BACK_BD_L2 THEN
INTRO_TAC THEN
PTAC CHANNELS_UPDATE_BD_Q_TRANSITIONS_BD_RAS_WAS THEN
AITAC THEN
FIRTAC BD_Q_PRESERVED_IMPLIES_POST_MEMBER_PRE_LEMMA THEN
AIRTAC THEN
STAC
QED



























Theorem UPDATING_BD_UPDATE_QS_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA:
!channel1 channel2 update_status bd_ras_was bd_ras_wass.
  channel2 = updating_bd_update_qs update_status channel1 bd_ras_was bd_ras_wass
  ==>
  BD_Q_PRESERVED channel1.queue.bds_to_fetch channel2.queue.bds_to_fetch
Proof
INTRO_TAC THEN
PTAC operationsTheory.updating_bd_update_qs THENL
[
 ASM_REWRITE_TAC [BD_Q_PRESERVED]
 ,
 PTAC operationsTheory.update_channel_qs THEN
 PTAC operationsTheory.update_qs THEN
 ETAC listTheory.FOLDL THEN
 PTAC operationsTheory.update_q THEN
 PTAC operationsTheory.update_q THEN
 LRTAC THEN
 RECORD_TAC THEN
 REWRITE_TAC [BD_Q_PRESERVED]
]
QED

Theorem UPDATING_BD_APPEND_REQUEST_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA:
!channel1 channel2 write_address_bytes tag.
  channel2 = updating_bd_append_request channel1 write_address_bytes tag
  ==>
  BD_Q_PRESERVED channel1.queue.bds_to_fetch channel2.queue.bds_to_fetch
Proof
INTRO_TAC THEN
PTAC operationsTheory.updating_bd_append_request THENL
[
 ASM_REWRITE_TAC [BD_Q_PRESERVED]
 ,
 LRTAC THEN
 RECORD_TAC THEN
 REWRITE_TAC [BD_Q_PRESERVED]
]
QED

Theorem UPDATING_BD_UPDATE_QS_UPDATING_BD_APPEND_REQUEST_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA:
!q1 q2 device1 device2 channel_id' channel_id channel1 channel2 channel3
 internal_state update_status bd_ras_was bd_ras_wass
 write_address_bytes tag.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  channel1 = schannel device1 channel_id /\
  channel2 = updating_bd_update_qs update_status channel1 bd_ras_was bd_ras_wass /\
  channel3 = updating_bd_append_request channel2 write_address_bytes tag /\
  device2 = update_device_state device1 channel_id internal_state channel3
  ==>
  BD_Q_PRESERVED q1.bds_to_fetch q2.bds_to_fetch
Proof
INTRO_TAC THEN
IRTAC UPDATING_BD_UPDATE_QS_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA THEN
IRTAC UPDATING_BD_APPEND_REQUEST_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA THEN
FIRTAC BD_PRESERVED_TRANSITIVITY_LEMMA THEN
FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA THEN
STAC
QED

Theorem UPDATING_BD_UPDATE_QS_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_UPDATE_BDS_TO_PROCESS_LEMMA:
!channel1 channel2 update_status bd_ras_was bd_ras_wass.
  channel1.queue.bds_to_update = bd_ras_was::bd_ras_wass /\
  channel2 = updating_bd_update_qs update_status channel1 bd_ras_was bd_ras_wass
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS channel1.queue.bds_to_update  channel2.queue.bds_to_update
                              channel1.queue.bds_to_process channel2.queue.bds_to_process
Proof
INTRO_TAC THEN
PTAC operationsTheory.updating_bd_update_qs THENL
[
 ALL_LRTAC THEN
 PTAC BD_Q_TRANSITIONS_BD_RAS_WAS THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 REWRITE_TAC [BD_Q_PRESERVED_PRESERVED, BD_Q_PRESERVED]
 ,
 ETAC operationsTheory.update_channel_qs THEN
 ETAC operationsTheory.update_qs THEN
 ETAC listTheory.FOLDL THEN
 ETAC operationsTheory.update_q THEN
 ALL_LRTAC THEN
 RECORD_TAC THEN
 ETAC BD_Q_TRANSITIONS_BD_RAS_WAS THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
 ETAC BD_Q_TRANSITION_BD_RAS_WAS THEN
 ETAC BD_Q_TRANSITION THEN
 REWRITE_TAC [combinTheory.I_THM]
]
QED

Theorem UPDATING_BD_APPEND_REQUEST_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA:
!channel1 channel2 write_address_bytes tag.
  channel2 = updating_bd_append_request channel1 write_address_bytes tag
  ==>
  BD_Q_PRESERVED channel1.queue.bds_to_write_back channel2.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC operationsTheory.updating_bd_append_request THENL
[
 ASM_REWRITE_TAC [BD_Q_PRESERVED]
 ,
 LRTAC THEN
 RECORD_TAC THEN
 REWRITE_TAC [BD_Q_PRESERVED]
]
QED

Theorem UPDATING_BD_APPEND_REQUEST_PRESERVES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_UPDATE_BDS_TO_PROCESS_LEMMA:
!channel1 channel2 channel3 write_address_bytes tag.
  channel3 = updating_bd_append_request channel2 write_address_bytes tag /\
  BD_Q_TRANSITIONS_BD_RAS_WAS channel1.queue.bds_to_update  channel2.queue.bds_to_update
                              channel1.queue.bds_to_process channel2.queue.bds_to_process
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS channel1.queue.bds_to_update  channel3.queue.bds_to_update
                              channel1.queue.bds_to_process channel3.queue.bds_to_process
Proof
INTRO_TAC THEN
PTAC operationsTheory.updating_bd_append_request THENL
[
 STAC
 ,
 LRTAC THEN
 RECORD_TAC THEN
 STAC
]
QED

Theorem UPDATING_BD_UPDATE_QS_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA:
!channel1 channel2 update_status bd_ras_was bd_ras_wass.
  channel2 = updating_bd_update_qs update_status channel1 bd_ras_was bd_ras_wass
  ==>
  BD_Q_PRESERVED channel1.queue.bds_to_write_back channel2.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC operationsTheory.updating_bd_update_qs THENL
[
 ASM_REWRITE_TAC [BD_Q_PRESERVED]
 ,
 PTAC operationsTheory.update_channel_qs THEN
 PTAC operationsTheory.update_qs THEN
 ETAC listTheory.FOLDL THEN
 PTAC operationsTheory.update_q THEN
 PTAC operationsTheory.update_q THEN
 LRTAC THEN
 RECORD_TAC THEN
 REWRITE_TAC [BD_Q_PRESERVED]
]
QED

Theorem UPDATING_BD_UPDATE_QS_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_UPDATE_BDS_TO_PROCESS_LEMMA:
!q1 q2 device1 device2 channel_id' channel_id channel1 channel2
 internal_state update_status bd_ras_was bd_ras_wass write_address_bytes tag.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  channel1 = schannel device1 channel_id /\
  channel1.queue.bds_to_update = bd_ras_was::bd_ras_wass /\
  channel2 = updating_bd_update_qs update_status channel1 bd_ras_was bd_ras_wass /\
  device2 = update_device_state device1 channel_id internal_state channel2
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS q1.bds_to_update q2.bds_to_update q1.bds_to_process q2.bds_to_process
Proof
INTRO_TAC THEN
IRTAC UPDATING_BD_UPDATE_QS_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_UPDATE_BDS_TO_PROCESS_LEMMA THEN
FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_UPDATE_BDS_TO_PROCESS_LEMMA THEN
STAC
QED

Theorem UPDATING_BD_UPDATE_QS_UPDATING_BD_APPEND_REQUEST_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_UPDATE_BDS_TO_PROCESS_LEMMA:
!q1 q2 device1 device2 channel_id' channel_id channel1 channel2 channel3
 internal_state update_status bd_ras_was bd_ras_wass write_address_bytes tag.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  channel1 = schannel device1 channel_id /\
  channel1.queue.bds_to_update = bd_ras_was::bd_ras_wass /\
  channel2 = updating_bd_update_qs update_status channel1 bd_ras_was bd_ras_wass /\
  channel3 = updating_bd_append_request channel2 write_address_bytes tag /\
  device2 = update_device_state device1 channel_id internal_state channel3
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS q1.bds_to_update q2.bds_to_update q1.bds_to_process q2.bds_to_process
Proof
INTRO_TAC THEN
IRTAC UPDATING_BD_UPDATE_QS_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_UPDATE_BDS_TO_PROCESS_LEMMA THEN
IRTAC UPDATING_BD_APPEND_REQUEST_PRESERVES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_UPDATE_BDS_TO_PROCESS_LEMMA THEN
FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_UPDATE_BDS_TO_PROCESS_LEMMA THEN
STAC
QED



Theorem UPDATING_BD_UPDATE_QS_UPDATING_BD_APPEND_REQUEST_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA:
!q1 q2 device1 device2 channel_id' channel_id channel1 channel2 channel3
 internal_state bd_ras_was bd_ras_wass write_address_bytes tag update_status.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  channel1 = schannel device1 channel_id /\
  channel2 = updating_bd_update_qs update_status channel1 bd_ras_was bd_ras_wass /\
  channel3 = updating_bd_append_request channel2 write_address_bytes tag /\
  device2 = update_device_state device1 channel_id internal_state channel3
  ==>
  BD_Q_PRESERVED q1.bds_to_write_back q2.bds_to_write_back
Proof
INTRO_TAC THEN
IRTAC UPDATING_BD_UPDATE_QS_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN
IRTAC UPDATING_BD_APPEND_REQUEST_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN
FIRTAC BD_PRESERVED_TRANSITIVITY_LEMMA THEN
FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN
STAC
QED



Theorem UPDATING_BD_UPDATE_QS_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_UPDATE_BDS_TO_PROCESS_LEMMA:
!channel1 channel2 update_status bd_ras_was bd_ras_wass.
  channel1.queue.bds_to_update = bd_ras_was::bd_ras_wass /\
  channel2 = updating_bd_update_qs update_status channel1 bd_ras_was bd_ras_wass
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS channel1.queue.bds_to_update  channel2.queue.bds_to_update
                              channel1.queue.bds_to_process channel2.queue.bds_to_process
Proof
INTRO_TAC THEN
PTAC operationsTheory.updating_bd_update_qs THENL
[
 LRTAC THEN
 REWRITE_TAC [BD_Q_TRANSITIONS_BD_RAS_WAS_SAME_QS_LEMMA]
 ,
 PTAC operationsTheory.update_channel_qs THEN
 PTAC operationsTheory.update_qs THEN
 ETAC listTheory.FOLDL THEN
 ETAC operationsTheory.update_q THEN
 LRTAC THEN
 RECORD_TAC THEN
 LRTAC THEN
 PTAC BD_Q_TRANSITIONS_BD_RAS_WAS THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
 PTAC BD_Q_TRANSITION_BD_RAS_WAS THEN
 PTAC BD_Q_TRANSITION THEN
 REWRITE_TAC [combinTheory.I_THM]
]
QED



Theorem UPDATING_BD_UPDATE_QS_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA:
!q1 q2 
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 internal_state channel1 channel2 channel_id' channel_id update_status bd_ras_was bd_ras_wass.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  channel1 = schannel device1 channel_id /\
  channel2 = updating_bd_update_qs update_status channel1 bd_ras_was bd_ras_wass /\
  device2 = update_device_state device1 channel_id internal_state channel2
  ==>
  BD_Q_PRESERVED q1.bds_to_fetch q2.bds_to_fetch
Proof
INTRO_TAC THEN
IRTAC UPDATING_BD_UPDATE_QS_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA THEN
FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA THEN
STAC
QED

Theorem UPDATING_BD_UPDATE_QS_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_UPDATE_BDS_TO_PROCESS_LEMMA:
!q1 q2 
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 internal_state channel1 channel2 channel_id channel_id' bd_ras_was bd_ras_wass update_status.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  channel1 = schannel device1 channel_id /\
  channel1.queue.bds_to_update = bd_ras_was::bd_ras_wass /\
  channel2 = updating_bd_update_qs update_status channel1 bd_ras_was bd_ras_wass /\
  device2 = update_device_state device1 channel_id internal_state channel2
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS q1.bds_to_update q2.bds_to_update q1.bds_to_process q2.bds_to_process
Proof
INTRO_TAC THEN
IRTAC UPDATING_BD_UPDATE_QS_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_UPDATE_BDS_TO_PROCESS_LEMMA THEN
FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_UPDATE_BDS_TO_PROCESS_LEMMA THEN
STAC
QED

Theorem UPDATING_BD_UPDATE_QS_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA:
!q1 q2
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 internal_state channel1 channel2 channel_id channel_id' update_status bd_ras_was bd_ras_wass.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  channel1 = schannel device1 channel_id /\
  channel2 = updating_bd_update_qs update_status channel1 bd_ras_was bd_ras_wass /\
  device2 = update_device_state device1 channel_id internal_state channel2
  ==>
  BD_Q_PRESERVED q1.bds_to_write_back q2.bds_to_write_back
Proof
INTRO_TAC THEN
IRTAC UPDATING_BD_UPDATE_QS_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN
FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN
STAC
QED



Theorem UPDATING_BD_L2_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 device2 internal_state1 internal_state2 channel1 channel2 channel_id memory channel_id' q1 q2.
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = (schannel device1 channel_id) /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = updating_bd_l2 device_characteristics channel_id memory internal_state1 channel1 /\
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue
  ==>
  BD_Q_PRESERVED q1.bds_to_fetch q2.bds_to_fetch
Proof
INTRO_TAC THEN
PTAC l2Theory.updating_bd_l2 THENL
[
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN RLTAC THEN
 ALL_LRTAC THEN
 FIRTAC UPDATING_BD_UPDATE_QS_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 ALL_LRTAC THEN
 FIRTAC UPDATING_BD_UPDATE_QS_UPDATING_BD_APPEND_REQUEST_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ALL_LRTAC THEN
 FIRTAC ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ALL_LRTAC THEN
 FIRTAC ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_LEMMA THEN
 STAC
]
QED

Theorem UPDATING_BD_L2_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_UPDATE_BDS_TO_PROCESS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 device2 internal_state1 internal_state2 channel1
 channel2 channel_id channel_id' q1 q2 memory.
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = (schannel device1 channel_id) /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = updating_bd_l2 device_characteristics channel_id memory internal_state1 channel1 /\
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS q1.bds_to_update q2.bds_to_update q1.bds_to_process q2.bds_to_process
Proof
INTRO_TAC THEN
PTAC l2Theory.updating_bd_l2 THENL
[
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN RLTAC THEN
 ALL_LRTAC THEN
 FIRTAC UPDATING_BD_UPDATE_QS_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_UPDATE_BDS_TO_PROCESS_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 ALL_LRTAC THEN
 FIRTAC UPDATING_BD_UPDATE_QS_UPDATING_BD_APPEND_REQUEST_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_UPDATE_BDS_TO_PROCESS_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 PTAC BD_Q_TRANSITIONS_BD_RAS_WAS THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 PTAC BD_Q_PRESERVED_PRESERVED THEN
 FITAC ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_UPDATE_LEMMA THEN
 FITAC ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_PROCESS_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 PTAC BD_Q_TRANSITIONS_BD_RAS_WAS THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 PTAC BD_Q_PRESERVED_PRESERVED THEN
 FITAC ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_UPDATE_LEMMA THEN
 FITAC ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_PROCESS_LEMMA THEN
 STAC
]
QED

Theorem UPDATING_BD_L2_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 device2 internal_state1 internal_state2 channel1 memory
 channel2 channel_id channel_id' q1 q2.
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = (schannel device1 channel_id) /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = updating_bd_l2 device_characteristics channel_id memory internal_state1 channel1 /\
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue
  ==>
  BD_Q_PRESERVED q1.bds_to_write_back q2.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC l2Theory.updating_bd_l2 THENL
[
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN RLTAC THEN
 ALL_LRTAC THEN
 FIRTAC UPDATING_BD_UPDATE_QS_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 ALL_LRTAC THEN
 FIRTAC UPDATING_BD_UPDATE_QS_UPDATING_BD_APPEND_REQUEST_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN RLTAC THEN
 ALL_LRTAC THEN
 FIRTAC ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 FIRTAC ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN
 STAC
]
QED

Theorem UPDATING_BD_L2_IMPLIES_CHANNELS_UPDATE_BD_Q_TRANSITIONS_BD_RAS_WAS_LEMMA:
!device_characteristics device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id memory.
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = (schannel device1 channel_id) /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = updating_bd_l2 device_characteristics channel_id memory internal_state1 channel1
  ==>
  CHANNELS_UPDATE_BD_Q_TRANSITIONS_BD_RAS_WAS device_characteristics device1 device2
Proof
INTRO_TAC THEN
PTAC CHANNELS_UPDATE_BD_Q_TRANSITIONS_BD_RAS_WAS THEN
INTRO_TAC THEN
REPEAT CONJ_TAC THENL
[
 FIRTAC UPDATING_BD_L2_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA THEN STAC
 ,
 FIRTAC UPDATING_BD_L2_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_BDS_TO_UPDATE_BDS_TO_PROCESS_LEMMA THEN STAC
 ,
 FIRTAC UPDATING_BD_L2_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN STAC
]
QED














Theorem UPDATING_BD_L2_IMPLIES_SCRATCHPAD_ADDRESSES_EQ_LEMMA:
!device_characteristics channel_id device1 device2 internal_state1 internal_state2 channel1 channel2 memory.
  PROOF_OBLIGATION_UPDATE_BD_PRESERVES_SCRATCHPAD device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = updating_bd_l2 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  SCRATCHPAD_ADDRESSES_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
ETAC stateTheory.SCRATCHPAD_ADDRESSES_EQ THEN
PTAC l2Theory.updating_bd_l2 THENL
[
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_UPDATE_BD_PRESERVES_SCRATCHPAD THEN
 AIRTAC THEN
 PTAC operationsTheory.update_device_state THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_UPDATE_BD_PRESERVES_SCRATCHPAD THEN
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
 ,
 EQ_PAIR_ASM_TAC THEN
 PTAC operationsTheory.update_device_state THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
]
QED

Theorem UPDATING_BD_L2_IMPLIES_BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_LEMMA:
!device_characteristics channel_id device1 device2 internal_state1 internal_state2 channel1 channel2 memory.
  PROOF_OBLIGATION_UPDATING_BD_PRESERVES_BD_INTERPRETATION device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = updating_bd_l2 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2
Proof
INTRO_TAC THEN
ETAC BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ THEN
INTRO_TAC THEN
REWRITE_TAC [boolTheory.FUN_EQ_THM] THEN
GEN_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_UPDATING_BD_PRESERVES_BD_INTERPRETATION THEN
PTAC l2Theory.updating_bd_l2 THENL
[
 EQ_PAIR_ASM_TAC THEN
 AIRTAC THEN
 AIRTAC THEN
 RLTAC THEN
 PTAC operationsTheory.update_device_state THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
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
 ,
 EQ_PAIR_ASM_TAC THEN
 PTAC operationsTheory.update_device_state THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
]
QED



Theorem UPDATING_BD_L2_PRESERVES_FETCH_UPDATE_PROCESS_WRITE_BACK_SCRATCHPAD_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_UPDATE_BD_PRESERVES_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_UPDATING_BD_PRESERVES_BD_INTERPRETATION device_characteristics /\

  INVARIANT_FETCH_BD_L2 device_characteristics memory device1 /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device1 /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device1 /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device1 /\
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device1 /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device1 /\

  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = (schannel device1 channel_id) /\
  (internal_state2, channel2) = updating_bd_l2 device_characteristics channel_id memory internal_state1 channel1 /\
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
ITAC UPDATING_BD_L2_IMPLIES_SCRATCHPAD_ADDRESSES_EQ_LEMMA THEN
ITAC UPDATING_BD_L2_IMPLIES_BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_LEMMA THEN
ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_IMPLIES_PENDING_REGISTER_RELEATED_MEMORY_REQUESTS_IN_POST_STATE_LEMMA THEN
ITAC SCRATCHPAD_ADDRESSES_EQ_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA THEN
ITAC SCRATCHPAD_ADDRESSES_EQ_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA THEN
IRTAC UPDATING_BD_L2_IMPLIES_CHANNELS_UPDATE_BD_Q_TRANSITIONS_BD_RAS_WAS_LEMMA THEN
ITAC CHANNELS_UPDATE_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA THEN
ITAC CHANNELS_UPDATE_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA THEN
ITAC CHANNELS_UPDATE_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA THEN
ITAC CHANNELS_UPDATE_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA THEN
STAC
QED

val _ = export_theory();
