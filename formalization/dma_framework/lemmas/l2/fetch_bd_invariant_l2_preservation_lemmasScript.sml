open HolKernel Parse boolLib bossLib helper_tactics;
open invariant_l2Theory invariant_l2_lemmasTheory;

val _ = new_theory "fetch_bd_invariant_l2_preservation_lemmas";

Definition CHANNELS_FETCH_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE:
           CHANNELS_FETCH_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
(device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
(device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) =
  !channel_id q1 q2.
    VALID_CHANNEL_ID device_characteristics channel_id /\
    q1 = (schannel device1 channel_id).queue /\
    q2 = (schannel device2 channel_id).queue
    ==>
    BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE q1.bds_to_fetch q2.bds_to_fetch q1.bds_to_update     q2.bds_to_update /\
    BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE q1.bds_to_fetch q2.bds_to_fetch q1.bds_to_process    q2.bds_to_process /\
    BD_Q_PRESERVED                                                           q1.bds_to_write_back q2.bds_to_write_back
End

Theorem CHANNELS_FETCH_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA:
!device_characteristics device1 device2 memory.
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2 /\
  CHANNELS_FETCH_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE device_characteristics device1 device2 /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_FETCH_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_FETCH_BD_L2 THEN
INTRO_TAC THEN
PTAC CHANNELS_FETCH_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE THEN
AITAC THEN
IRTAC BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_IMPLIES_PRE_MEMBER_LEMMA THEN
AITAC THEN
IRTAC BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_PRESERVES_BD_DATA_LEMMA THEN
STAC
QED

Theorem INVARIANT_FETCH_BD_L2_IMPLIES_MEMBER_BDS_TO_FETCH_BD_WRITE_DATA_LEMMA:
!device_characteristics channel_id memory device bd bd_ras bd_was update_flag ras_was EXTERNAL_MEMORY_BDS R W.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory device /\
  MEM ((bd, bd_ras, bd_was), update_flag) (schannel device channel_id).queue.bds_to_fetch /\
  ras_was = (cverification device_characteristics channel_id).bd_transfer_ras_was device.dma_state.internal_state bd /\
  EXTERNAL_MEMORY_BDS = EXTERNAL_BDS device_characteristics /\
  W = device_characteristics.dma_characteristics.W memory /\
  R = device_characteristics.dma_characteristics.R memory
  ==>
  BD_WRITE W EXTERNAL_MEMORY_BDS bd_was /\
  BD_DATA R W ras_was
Proof
INTRO_TAC THEN
PTAC INVARIANT_FETCH_BD_L2 THEN
AITAC THEN
STAC
QED

Theorem INVARIANT_FETCH_BD_L2_AND_BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_IMPLIES_MEMBER_BDS_TO_FETCH_BD_WRITE_DATA_LEMMA:
!device_characteristics channel_id memory device1 device2 bd bd_ras bd_was update_flag ras_was EXTERNAL_MEMORY_BDS R W.
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2 /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory device1 /\
  MEM ((bd, bd_ras, bd_was), update_flag) (schannel device1 channel_id).queue.bds_to_fetch /\
  ras_was = (cverification device_characteristics channel_id).bd_transfer_ras_was device2.dma_state.internal_state bd /\
  EXTERNAL_MEMORY_BDS = EXTERNAL_BDS device_characteristics /\
  W = device_characteristics.dma_characteristics.W memory /\
  R = device_characteristics.dma_characteristics.R memory
  ==>
  BD_WRITE W EXTERNAL_MEMORY_BDS bd_was /\
  BD_DATA R W ras_was
Proof
INTRO_TAC THEN
ITAC INVARIANT_FETCH_BD_L2_IMPLIES_MEMBER_BDS_TO_FETCH_BD_WRITE_DATA_LEMMA THEN
ITAC BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_PRESERVES_BD_DATA_LEMMA THEN
STAC
QED

Theorem CHANNELS_FETCH_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA:
!device_characteristics device1 device2 memory.
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2 /\
  CHANNELS_FETCH_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE device_characteristics device1 device2 /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory device1 /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_UPDATE_BD_L2 THEN
INTRO_TAC THEN
PTAC CHANNELS_FETCH_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE THEN
AITAC THEN
IRTAC BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_IMPLIES_POST_MEMBER_PRE_MEMBER_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AITAC THEN
 IRTAC BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_PRESERVES_BD_DATA_LEMMA THEN
 STAC
 ,
 AXTAC THEN
 IRTAC INVARIANT_FETCH_BD_L2_AND_BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_IMPLIES_MEMBER_BDS_TO_FETCH_BD_WRITE_DATA_LEMMA THEN
 STAC
]
QED

Theorem CHANNELS_FETCH_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA:
!device_characteristics device1 device2 memory.
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2 /\
  CHANNELS_FETCH_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE device_characteristics device1 device2 /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory device1 /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device1
  ==>
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_TRANSFER_DATA_L2 THEN
INTRO_TAC THEN
PTAC CHANNELS_FETCH_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE THEN
AITAC THEN
FIRTAC BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_IMPLIES_POST_MEMBER_PRE_MEMBER_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AITAC THEN
 IRTAC BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_PRESERVES_BD_DATA_LEMMA THEN
 STAC
 ,
 AXTAC THEN
 IRTAC INVARIANT_FETCH_BD_L2_AND_BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_IMPLIES_MEMBER_BDS_TO_FETCH_BD_WRITE_DATA_LEMMA THEN
 STAC
]
QED

Theorem CHANNELS_FETCH_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA:
!device_characteristics device1 device2 memory.
  CHANNELS_FETCH_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE device_characteristics device1 device2 /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_WRITE_BACK_BD_L2 THEN
INTRO_TAC THEN
PTAC CHANNELS_FETCH_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE THEN
AITAC THEN
FIRTAC BD_Q_PRESERVED_IMPLIES_POST_MEMBER_PRE_LEMMA THEN
AIRTAC THEN
STAC
QED






























Theorem FETCHING_BD_CLEAR_REPLY_PRESERVES_BD_QS_LEMMA:
!channel1 channel2.
  channel2 = fetching_bd_clear_reply channel1
  ==>
  BD_Q_PRESERVED channel1.queue.bds_to_fetch      channel2.queue.bds_to_fetch /\
  BD_Q_PRESERVED channel1.queue.bds_to_update     channel2.queue.bds_to_update /\
  BD_Q_PRESERVED channel1.queue.bds_to_process    channel2.queue.bds_to_process /\
  BD_Q_PRESERVED channel1.queue.bds_to_write_back channel2.queue.bds_to_write_back
Proof
INTRO_TAC THEN
ETAC BD_Q_PRESERVED THEN
PTAC operationsTheory.fetching_bd_clear_reply THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem FETCHING_BD_UPDATE_QS_ABSTRACT_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLCE_BDS_TO_UPDATE_LEMMA:
!channel1 channel2.
  channel2 = fetching_bd_update_qs_abstract channel1 channel1.queue.bds_to_fetch
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE channel1.queue.bds_to_fetch  channel2.queue.bds_to_fetch
                                           channel1.queue.bds_to_update channel2.queue.bds_to_update
Proof
INTRO_TAC THEN
PTAC abstractTheory.fetching_bd_update_qs_abstract THENL
[
 ASM_REWRITE_TAC [BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_SAME_QS_LEMMA]
 ,
 PTAC operationsTheory.update_channel_qs THEN
 PTAC operationsTheory.update_qs THEN
 PTAC listTheory.FOLDL THEN
 PTAC operationsTheory.update_q THEN
 PTAC listTheory.FOLDL THEN
 PTAC operationsTheory.update_q THEN
 PTAC listTheory.FOLDL THEN
 LRTAC THEN
 PTAC BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
 PTAC BD_Q_TRANSITION_BD_RAS_WAS_UPDATE_CYCLE THEN
 PTAC BD_Q_TRANSITION THEN
 ALL_LRTAC THEN
 RECORD_TAC THEN
 PTAC invariant_l2_lemmasTheory.bd_ras_was_update_cycle2bd_ras_was THEN
 STAC
 ,
 PTAC operationsTheory.update_channel_qs THEN
 PTAC operationsTheory.update_qs THEN
 PTAC listTheory.FOLDL THEN
 PTAC operationsTheory.update_q THEN
 PTAC listTheory.FOLDL THEN
 PTAC operationsTheory.update_q THEN
 PTAC listTheory.FOLDL THEN
 LRTAC THEN
 RECORD_TAC THEN
 ALL_LRTAC THEN
 PTAC BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
 PTAC BD_Q_CYCLIC_REMOVAL_PRESERVED THEN
 PTAC BD_Q_CYCLIC_REMOVAL THEN
 REWRITE_TAC [BD_Q_PRESERVED] THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
 PTAC BD_Q_REMOVAL THEN
 STAC
]
QED

Theorem FETCHING_BD_UPDATE_QS_ABSTRACT_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLCE_BDS_TO_PROCESS_LEMMA:
!channel1 channel2.
  channel2 = fetching_bd_update_qs_abstract channel1 channel1.queue.bds_to_fetch
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE channel1.queue.bds_to_fetch   channel2.queue.bds_to_fetch
                                           channel1.queue.bds_to_process channel2.queue.bds_to_process
Proof
INTRO_TAC THEN
PTAC abstractTheory.fetching_bd_update_qs_abstract THENL
[
 ASM_REWRITE_TAC [BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_SAME_QS_LEMMA]
 ,
 PTAC operationsTheory.update_channel_qs THEN
 PTAC operationsTheory.update_qs THEN
 PTAC listTheory.FOLDL THEN
 PTAC operationsTheory.update_q THEN
 PTAC listTheory.FOLDL THEN
 PTAC operationsTheory.update_q THEN
 PTAC listTheory.FOLDL THEN
 LRTAC THEN
 RECORD_TAC THEN
 ALL_LRTAC THEN
 PTAC BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
 PTAC BD_Q_CYCLIC_REMOVAL_PRESERVED THEN
 REWRITE_TAC [BD_Q_PRESERVED] THEN
 PTAC BD_Q_CYCLIC_REMOVAL THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
 PTAC BD_Q_REMOVAL THEN
 STAC
 ,
 PTAC operationsTheory.update_channel_qs THEN
 PTAC operationsTheory.update_qs THEN
 PTAC listTheory.FOLDL THEN
 PTAC operationsTheory.update_q THEN
 PTAC listTheory.FOLDL THEN
 PTAC operationsTheory.update_q THEN
 PTAC listTheory.FOLDL THEN
 LRTAC THEN
 RECORD_TAC THEN
 ALL_LRTAC THEN
 PTAC BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
 PTAC BD_Q_TRANSITION_BD_RAS_WAS_UPDATE_CYCLE THEN
 PTAC BD_Q_TRANSITION THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
 PTAC bd_ras_was_update_cycle2bd_ras_was THEN
 STAC
]
QED

Theorem FETCHING_BD_UPDATE_QS_ABSTRACT_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA:
!channel1 channel2.
  channel2 = fetching_bd_update_qs_abstract channel1 channel1.queue.bds_to_fetch
  ==>
  BD_Q_PRESERVED channel1.queue.bds_to_write_back channel2.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC abstractTheory.fetching_bd_update_qs_abstract THEN ASM_REWRITE_TAC [BD_Q_PRESERVED] THEN
 ETAC operationsTheory.update_channel_qs THEN
 ETAC operationsTheory.update_qs THEN
 ETAC listTheory.FOLDL THEN
 ETAC operationsTheory.update_q THEN
 RECORD_TAC THEN
 STAC
QED



Theorem FETCHING_BD_FETCH_BD_ABSTRACT_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_UPDATE_LEMMA:
!operation_fetch_bd internal_state1 internal_state2 reply channel1 channel2.
  (internal_state2, channel2) = fetching_bd_fetch_bd_abstract operation_fetch_bd internal_state1 channel1 reply
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE channel1.queue.bds_to_fetch  channel2.queue.bds_to_fetch
                                           channel1.queue.bds_to_update channel2.queue.bds_to_update
Proof
INTRO_TAC THEN
PTAC abstractTheory.fetching_bd_fetch_bd_abstract THENL
[
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 IRTAC FETCHING_BD_UPDATE_QS_ABSTRACT_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLCE_BDS_TO_UPDATE_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ASM_REWRITE_TAC [BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_SAME_QS_LEMMA]
]
QED

Theorem FETCHING_BD_FETCH_BD_ABSTRACT_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_PROCESS_LEMMA:
!operation_fetch_bd internal_state1 internal_state2 reply channel1 channel2.
  (internal_state2, channel2) = fetching_bd_fetch_bd_abstract operation_fetch_bd internal_state1 channel1 reply
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE channel1.queue.bds_to_fetch  channel2.queue.bds_to_fetch
                                           channel1.queue.bds_to_process channel2.queue.bds_to_process
Proof
INTRO_TAC THEN
PTAC abstractTheory.fetching_bd_fetch_bd_abstract THENL
[
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 IRTAC FETCHING_BD_UPDATE_QS_ABSTRACT_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLCE_BDS_TO_PROCESS_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ASM_REWRITE_TAC [BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_SAME_QS_LEMMA]
]
QED

Theorem FETCHING_BD_FETCH_BD_ABSTRACT_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA:
!operation_fetch_bd internal_state1 internal_state2 reply channel1 channel2.
  (internal_state2, channel2) = fetching_bd_fetch_bd_abstract operation_fetch_bd internal_state1 channel1 reply
  ==>
  BD_Q_PRESERVED channel1.queue.bds_to_write_back channel2.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC abstractTheory.fetching_bd_fetch_bd_abstract THENL
[
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 IRTAC FETCHING_BD_UPDATE_QS_ABSTRACT_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ASM_REWRITE_TAC [BD_Q_PRESERVED]
]
QED









Theorem FETCHING_BD_CLEAR_REPLY_FETCHING_BD_FETCH_BD_ABSTRACT_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_UPDATE_LEMMA:
!channel1 channel2 channel3 internal_state1 internal_state2 reply operation_fetch_bd.
  channel2 = fetching_bd_clear_reply channel1 /\
  (internal_state2, channel3) = fetching_bd_fetch_bd_abstract operation_fetch_bd internal_state1 channel2 reply
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE channel1.queue.bds_to_fetch  channel3.queue.bds_to_fetch
                                           channel1.queue.bds_to_update channel3.queue.bds_to_update
Proof
INTRO_TAC THEN
IRTAC FETCHING_BD_CLEAR_REPLY_PRESERVES_BD_QS_LEMMA THEN
IRTAC FETCHING_BD_FETCH_BD_ABSTRACT_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_UPDATE_LEMMA THEN
IRTAC BD_QS_PRESERVED_PRESERVES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_LEMMA THEN
STAC
QED

Theorem FETCHING_BD_CLEAR_REPLY_FETCHING_BD_FETCH_BD_ABSTRACT_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_PROCESS_LEMMA:
!channel1 channel2 channel3 internal_state1 internal_state2 reply operation_fetch_bd.
  channel2 = fetching_bd_clear_reply channel1 /\
  (internal_state2, channel3) = fetching_bd_fetch_bd_abstract operation_fetch_bd internal_state1 channel2 reply
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE channel1.queue.bds_to_fetch   channel3.queue.bds_to_fetch
                                           channel1.queue.bds_to_process channel3.queue.bds_to_process
Proof
INTRO_TAC THEN
IRTAC FETCHING_BD_CLEAR_REPLY_PRESERVES_BD_QS_LEMMA THEN
IRTAC FETCHING_BD_FETCH_BD_ABSTRACT_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_PROCESS_LEMMA THEN
FIRTAC BD_QS_PRESERVED_PRESERVES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_LEMMA THEN
STAC
QED

Theorem FETCHING_BD_CLEAR_REPLY_FETCHING_BD_FETCH_BD_ABSTRACT_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA:
!channel1 channel2 channel3 internal_state1 internal_state2 reply operation_fetch_bd.
  channel2 = fetching_bd_clear_reply channel1 /\
  (internal_state2, channel3) = fetching_bd_fetch_bd_abstract operation_fetch_bd internal_state1 channel2 reply
  ==>
  BD_Q_PRESERVED channel1.queue.bds_to_write_back channel3.queue.bds_to_write_back
Proof
INTRO_TAC THEN
IRTAC FETCHING_BD_CLEAR_REPLY_PRESERVES_BD_QS_LEMMA THEN
IRTAC FETCHING_BD_FETCH_BD_ABSTRACT_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN
ETAC BD_Q_PRESERVED THEN
STAC
QED




Theorem UPDATE_DEVICE_PRESERVES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_UPDATE_LEMMA:
!q1 q2 device1 device2 channel1 channel2 channel_id channel_id' internal_state1.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  channel1 = schannel device1 channel_id /\
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE channel1.queue.bds_to_fetch  channel2.queue.bds_to_fetch
                                           channel1.queue.bds_to_update channel2.queue.bds_to_update /\
  device2 = update_device_state device1 channel_id internal_state1 channel2
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE q1.bds_to_fetch q2.bds_to_fetch q1.bds_to_update q2.bds_to_update
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
 REWRITE_TAC [BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_SAME_QS_LEMMA]
]
QED

Theorem UPDATE_DEVICE_PRESERVES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_PROCESS_LEMMA:
!q1 q2 device1 device2 channel1 channel2 channel_id channel_id' internal_state1.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  channel1 = schannel device1 channel_id /\
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE channel1.queue.bds_to_fetch   channel2.queue.bds_to_fetch
                                           channel1.queue.bds_to_process channel2.queue.bds_to_process /\
  device2 = update_device_state device1 channel_id internal_state1 channel2
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE q1.bds_to_fetch q2.bds_to_fetch q1.bds_to_process q2.bds_to_process
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
 REWRITE_TAC [BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_SAME_QS_LEMMA]
]
QED

Theorem UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA:
!q1 q2 device1 device2 channel1 channel2 channel_id channel_id' internal_state1.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  channel1 = schannel device1 channel_id /\
  BD_Q_PRESERVED channel1.queue.bds_to_write_back channel2.queue.bds_to_write_back /\
  device2 = update_device_state device1 channel_id internal_state1 channel2
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



Theorem FETCHING_BD_CLEAR_REPLY_FETCHING_BD_FETCH_BD_ABSTRACT_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_UPDATE_LEMMA:
!q1 q2 device1 device2 channel_id' channel_id channel1 channel2 channel3 internal_state1 internal_state2 reply operation_fetch_bd.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  channel2 = fetching_bd_clear_reply channel1 /\
  (internal_state2, channel3) = fetching_bd_fetch_bd_abstract operation_fetch_bd internal_state1 channel2 reply /\
  device2 = update_device_state device1 channel_id internal_state2 channel3
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE q1.bds_to_fetch q2.bds_to_fetch q1.bds_to_update q2.bds_to_update
Proof
INTRO_TAC THEN
IRTAC FETCHING_BD_CLEAR_REPLY_FETCHING_BD_FETCH_BD_ABSTRACT_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_UPDATE_LEMMA THEN
FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_UPDATE_LEMMA THEN
STAC
QED

Theorem FETCHING_BD_CLEAR_REPLY_FETCHING_BD_FETCH_BD_ABSTRACT_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_PROCESS_LEMMA:
!q1 q2 device1 device2 channel_id' channel_id channel1 channel2 channel3 internal_state1 internal_state2 reply operation_fetch_bd.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  channel2 = fetching_bd_clear_reply channel1 /\
  (internal_state2, channel3) = fetching_bd_fetch_bd_abstract operation_fetch_bd internal_state1 channel2 reply /\
  device2 = update_device_state device1 channel_id internal_state2 channel3
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE q1.bds_to_fetch q2.bds_to_fetch q1.bds_to_process q2.bds_to_process
Proof
INTRO_TAC THEN
IRTAC FETCHING_BD_CLEAR_REPLY_FETCHING_BD_FETCH_BD_ABSTRACT_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_PROCESS_LEMMA THEN
FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_PROCESS_LEMMA THEN
STAC
QED

Theorem FETCHING_BD_CLEAR_REPLY_FETCHING_BD_FETCH_BD_ABSTRACT_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA:
!q1 q2 device1 device2 channel_id' channel_id channel1 channel2 channel3 internal_state1 internal_state2 reply operation_fetch_bd.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  channel2 = fetching_bd_clear_reply channel1 /\
  (internal_state2, channel3) = fetching_bd_fetch_bd_abstract operation_fetch_bd internal_state1 channel2 reply /\
  device2 = update_device_state device1 channel_id internal_state2 channel3
  ==>
  BD_Q_PRESERVED q1.bds_to_write_back q2.bds_to_write_back
Proof
INTRO_TAC THEN
IRTAC FETCHING_BD_CLEAR_REPLY_FETCHING_BD_FETCH_BD_ABSTRACT_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN
FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN
STAC
QED



Theorem FETCHING_BD_SET_REQUEST_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_UPDATE_LEMMA:
!channel1 channel2 fetch_bd_read_addresses tag.
  channel2 = fetching_bd_set_request channel1 fetch_bd_read_addresses tag
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE channel1.queue.bds_to_fetch  channel2.queue.bds_to_fetch
                                           channel1.queue.bds_to_update channel2.queue.bds_to_update
Proof
INTRO_TAC THEN
PTAC operationsTheory.fetching_bd_set_request THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_SAME_QS_LEMMA]
QED

Theorem FETCHING_BD_SET_REQUEST_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_PROCESS_LEMMA:
!channel1 channel2 fetch_bd_read_addresses tag.
  channel2 = fetching_bd_set_request channel1 fetch_bd_read_addresses tag
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE channel1.queue.bds_to_fetch   channel2.queue.bds_to_fetch
                                           channel1.queue.bds_to_process channel2.queue.bds_to_process
Proof
INTRO_TAC THEN
PTAC operationsTheory.fetching_bd_set_request THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_SAME_QS_LEMMA]
QED

Theorem FETCHING_BD_SET_REQUEST_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA:
!channel1 channel2 fetch_bd_read_addresses tag.
  channel2 = fetching_bd_set_request channel1 fetch_bd_read_addresses tag
  ==>
  BD_Q_PRESERVED channel1.queue.bds_to_write_back channel2.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC operationsTheory.fetching_bd_set_request THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [BD_Q_PRESERVED]
QED



Theorem FETCHING_BD_SET_REQUEST_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_UPDATE_LEMMA:
!q1 q2 device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id channel_id' fetch_bd_read_addresses tag.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = (internal_state1, fetching_bd_set_request channel1 fetch_bd_read_addresses tag) /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE q1.bds_to_fetch q2.bds_to_fetch q1.bds_to_update q2.bds_to_update
Proof
INTRO_TAC THEN
EQ_PAIR_ASM_TAC THEN
IRTAC FETCHING_BD_SET_REQUEST_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_UPDATE_LEMMA THEN
FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_UPDATE_LEMMA THEN
STAC
QED

Theorem FETCHING_BD_SET_REQUEST_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_PROCESS_LEMMA:
!q1 q2 device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id channel_id' fetch_bd_read_addresses tag.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = (internal_state1, fetching_bd_set_request channel1 fetch_bd_read_addresses tag) /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE q1.bds_to_fetch q2.bds_to_fetch q1.bds_to_process q2.bds_to_process
Proof
INTRO_TAC THEN
EQ_PAIR_ASM_TAC THEN
IRTAC FETCHING_BD_SET_REQUEST_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_PROCESS_LEMMA THEN
FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_PROCESS_LEMMA THEN
STAC
QED

Theorem FETCHING_BD_SET_REQUEST_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA:
!q1 q2 device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id channel_id' fetch_bd_read_addresses tag.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = (internal_state1, fetching_bd_set_request channel1 fetch_bd_read_addresses tag) /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_Q_PRESERVED q1.bds_to_write_back q2.bds_to_write_back
Proof
INTRO_TAC THEN
EQ_PAIR_ASM_TAC THEN
IRTAC FETCHING_BD_SET_REQUEST_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN
FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN
STAC
QED



Theorem FETCHING_BD_FETCHING_BD_ABSTRACT_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_UPDATE_LEMMA:
!q1 q2 device1 device2 channel_id' internal_state1 internal_state2 channel1 channel2 reply channel_id operation.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = fetching_bd_fetch_bd_abstract operation.fetch_bd internal_state1 channel1 reply /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE q1.bds_to_fetch q2.bds_to_fetch q1.bds_to_update q2.bds_to_update
Proof
INTRO_TAC THEN
IRTAC FETCHING_BD_FETCH_BD_ABSTRACT_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_UPDATE_LEMMA THEN
FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_UPDATE_LEMMA THEN
STAC
QED

Theorem FETCHING_BD_FETCHING_BD_ABSTRACT_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_PROCESS_LEMMA:
!q1 q2 device1 device2 channel_id' internal_state1 internal_state2 channel1 channel2 reply channel_id operation.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = fetching_bd_fetch_bd_abstract operation.fetch_bd internal_state1 channel1 reply /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE q1.bds_to_fetch q2.bds_to_fetch q1.bds_to_process q2.bds_to_process
Proof
INTRO_TAC THEN
IRTAC FETCHING_BD_FETCH_BD_ABSTRACT_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_PROCESS_LEMMA THEN
FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_PROCESS_LEMMA THEN
STAC
QED

Theorem FETCHING_BD_FETCHING_BD_ABSTRACT_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA:
!q1 q2 device1 device2 channel_id' internal_state1 internal_state2 channel1 channel2 reply channel_id operation.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = fetching_bd_fetch_bd_abstract operation.fetch_bd internal_state1 channel1 reply /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_Q_PRESERVED q1.bds_to_write_back q2.bds_to_write_back
Proof
INTRO_TAC THEN
IRTAC FETCHING_BD_FETCH_BD_ABSTRACT_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN
FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN
STAC
QED



Theorem FETCHING_BD_L2_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_FETCH_BDS_TO_UPDATE_LEMMA:
!device_characteristics device1 device2 internal_state1 internal_state2 channel1
 channel2 channel_id channel_id' q1 q2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = (schannel device1 channel_id) /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = fetching_bd_l2 device_characteristics channel_id internal_state1 channel1 /\
  VALID_CHANNEL_ID device_characteristics channel_id' /\
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE q1.bds_to_fetch q2.bds_to_fetch q1.bds_to_update q2.bds_to_update
Proof
INTRO_TAC THEN
PTAC l2Theory.fetching_bd_l2 THENL
[
 FIRTAC FETCHING_BD_FETCHING_BD_ABSTRACT_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_UPDATE_LEMMA THEN STAC
 ,
 FIRTAC FETCHING_BD_SET_REQUEST_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_UPDATE_LEMMA THEN STAC
 ,
 FIRTAC FETCHING_BD_CLEAR_REPLY_FETCHING_BD_FETCH_BD_ABSTRACT_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_UPDATE_LEMMA THEN STAC
]
QED

Theorem FETCHING_BD_L2_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_FETCH_BDS_TO_PROCESS_LEMMA:
!device_characteristics device1 device2 internal_state1 internal_state2 channel1
 channel2 channel_id channel_id' q1 q2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = (schannel device1 channel_id) /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = fetching_bd_l2 device_characteristics channel_id internal_state1 channel1 /\
  VALID_CHANNEL_ID device_characteristics channel_id' /\
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue
  ==>
  BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE q1.bds_to_fetch q2.bds_to_fetch q1.bds_to_process q2.bds_to_process
Proof
INTRO_TAC THEN
PTAC l2Theory.fetching_bd_l2 THENL
[
 FIRTAC FETCHING_BD_FETCHING_BD_ABSTRACT_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_PROCESS_LEMMA THEN STAC
 ,
 FIRTAC FETCHING_BD_SET_REQUEST_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_PROCESS_LEMMA THEN STAC
 ,
 FIRTAC FETCHING_BD_CLEAR_REPLY_FETCHING_BD_FETCH_BD_ABSTRACT_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_PROCESS_LEMMA THEN STAC
]
QED

Theorem FETCHING_BD_L2_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA:
!device_characteristics device1 device2 internal_state1 internal_state2 channel1
 channel2 channel_id channel_id' q1 q2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = (schannel device1 channel_id) /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = fetching_bd_l2 device_characteristics channel_id internal_state1 channel1 /\
  VALID_CHANNEL_ID device_characteristics channel_id' /\
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue
  ==>
  BD_Q_PRESERVED q1.bds_to_write_back q2.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC l2Theory.fetching_bd_l2 THENL
[
 FIRTAC FETCHING_BD_FETCHING_BD_ABSTRACT_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN STAC
 ,
 FIRTAC FETCHING_BD_SET_REQUEST_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN STAC
 ,
 FIRTAC FETCHING_BD_CLEAR_REPLY_FETCHING_BD_FETCH_BD_ABSTRACT_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN STAC
]
QED

Theorem FETCHING_BD_L2_IMPLIES_CHANNELS_FETCH_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_LEMMA:
!device_characteristics device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = (schannel device1 channel_id) /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = fetching_bd_l2 device_characteristics channel_id internal_state1 channel1
  ==>
  CHANNELS_FETCH_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE device_characteristics device1 device2
Proof
INTRO_TAC THEN
PTAC CHANNELS_FETCH_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE THEN
INTRO_TAC THEN
REPEAT CONJ_TAC THENL
[
 FIRTAC FETCHING_BD_L2_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_FETCH_BDS_TO_UPDATE_LEMMA THEN STAC
 ,
 FIRTAC FETCHING_BD_L2_IMPLIES_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_BDS_TO_FETCH_BDS_TO_PROCESS_LEMMA THEN STAC 
 ,
 FIRTAC FETCHING_BD_L2_IMPLIES_BD_Q_PRESERVED_BDS_TO_WRITE_BACK_LEMMA THEN STAC
]
QED





Theorem FETCHING_BD_L2_IMPLIES_SCRATCHPAD_ADDRESSES_EQ_LEMMA:
!device_characteristics channel_id device1 device2 internal_state1 internal_state2 channel1 channel2.
  PROOF_OBLIGATION_FETCH_BD_PRESERVES_SCRATCHPAD device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = fetching_bd_l2 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  SCRATCHPAD_ADDRESSES_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
ETAC stateTheory.SCRATCHPAD_ADDRESSES_EQ THEN
PTAC l2Theory.fetching_bd_l2 THENL
[
 PTAC abstractTheory.fetching_bd_fetch_bd_abstract THEN
  EQ_PAIR_ASM_TAC THEN
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCH_BD_PRESERVES_SCRATCHPAD THEN
  AIRTAC THEN
  RLTAC THEN
  PTAC operationsTheory.update_device_state THEN
  LRTAC THEN
  RECORD_TAC THEN
  STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCH_BD_PRESERVES_SCRATCHPAD THEN
 AIRTAC THEN
 RLTAC THEN
 PTAC operationsTheory.update_device_state THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 PTAC abstractTheory.fetching_bd_fetch_bd_abstract THEN
  EQ_PAIR_ASM_TAC THEN
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCH_BD_PRESERVES_SCRATCHPAD THEN
  AIRTAC THEN
  RLTAC THEN
  PTAC operationsTheory.update_device_state THEN
  LRTAC THEN
  RECORD_TAC THEN
  STAC
]
QED

Theorem FETCHING_BD_L2_IMPLIES_BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_LEMMA:
!device_characteristics channel_id device1 device2 internal_state1 internal_state2 channel1 channel2.
  PROOF_OBLIGATION_FETCHING_BD_PRESERVES_BD_INTERPRETATION device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = fetching_bd_l2 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2
Proof
INTRO_TAC THEN
ETAC BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ THEN
INTRO_TAC THEN
REWRITE_TAC [boolTheory.FUN_EQ_THM] THEN
GEN_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHING_BD_PRESERVES_BD_INTERPRETATION THEN
PTAC l2Theory.fetching_bd_l2 THENL
[
 PTAC abstractTheory.fetching_bd_fetch_bd_abstract THEN
  EQ_PAIR_ASM_TAC THEN
  RLTAC THEN
  AIRTAC THEN
  AIRTAC THEN
  PTAC operationsTheory.update_device_state THEN
  LRTAC THEN
  RLTAC THEN
  RECORD_TAC THEN
  STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ALL_LRTAC THEN
 ETAC stateTheory.schannel THEN
 PTAC operationsTheory.update_device_state THEN
 RECORD_TAC THEN
 STAC
 ,
 PTAC abstractTheory.fetching_bd_fetch_bd_abstract THEN
  EQ_PAIR_ASM_TAC THEN
  AIRTAC THEN
  AIRTAC THEN
  RLTAC THEN
  PTAC operationsTheory.update_device_state THEN
  LRTAC THEN
  RECORD_TAC THEN
  STAC
]
QED

Theorem FETCHING_BD_L2_PRESERVES_FETCH_UPDATE_PROCESS_WRITE_BACK_SCRATCHPAD_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_FETCH_BD_PRESERVES_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_FETCHING_BD_PRESERVES_BD_INTERPRETATION device_characteristics /\

  INVARIANT_FETCH_BD_L2 device_characteristics memory device1 /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device1 /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device1 /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device1 /\
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device1 /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device1 /\

  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = (schannel device1 channel_id) /\
  (internal_state2, channel2) = fetching_bd_l2 device_characteristics channel_id internal_state1 channel1 /\
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
ITAC FETCHING_BD_L2_IMPLIES_SCRATCHPAD_ADDRESSES_EQ_LEMMA THEN
ITAC FETCHING_BD_L2_IMPLIES_BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_LEMMA THEN
ITAC SCRATCHPAD_ADDRESSES_EQ_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA THEN
ITAC SCRATCHPAD_ADDRESSES_EQ_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA THEN
IRTAC FETCHING_BD_L2_IMPLIES_CHANNELS_FETCH_BD_Q_TRANSITIONS_BD_RAS_WAS_UPDATE_CYCLE_LEMMA THEN
ITAC CHANNELS_FETCH_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA THEN
ITAC CHANNELS_FETCH_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA THEN
ITAC CHANNELS_FETCH_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA THEN
ITAC CHANNELS_FETCH_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA THEN
STAC
QED

val _ = export_theory();

