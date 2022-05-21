open HolKernel Parse boolLib bossLib helper_tactics;
open invariant_l2Theory invariant_l2_lemmasTheory;

val _ = new_theory "write_back_bd_invariant_l2_preservation_lemmas";

Definition BD_Q_RELEASED:
BD_Q_RELEASED q1 q2 =
  !bd_ras_was. MEM bd_ras_was q2 ==> MEM bd_ras_was q1
End

Theorem BD_Q_RELEASED_REFL_LEMMA:
!q. BD_Q_RELEASED q q
Proof
GEN_TAC THEN
PTAC BD_Q_RELEASED THEN
INTRO_TAC THEN
STAC
QED

Theorem BD_Q_RELEASED_TRANSITIVITY_LEMMA:
!q1 q q2.
  BD_Q_RELEASED q1 q /\
  BD_Q_RELEASED q q2
  ==>
  BD_Q_RELEASED q1 q2
Proof
REWRITE_TAC [BD_Q_RELEASED] THEN
INTRO_TAC THEN
INTRO_TAC THEN
FAIRTAC THEN
AIRTAC THEN
STAC
QED

Theorem UPDATE_DEVICE_PRESERVES_BD_Q_RELEASED_LEMMA:
!q1 q2 device1 device2 channel1 channel2 channel_id' channel_id internal_state.
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue /\
  channel1 = schannel device1 channel_id /\
  device2 = update_device_state device1 channel_id internal_state channel2 /\
  BD_Q_RELEASED channel1.queue.bds_to_write_back channel2.queue.bds_to_write_back
  ==>
  BD_Q_RELEASED q1.bds_to_write_back q2.bds_to_write_back
Proof
INTRO_TAC THEN
ETAC BD_Q_RELEASED THEN
INTRO_TAC THEN
PTAC operationsTheory.update_device_state THEN
LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 RLTAC THEN
 ETAC optionTheory.THE_DEF THEN
 RLTAC THEN
 AIRTAC THEN
 RLTAC THEN
 RLTAC THEN
 STAC
 ,
 RLTAC THEN
 RLTAC THEN
 STAC
]
QED

Theorem ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_RELEASED_LEMMA:
!q1 q2 device1 device2 channel_id' channel_id channel internal_state.
  channel = (schannel device1 channel_id) /\
  device2 = update_device_state device1 channel_id internal_state channel /\
  q1 = (schannel device1 channel_id').queue /\
  q2 = (schannel device2 channel_id').queue
  ==>
  BD_Q_RELEASED q1.bds_to_write_back q2.bds_to_write_back
Proof
INTRO_TAC THEN
ETAC BD_Q_RELEASED THEN
INTRO_TAC THEN
ETAC stateTheory.schannel THEN
ALL_LRTAC THEN
ETAC operationsTheory.update_device_state THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 RLTAC THEN
 ETAC optionTheory.THE_DEF THEN
 STAC
 ,
 STAC
]
QED

Theorem BD_Q_RELEASED_IMPLIES_PRE_MEMBER_LEMMA:
!q1 q2 bd.
  BD_Q_RELEASED q1 q2 /\
  MEM bd q2
  ==>
  MEM bd q1
Proof
INTRO_TAC THEN
PTAC BD_Q_RELEASED THEN
AIRTAC THEN
STAC
QED










Definition CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_BD_RAS_WAS:
           CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_BD_RAS_WAS
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
(device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
(device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) =
  !channel_id q1 q2.
    VALID_CHANNEL_ID device_characteristics channel_id /\
    q1 = (schannel device1 channel_id).queue /\
    q2 = (schannel device2 channel_id).queue
    ==>
    BD_Q_PRESERVED q1.bds_to_fetch      q2.bds_to_fetch /\
    BD_Q_PRESERVED q1.bds_to_update     q2.bds_to_update /\
    BD_Q_PRESERVED q1.bds_to_process    q2.bds_to_process /\
    BD_Q_RELEASED  q1.bds_to_write_back q2.bds_to_write_back
End

Theorem CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA:
!device_characteristics device1 device2 memory.
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2 /\
  CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_BD_RAS_WAS device_characteristics device1 device2 /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_FETCH_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_FETCH_BD_L2 THEN
INTRO_TAC THEN
PTAC CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_BD_RAS_WAS THEN
AITAC THEN
ITAC BD_Q_PRESERVED_IMPLIES_POST_MEMBER_PRE_LEMMA THEN
AITAC THEN
IRTAC BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_PRESERVES_BD_DATA_LEMMA THEN
STAC
QED

Theorem CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA:
!device_characteristics device1 device2 memory.
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2 /\
  CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_BD_RAS_WAS device_characteristics device1 device2 /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_UPDATE_BD_L2 THEN
INTRO_TAC THEN
PTAC CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_BD_RAS_WAS THEN
AITAC THEN
FITAC BD_Q_PRESERVED_IMPLIES_POST_MEMBER_PRE_LEMMA THEN
AITAC THEN
IRTAC BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_PRESERVES_BD_DATA_LEMMA THEN
STAC
QED

Theorem CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA:
!device_characteristics device1 device2 memory.
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2 /\
  CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_BD_RAS_WAS device_characteristics device1 device2 /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device1
  ==>
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_TRANSFER_DATA_L2 THEN
INTRO_TAC THEN
PTAC CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_BD_RAS_WAS THEN
AITAC THEN
FITAC BD_Q_PRESERVED_IMPLIES_POST_MEMBER_PRE_LEMMA THEN
AITAC THEN
IRTAC BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_PRESERVES_BD_DATA_LEMMA THEN
STAC
QED

Theorem CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA:
!device_characteristics device1 device2 memory.
  CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_BD_RAS_WAS device_characteristics device1 device2 /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device1
  ==>
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_WRITE_BACK_BD_L2 THEN
INTRO_TAC THEN
PTAC CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_BD_RAS_WAS THEN
AITAC THEN
IRTAC BD_Q_RELEASED_IMPLIES_PRE_MEMBER_LEMMA THEN
AIRTAC THEN
STAC
QED



Theorem WRITING_BACK_BD_REMOVE_RELEASED_BDS_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA:
!channel1 channel2 released_bds.
  channel2 = writing_back_bd_remove_released_bds channel1 released_bds
  ==>
  BD_Q_PRESERVED channel1.queue.bds_to_fetch channel2.queue.bds_to_fetch
Proof
INTRO_TAC THEN
PTAC operationsTheory.writing_back_bd_remove_released_bds THEN
ETAC operationsTheory.update_channel_qs THEN
ETAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [BD_Q_PRESERVED_REFL_LEMMA]
QED

Theorem WRITING_BACK_BD_REMOVE_RELEASED_BDS_IMPLIES_BD_Q_PRESERVED_BDS_TO_UPDATE_LEMMA:
!channel1 channel2 released_bds.
  channel2 = writing_back_bd_remove_released_bds channel1 released_bds
  ==>
  BD_Q_PRESERVED channel1.queue.bds_to_update channel2.queue.bds_to_update
Proof
INTRO_TAC THEN
PTAC operationsTheory.writing_back_bd_remove_released_bds THEN
ETAC operationsTheory.update_channel_qs THEN
ETAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [BD_Q_PRESERVED_REFL_LEMMA]
QED

Theorem WRITING_BACK_BD_REMOVE_RELEASED_BDS_IMPLIES_BD_Q_PRESERVED_BDS_TO_PROCESS_LEMMA:
!channel1 channel2 released_bds.
  channel2 = writing_back_bd_remove_released_bds channel1 released_bds
  ==>
  BD_Q_PRESERVED channel1.queue.bds_to_process channel2.queue.bds_to_process
Proof
INTRO_TAC THEN
PTAC operationsTheory.writing_back_bd_remove_released_bds THEN
ETAC operationsTheory.update_channel_qs THEN
ETAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [BD_Q_PRESERVED_REFL_LEMMA]
QED

Theorem WRITING_BACK_BD_APPEND_REQUEST_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA:
!channel1 channel2 write_address_bytes tag.
  channel2 = writing_back_bd_append_request channel1 write_address_bytes tag
  ==>
  BD_Q_PRESERVED channel1.queue.bds_to_fetch channel2.queue.bds_to_fetch
Proof
INTRO_TAC THEN
PTAC operationsTheory.writing_back_bd_append_request THENL
[
 ASM_REWRITE_TAC [BD_Q_PRESERVED_REFL_LEMMA]
 ,
 LRTAC THEN
 RECORD_TAC THEN
 REWRITE_TAC [BD_Q_PRESERVED_REFL_LEMMA]
]
QED

Theorem WRITING_BACK_BD_APPEND_REQUEST_IMPLIES_BD_Q_PRESERVED_BDS_TO_UPDATE_LEMMA:
!channel1 channel2 write_address_bytes tag.
  channel2 = writing_back_bd_append_request channel1 write_address_bytes tag
  ==>
  BD_Q_PRESERVED channel1.queue.bds_to_update channel2.queue.bds_to_update
Proof
INTRO_TAC THEN
PTAC operationsTheory.writing_back_bd_append_request THENL
[
 ASM_REWRITE_TAC [BD_Q_PRESERVED_REFL_LEMMA]
 ,
 LRTAC THEN
 RECORD_TAC THEN
 REWRITE_TAC [BD_Q_PRESERVED_REFL_LEMMA]
]
QED

Theorem WRITING_BACK_BD_APPEND_REQUEST_IMPLIES_BD_Q_PRESERVED_BDS_TO_PROCESS_LEMMA:
!channel1 channel2 write_address_bytes tag.
  channel2 = writing_back_bd_append_request channel1 write_address_bytes tag
  ==>
  BD_Q_PRESERVED channel1.queue.bds_to_process channel2.queue.bds_to_process
Proof
INTRO_TAC THEN
PTAC operationsTheory.writing_back_bd_append_request THENL
[
 ASM_REWRITE_TAC [BD_Q_PRESERVED_REFL_LEMMA]
 ,
 LRTAC THEN
 RECORD_TAC THEN
 REWRITE_TAC [BD_Q_PRESERVED_REFL_LEMMA]
]
QED

Theorem WRITING_BACK_BD_L2_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA:
!internal_state2 channel2 device_characteristics channel_id memory
 environment internal_state1 channel1 device1 device2 q1 q2 channel_id'.
  (internal_state2, channel2) = writing_back_bd_l2 device_characteristics channel_id memory environment internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  channel1 = schannel device1 channel_id /\
  q2 = (schannel device2 channel_id').queue /\
  q1 = (schannel device1 channel_id').queue
  ==>
  BD_Q_PRESERVED q1.bds_to_fetch q2.bds_to_fetch
Proof
INTRO_TAC THEN
PTAC l2Theory.writing_back_bd_l2 THENL
[
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 2 THEN
 IRTAC WRITING_BACK_BD_REMOVE_RELEASED_BDS_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA THEN
 FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 IRTAC WRITING_BACK_BD_REMOVE_RELEASED_BDS_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA THEN
 IRTAC WRITING_BACK_BD_APPEND_REQUEST_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA THEN
 FIRTAC BD_PRESERVED_TRANSITIVITY_LEMMA THEN
 FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 2 THEN
 FIRTAC ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA THEN
 STAC
]
QED

Theorem WRITING_BACK_BD_L2_IMPLIES_BD_Q_PRESERVED_BDS_TO_UPDATE_LEMMA:
!internal_state2 channel2 device_characteristics channel_id memory
 environment internal_state1 channel1 device1 device2 q1 q2 channel_id'.
  (internal_state2, channel2) = writing_back_bd_l2 device_characteristics channel_id memory environment internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  channel1 = schannel device1 channel_id /\
  q2 = (schannel device2 channel_id').queue /\
  q1 = (schannel device1 channel_id').queue
  ==>
  BD_Q_PRESERVED q1.bds_to_update q2.bds_to_update
Proof
INTRO_TAC THEN
PTAC l2Theory.writing_back_bd_l2 THENL
[
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 2 THEN
 IRTAC WRITING_BACK_BD_REMOVE_RELEASED_BDS_IMPLIES_BD_Q_PRESERVED_BDS_TO_UPDATE_LEMMA THEN
 FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_UPDATE_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 IRTAC WRITING_BACK_BD_REMOVE_RELEASED_BDS_IMPLIES_BD_Q_PRESERVED_BDS_TO_UPDATE_LEMMA THEN
 IRTAC WRITING_BACK_BD_APPEND_REQUEST_IMPLIES_BD_Q_PRESERVED_BDS_TO_UPDATE_LEMMA THEN
 FIRTAC BD_PRESERVED_TRANSITIVITY_LEMMA THEN
 FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_UPDATE_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 2 THEN
 FIRTAC ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_UPDATE_LEMMA THEN
 STAC
]
QED

Theorem WRITING_BACK_BD_L2_IMPLIES_BD_Q_PRESERVED_BDS_TO_PROCESS_LEMMA:
!internal_state2 channel2 device_characteristics channel_id memory
 environment internal_state1 channel1 device1 device2 q1 q2 channel_id'.
  (internal_state2, channel2) = writing_back_bd_l2 device_characteristics channel_id memory environment internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  channel1 = schannel device1 channel_id /\
  q2 = (schannel device2 channel_id').queue /\
  q1 = (schannel device1 channel_id').queue
  ==>
  BD_Q_PRESERVED q1.bds_to_process q2.bds_to_process
Proof
INTRO_TAC THEN
PTAC l2Theory.writing_back_bd_l2 THENL
[
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 2 THEN
 IRTAC WRITING_BACK_BD_REMOVE_RELEASED_BDS_IMPLIES_BD_Q_PRESERVED_BDS_TO_PROCESS_LEMMA THEN
 FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_PROCESS_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 IRTAC WRITING_BACK_BD_REMOVE_RELEASED_BDS_IMPLIES_BD_Q_PRESERVED_BDS_TO_PROCESS_LEMMA THEN
 IRTAC WRITING_BACK_BD_APPEND_REQUEST_IMPLIES_BD_Q_PRESERVED_BDS_TO_PROCESS_LEMMA THEN
 FIRTAC BD_PRESERVED_TRANSITIVITY_LEMMA THEN
 FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_PRESERVED_BDS_TO_PROCESS_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 2 THEN
 FIRTAC ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_PRESERVED_BDS_TO_PROCESS_LEMMA THEN
 STAC
]
QED



Theorem WRITING_BACK_BD_REMOVE_RELEASED_BDS_IMPLIES_BD_Q_RELEASED_LEMMA:
!channel1 channel2 released_bds.
  channel2 = writing_back_bd_remove_released_bds channel1 released_bds
  ==>
  BD_Q_RELEASED channel1.queue.bds_to_write_back channel2.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC operationsTheory.writing_back_bd_remove_released_bds THEN
ETAC operationsTheory.update_channel_qs THEN
ETAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [BD_Q_RELEASED] THEN
INTRO_TAC THEN
ETAC listTheory.MEM_FILTER THEN
STAC
QED

Theorem WRITING_BACK_BD_APPEND_REQUEST_IMPLIES_BD_Q_RELEASED_LEMMA:
!channel1 channel2 write_address_bytes tag.
  channel2 = writing_back_bd_append_request channel1 write_address_bytes tag
  ==>
  BD_Q_RELEASED channel1.queue.bds_to_write_back channel2.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC operationsTheory.writing_back_bd_append_request THENL
[
 ASM_REWRITE_TAC [BD_Q_RELEASED_REFL_LEMMA]
 ,
 LRTAC THEN
 RECORD_TAC THEN
 REWRITE_TAC [BD_Q_RELEASED_REFL_LEMMA]
]
QED

Theorem WRITING_BACK_BD_L2_IMPLIES_BD_Q_RELEASED_BDS_TO_WRITE_BACK_LEMMA:
!internal_state2 channel2 device_characteristics channel_id memory
 environment internal_state1 channel1 device1 device2 q1 q2 channel_id'.
  (internal_state2, channel2) = writing_back_bd_l2 device_characteristics channel_id memory environment internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  channel1 = schannel device1 channel_id /\
  q2 = (schannel device2 channel_id').queue /\
  q1 = (schannel device1 channel_id').queue
  ==>
  BD_Q_RELEASED q1.bds_to_write_back q2.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC l2Theory.writing_back_bd_l2 THENL
[
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 2 THEN
 IRTAC WRITING_BACK_BD_REMOVE_RELEASED_BDS_IMPLIES_BD_Q_RELEASED_LEMMA THEN
 FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_RELEASED_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 IRTAC WRITING_BACK_BD_REMOVE_RELEASED_BDS_IMPLIES_BD_Q_RELEASED_LEMMA THEN
 IRTAC WRITING_BACK_BD_APPEND_REQUEST_IMPLIES_BD_Q_RELEASED_LEMMA THEN
 FIRTAC BD_Q_RELEASED_TRANSITIVITY_LEMMA THEN
 FIRTAC UPDATE_DEVICE_PRESERVES_BD_Q_RELEASED_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 IRTAC ID_UPDATE_DEVICE_STATE_IMPLIES_BD_Q_RELEASED_LEMMA THEN
 STAC
]
QED

Theorem WRITING_BACK_BD_L2_IMPLIES_CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_BD_RAS_WAS_LEMMA:
!device_characteristics device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id memory environment.
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = (schannel device1 channel_id) /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = writing_back_bd_l2 device_characteristics channel_id memory environment internal_state1 channel1
  ==>
  CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_BD_RAS_WAS device_characteristics device1 device2
Proof
INTRO_TAC THEN
PTAC CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_BD_RAS_WAS THEN
INTRO_TAC THEN
CONJS_TAC THENL
[
 IRTAC WRITING_BACK_BD_L2_IMPLIES_BD_Q_PRESERVED_BDS_TO_FETCH_LEMMA THEN STAC
 ,
 IRTAC WRITING_BACK_BD_L2_IMPLIES_BD_Q_PRESERVED_BDS_TO_UPDATE_LEMMA THEN STAC
 ,
 IRTAC WRITING_BACK_BD_L2_IMPLIES_BD_Q_PRESERVED_BDS_TO_PROCESS_LEMMA THEN STAC 
 ,
 IRTAC WRITING_BACK_BD_L2_IMPLIES_BD_Q_RELEASED_BDS_TO_WRITE_BACK_LEMMA THEN STAC
]
QED



Theorem WRITING_BACK_BD_L2_IMPLIES_SCRATCHPAD_ADDRESSES_EQ_LEMMA:
!device_characteristics channel_id device1 device2 internal_state1 internal_state2 channel1 channel2 memory environment.
  PROOF_OBLIGATION_WRITE_BACK_BD_PRESERVES_SCRATCHPAD device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = writing_back_bd_l2 device_characteristics channel_id memory environment internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  SCRATCHPAD_ADDRESSES_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
ETAC stateTheory.SCRATCHPAD_ADDRESSES_EQ THEN
PTAC l2Theory.writing_back_bd_l2 THENL
[
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_WRITE_BACK_BD_PRESERVES_SCRATCHPAD THEN
 AIRTAC THEN
 PTAC operationsTheory.update_device_state THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_WRITE_BACK_BD_PRESERVES_SCRATCHPAD THEN
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

Theorem WRITING_BACK_BD_L2_IMPLIES_BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_LEMMA:
!device_characteristics channel_id device1 device2 internal_state1 internal_state2 channel1 channel2 memory environment.
  PROOF_OBLIGATION_WRITE_BACK_PRESERVES_BD_INTERPRETATION device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = writing_back_bd_l2 device_characteristics channel_id memory environment internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ device_characteristics device1 device2
Proof
INTRO_TAC THEN
ETAC BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ THEN
INTRO_TAC THEN
REWRITE_TAC [boolTheory.FUN_EQ_THM] THEN
GEN_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_WRITE_BACK_PRESERVES_BD_INTERPRETATION THEN
PTAC l2Theory.writing_back_bd_l2 THENL
[
 EQ_PAIR_ASM_TAC THEN
 FAIRTAC THEN
 AIRTAC THEN
 RLTAC THEN
 PTAC operationsTheory.update_device_state THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 FAIRTAC THEN
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

Theorem WRITING_BACK_BD_L2_PRESERVES_FETCH_UPDATE_PROCESS_WRITE_BACK_SCRATCHPAD_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id environment.
  PROOF_OBLIGATION_WRITE_BACK_BD_PRESERVES_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_PRESERVES_BD_INTERPRETATION device_characteristics /\

  INVARIANT_FETCH_BD_L2 device_characteristics memory device1 /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device1 /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device1 /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device1 /\
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device1 /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device1 /\

  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = (schannel device1 channel_id) /\
  (internal_state2, channel2) = writing_back_bd_l2 device_characteristics channel_id memory environment internal_state1 channel1 /\
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
ITAC WRITING_BACK_BD_L2_IMPLIES_SCRATCHPAD_ADDRESSES_EQ_LEMMA THEN
ITAC WRITING_BACK_BD_L2_IMPLIES_BD_TRANSFER_RAS_WAS_INTERNAL_STATE_EQ_LEMMA THEN
ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_IMPLIES_PENDING_REGISTER_RELEATED_MEMORY_REQUESTS_IN_POST_STATE_LEMMA THEN
ITAC SCRATCHPAD_ADDRESSES_EQ_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA THEN
ITAC SCRATCHPAD_ADDRESSES_EQ_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA THEN
IRTAC WRITING_BACK_BD_L2_IMPLIES_CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_BD_RAS_WAS_LEMMA THEN
ITAC CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA THEN
ITAC CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA THEN
ITAC CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA THEN
ITAC CHANNELS_WRITE_BACK_BD_Q_TRANSITIONS_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA THEN
STAC
QED

val _ = export_theory();

