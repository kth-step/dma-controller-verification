open HolKernel Parse boolLib bossLib helper_tactics;
open l4Theory invariant_l4Theory invariant_l4_lemmasTheory;

val _ = new_theory "transferring_data_l4_preserves_invariant_concrete_l4_lemmas";

Theorem TRANSFERRING_DATA_L4_PRESERVES_OR_UPDATES_INTERNAL_STATE_LEMMA:
!device_characteristics channel_id internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = transferring_data_l4 device_characteristics channel_id internal_state1 channel1
  ==>
  internal_state2 = internal_state1 \/
  ?new_requests complete bd ras was bds replies.
    channel1.queue.bds_to_process = (bd, ras, was)::bds /\
    (internal_state2, new_requests, complete) = (coperation device_characteristics channel_id).process_replies_generate_requests internal_state1 bd replies
Proof
INTRO_TAC THEN
PTAC transferring_data_l4 THEN EQ_PAIR_ASM_TAC THEN TRY STAC THEN
RLTAC THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
PTAC operationsTheory.transferring_data_replies_requests THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 4 THEN
PAXTAC THEN
STAC
QED

Theorem TRANSFERRING_DATA_L4_IMPLIES_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = transferring_data_l4 device_characteristics channel_id internal_state1 channel1
  ==>
  BDS_TO_FETCH_EQ device_characteristics memory internal_state1 internal_state2
Proof
INTRO_TAC THEN
IRTAC TRANSFERRING_DATA_L4_PRESERVES_OR_UPDATES_INTERNAL_STATE_LEMMA THEN
SPLIT_ASM_DISJS_TAC THEN TRY (ASM_REWRITE_TAC [stateTheory.BDS_TO_FETCH_EQ]) THEN
AXTAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH THEN
AIRTAC THEN
STAC
QED

Theorem TRANSFERRING_DATA_L4_SHIFTS_BDS_TO_PROCESS_WRITE_BACK_LEMMA:
!device_characteristics channel_id internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = transferring_data_l4 device_characteristics channel_id internal_state1 channel1
  ==>
  (channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
   channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back) \/
  ?bd bds.
    channel1.queue.bds_to_process = bd::bds /\
    channel2.queue.bds_to_process = bds /\
    channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back ++ [bd]
Proof
INTRO_TAC THEN
PTAC transferring_data_l4 THENL
[
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 IRTAC transferring_data_l3_preserves_invariant_concrete_l3_lemmasTheory.TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_BDS_LEMMA THEN
 IF_SPLIT_TAC THENL
 [
  RLTAC THEN
  ITAC transferring_data_l3_preserves_invariant_concrete_l3_lemmasTheory.TRANSFERRING_DATA_UPDATE_QS_SHIFTS_BDS_TO_UPDATE_PROCESS_WRITE_BACK_LEMMA THEN
  IRTAC transferring_data_l3_preserves_invariant_concrete_l3_lemmasTheory.TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_BDS_LEMMA THEN
  RLTAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  LRTAC THEN
  RLTAC THEN
  RLTAC THEN
  EXISTS_EQ_TAC
  ,
  IRTAC transferring_data_l3_preserves_invariant_concrete_l3_lemmasTheory.TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_BDS_LEMMA THEN
  STAC
 ]
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem TRANSFERRING_DATA_L4_PRESERVES_BDS_TO_UPDATE_LEMMA:
!device_characteristics channel_id internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = transferring_data_l4 device_characteristics channel_id internal_state1 channel1
  ==>
  channel2.queue.bds_to_update = channel1.queue.bds_to_update
Proof
INTRO_TAC THEN
PTAC transferring_data_l4 THENL
[
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 IRTAC transferring_data_l3_preserves_invariant_concrete_l3_lemmasTheory.TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_BDS_LEMMA THEN
 IF_SPLIT_TAC THENL
 [
  RLTAC THEN
  ITAC transferring_data_l3_preserves_invariant_concrete_l3_lemmasTheory.TRANSFERRING_DATA_UPDATE_QS_SHIFTS_BDS_TO_UPDATE_PROCESS_WRITE_BACK_LEMMA THEN
  IRTAC transferring_data_l3_preserves_invariant_concrete_l3_lemmasTheory.TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_BDS_LEMMA THEN
  STAC
  ,
  IRTAC transferring_data_l3_preserves_invariant_concrete_l3_lemmasTheory.TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_BDS_LEMMA THEN STAC
 ]
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem TRANSFERRING_DATA_L4_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA:
!device_characteristics channel_id device1 device2 internal_state1 internal_state2 channel1 channel2.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = transferring_data_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
IRTAC TRANSFERRING_DATA_L4_PRESERVES_OR_UPDATES_INTERNAL_STATE_LEMMA THEN
ETAC stateTheory.BD_TRANSFER_RAS_WAS_EQ THEN
SPLIT_ASM_DISJS_TAC THENL
[
 RLTAC THEN LRTAC THEN IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN STAC
 ,
 AXTAC THEN
 ETAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION THEN
 AIRTAC THEN
 RLTAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 LRTAC THEN
 INTRO_TAC THEN
 AIRTAC THEN
 STAC
]
QED

Theorem TRANSFERRING_DATA_L4_IMPLIES_BDS_TO_FETCH_NOT_EXPANDED_LEMMA:
!device_characteristics channel_id device1 device2 internal_state1 internal_state2 channel1 channel2.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = transferring_data_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  !memory.
    BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
IRTAC TRANSFERRING_DATA_L4_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
RLTAC THEN
IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
LRTAC THEN
REWRITE_TAC [BDS_TO_FETCH_NOT_EXPANDED] THEN
RW_HYPS_TAC stateTheory.BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
AIRTAC THEN
STAC
QED

Theorem TRANSFERRING_DATA_L4_IMPLIES_BDS_TO_UPDATE_NOT_EXPANDED_LEMMA:
!device_characteristics channel_id device1 device2 internal_state1 internal_state2 channel1 channel2.
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = transferring_data_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BDS_TO_UPDATE_NOT_EXPANDED device_characteristics device1 device2
Proof
INTRO_TAC THEN
IRTAC TRANSFERRING_DATA_L4_PRESERVES_BDS_TO_UPDATE_LEMMA THEN
ETAC BDS_TO_UPDATE_NOT_EXPANDED THEN
ETAC BDS_TO_OPERATE_ON_NOT_EXPANDED THEN
INTRO_TAC THEN
Cases_on ‘channel_id' = channel_id’ THENL
[
 LRTAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN
 ALL_LRTAC THEN
 REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
 ,
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN
 AIRTAC THEN
 ALL_LRTAC THEN
 REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
]
QED

Theorem TRANSFERRING_DATA_L4_IMPLIES_BDS_TO_PROCESS_NOT_EXPANDED_LEMMA:
!device_characteristics channel_id device1 device2 internal_state1 internal_state2 channel1 channel2.
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = transferring_data_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BDS_TO_PROCESS_NOT_EXPANDED device_characteristics device1 device2
Proof
INTRO_TAC THEN
IRTAC TRANSFERRING_DATA_L4_SHIFTS_BDS_TO_PROCESS_WRITE_BACK_LEMMA THEN
ETAC BDS_TO_PROCESS_NOT_EXPANDED THEN
ETAC BDS_TO_OPERATE_ON_NOT_EXPANDED THEN
INTRO_TAC THEN
Cases_on ‘channel_id' = channel_id’ THENL
[
 LRTAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN
 ALL_LRTAC THEN
 REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA] THEN
 SPLIT_ASM_DISJS_TAC THEN TRY (ALL_LRTAC THEN REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]) THEN
 AXTAC THEN
 ALL_LRTAC THEN
 ETAC listsTheory.LIST1_IN_LIST2 THEN
 ETAC listTheory.EVERY_MEM THEN
 INTRO_TAC THEN
 APP_SCALAR_TAC THEN
 ASM_REWRITE_TAC [listTheory.MEM]
 ,
 LRTAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN
 AIRTAC THEN
 SPLIT_ASM_DISJS_TAC THEN
  ALL_LRTAC THEN REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
]
QED

Theorem TRANSFERRING_DATA_L4_IMPLIES_BD_TO_PROCESS_TO_BDS_TO_WRITE_BACK_LEMMA:
!device_characteristics channel_id device1 device2 internal_state1 internal_state2 channel1 channel2.
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = transferring_data_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TO_PROCESS_TO_BDS_TO_WRITE_BACK device_characteristics device1 device2
Proof
INTRO_TAC THEN
IRTAC TRANSFERRING_DATA_L4_SHIFTS_BDS_TO_PROCESS_WRITE_BACK_LEMMA THEN
ETAC BD_TO_PROCESS_TO_BDS_TO_WRITE_BACK THEN
INTRO_TAC THEN
Cases_on ‘channel_id' = channel_id’ THEN TRY (IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN AIRTAC THEN STAC) THEN
LRTAC THEN
IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN
LRTAC THEN
RLTAC THEN
SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
AXTAC THEN
ALL_LRTAC THEN
REWRITE_TAC [listTheory.TL, listTheory.NULL]
QED

Theorem TRANSFERRING_DATA_L4_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = transferring_data_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  INVARIANT_CONCRETE_L4 device_characteristics memory device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_CONCRETE_L4 THEN
ITAC TRANSFERRING_DATA_L4_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA THEN
ITAC TRANSFERRING_DATA_L4_IMPLIES_BDS_TO_FETCH_NOT_EXPANDED_LEMMA THEN
ITAC TRANSFERRING_DATA_L4_IMPLIES_BDS_TO_UPDATE_NOT_EXPANDED_LEMMA THEN
ITAC TRANSFERRING_DATA_L4_IMPLIES_BDS_TO_PROCESS_NOT_EXPANDED_LEMMA THEN
IRTAC TRANSFERRING_DATA_L4_IMPLIES_BD_TO_PROCESS_TO_BDS_TO_WRITE_BACK_LEMMA THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4_LEMMA THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4_LEMMA THEN
ITAC BDS_TO_UPDATE_NOT_EXPANDED_PRESERVES_INVARIANT_UPDATE_BD_BD_WRITE_L4_LEMMA THEN
ITAC BDS_TO_PROCESS_NOT_EXPANDED_PRESERVES_INVARIANT_PROCESS_BD_BD_WRITE_L4_LEMMA THEN
ITAC BDS_TO_PROCESS_TO_BDS_TO_WRITE_BACK_PRESERVES_INVARIANT_WRITE_BACK_BD_BD_WRITE_L4_LEMMA THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_INVARIANT_FETCH_BD_DMA_WRITE_L4_LEMMA THEN
ITAC BDS_TO_UPDATE_NOT_EXPANDED_PRESERVES_INVARIANT_UPDATE_BD_DMA_WRITE_L4_LEMMA THEN
IRTAC BDS_TO_PROCESS_NOT_EXPANDED_PRESERVES_INVARIANT_PROCESS_BD_DMA_WRITE_L4_LEMMA THEN
STAC
QED

val _ = export_theory();

