open HolKernel Parse boolLib bossLib helper_tactics;
open l4Theory invariant_l4Theory invariant_l4_lemmasTheory;

val _ = new_theory "updating_bd_l4_preserves_invariant_concrete_l4_lemmas";

(*******************************************************************************)

Theorem UPDATING_BD_UPDATING_INTERNAL_STATE_LEMMA:
!device_characteristics channel_id internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = updating_bd_l4 device_characteristics channel_id internal_state1 channel1
  ==>
  internal_state2 = internal_state1 \/
  ?address_bytes tag update_status bd bds.
    channel1.queue.bds_to_update = bd::bds /\
    (internal_state2, address_bytes, tag, update_status) = (coperation device_characteristics channel_id).update_bd internal_state1 bd
Proof
INTRO_TAC THEN
PTAC updating_bd_l4 THEN TRY (EQ_PAIR_ASM_TAC THEN STAC) THEN EQ_PAIR_ASM_TAC THEN NRLTAC 2 THEN MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN RLTAC THEN EXISTS_EQ_TAC THEN PAXTAC THEN STAC
QED

Theorem UPDATE_BD_IMPLIES_UPDATE_BD_ADDRESSES_LEMMA:
!device_characteristics internal_state1 internal_state2 address_bytes tag uf channel_id bd.
  (internal_state2, address_bytes, tag, uf) = (coperation device_characteristics channel_id).update_bd internal_state1 bd
  ==>
  ?write_addresses.
    write_addresses = (cverification device_characteristics channel_id).update_bd_addresses internal_state1 bd
Proof
INTRO_TAC THEN
EXISTS_EQ_TAC
QED

Theorem UPDATE_BD_IMPLIES_UPDATE_BD_ADDRESSES_LEMMA:
!device_characteristics internal_state1 internal_state2 address_bytes tag uf channel_id bd ras was.
  PROOF_OBLIGATION_DECLARED_UPDATE_WRITES_BD_WAS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, address_bytes, tag, uf) = (coperation device_characteristics channel_id).update_bd internal_state1 (bd, ras, was)
  ==>
  ?write_addresses.
    write_addresses = (cverification device_characteristics channel_id).update_bd_addresses internal_state1 (bd, ras, was) /\
    LIST1_IN_LIST2 write_addresses was
Proof
INTRO_TAC THEN
ITAC UPDATE_BD_IMPLIES_UPDATE_BD_ADDRESSES_LEMMA THEN
AXTAC THEN
PAXTAC THEN
CONJS_TAC THEN TRY STAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_DECLARED_UPDATE_WRITES_BD_WAS THEN
AIRTAC THEN
STAC
QED

Theorem UPDATING_BD_L4_IMPLIES_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 device1.
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  PROOF_OBLIGATION_DECLARED_UPDATE_WRITES_BD_WAS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  INVARIANT_UPDATE_BD_BD_WRITE_L4 device_characteristics memory device1 /\
  (internal_state2, channel2) = updating_bd_l4 device_characteristics channel_id internal_state1 channel1
  ==>
  BDS_TO_FETCH_EQ device_characteristics memory internal_state1 internal_state2
Proof
INTRO_TAC THEN
IRTAC UPDATING_BD_UPDATING_INTERNAL_STATE_LEMMA THEN
ETAC stateTheory.BDS_TO_FETCH_EQ THEN
SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
AXTAC THEN
PTAC invariant_l4Theory.INVARIANT_UPDATE_BD_BD_WRITE_L4 THEN
ETAC BD_WRITE THEN
IRTAC lists_lemmasTheory.MEM_HD_LEMMA THEN
FAITAC THEN
ETAC bd_queuesTheory.CONSISTENT_BD_WRITE THEN
Cases_on ‘EXTERNAL_BDS device_characteristics’ THENL
[
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST THEN
 FAIRTAC THEN
 INTRO_TAC THEN
 AIRTAC THEN
 STAC
 ,
 IRTAC state_lemmasTheory.NOT_EXTERNAL_BDS_IMPLIES_INTERNAL_BDS_LEMMA THEN
 ITAC UPDATE_BD_IMPLIES_UPDATE_BD_ADDRESSES_LEMMA THEN
 AXTAC THEN
 IRTAC bd_queues_lemmasTheory.LIST1_IN_LIST2_PRESERVES_WRITE_ADDRESS_NOT_BD_TO_FETCH_LEMMA THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL THEN
 AIRTAC THEN
 STAC
]
QED

Theorem UPDATING_BD_L4_IMPLIES_BDS_TO_FETCH_NOT_EXPANDED_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 device1 device2.
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  PROOF_OBLIGATION_DECLARED_UPDATE_WRITES_BD_WAS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  INVARIANT_UPDATE_BD_BD_WRITE_L4 device_characteristics memory device1 /\
  (internal_state2, channel2) = updating_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
ITAC UPDATING_BD_L4_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
LRTAC THEN
IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
RLTAC THEN
IRTAC BDS_TO_FETCH_EQ_IMPLIES_BDS_TO_FETCH_NOT_EXPANDED_LEMMA THEN
STAC
QED

(*******************************************************************************)

Theorem UPDATING_BD_L4_SHIFTS_BDS_TO_UPDATE_PROCESS_LEMMA:
!device_characteristics channel_id internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = updating_bd_l4 device_characteristics channel_id internal_state1 channel1
  ==>
  (channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
   channel2.queue.bds_to_process = channel1.queue.bds_to_process) \/
  ?bd bds.
    channel1.queue.bds_to_update = bd::bds /\
    channel2.queue.bds_to_update = bds /\
    channel2.queue.bds_to_process = channel1.queue.bds_to_process ++ [bd]
Proof
INTRO_TAC THEN
PTAC updating_bd_l4 THEN TRY (EQ_PAIR_ASM_TAC THEN STAC) THENL
[
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 2 THEN
 IRTAC updating_bd_lemmasTheory.UPDATING_BD_UPDATE_QS_SHIFTS_BDS_TO_UPDATE_PROCESS_LEMMA THEN
 SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 PAXTAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 IRTAC updating_bd_lemmasTheory.UPDATING_BD_UPDATE_QS_SHIFTS_BDS_TO_UPDATE_PROCESS_LEMMA THEN
 IRTAC updating_bd_lemmasTheory.UPDATING_BD_APPEND_REQUEST_PRESERVES_BDS_TO_UPDATE_PROCESS_WRITE_BACK_LEMMA THEN
 NRLTAC 3 THEN
 SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 PAXTAC THEN
 STAC
]
QED

Theorem UPDATING_BD_L4_IMPLIES_BDS_TO_UPDATE_NOT_EXPANDED_LEMMA:
!device_characteristics channel_id internal_state1 internal_state2 channel1 channel2 device1 device2.
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = updating_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BDS_TO_UPDATE_NOT_EXPANDED device_characteristics device1 device2
Proof
INTRO_TAC THEN
IRTAC UPDATING_BD_L4_SHIFTS_BDS_TO_UPDATE_PROCESS_LEMMA THEN
ETAC BDS_TO_UPDATE_NOT_EXPANDED THEN
ETAC BDS_TO_OPERATE_ON_NOT_EXPANDED THEN
INTRO_TAC THEN
Cases_on ‘channel_id' = channel_id’ THENL
[
 LRTAC THEN
 ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN
 LRTAC THEN
 RLTAC THEN
 RLTAC THEN
 LRTAC THEN
 SPLIT_ASM_DISJS_TAC THEN TRY (LRTAC THEN REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]) THEN
 AXTAC THEN
 ETAC listsTheory.LIST1_IN_LIST2 THEN
 ALL_LRTAC THEN
 ETAC listTheory.EVERY_MEM THEN
 INTRO_TAC THEN
 APP_SCALAR_TAC THEN
 ASM_REWRITE_TAC [listTheory.MEM]
 ,
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN
 AIRTAC THEN
 ALL_LRTAC THEN
 REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
]
QED

(*******************************************************************************)

Theorem UPDATING_BD_L4_IMPLIES_BD_TO_UPDATE_TO_BDS_TO_PROCESS_LEMMA:
!device_characteristics channel_id internal_state1 internal_state2 channel1 channel2 device1 device2.
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = updating_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TO_UPDATE_TO_BDS_TO_PROCESS device_characteristics device1 device2
Proof
INTRO_TAC THEN
IRTAC UPDATING_BD_L4_SHIFTS_BDS_TO_UPDATE_PROCESS_LEMMA THEN
ETAC BD_TO_UPDATE_TO_BDS_TO_PROCESS THEN
INTRO_TAC THEN
Cases_on ‘channel_id' = channel_id’ THENL
[
 LRTAC THEN
 ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN
 LRTAC THEN
 RLTAC THEN
 SPLIT_ASM_DISJS_TAC THEN
 STAC
 ,
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN AIRTAC THEN STAC
]
QED

(*******************************************************************************)

Theorem UPDATING_BD_L4_PRESERVES_BDS_TO_WRITE_BACK_LEMMA:
!device_characteristics channel_id internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = updating_bd_l4 device_characteristics channel_id internal_state1 channel1
  ==>
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC updating_bd_l4 THEN TRY (EQ_PAIR_ASM_TAC THEN STAC) THENL
[
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 2 THEN
 IRTAC updating_bd_lemmasTheory.UPDATING_BD_UPDATE_QS_PRESERVES_BDS_TO_WRITE_BACK_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 IRTAC updating_bd_lemmasTheory.UPDATING_BD_UPDATE_QS_PRESERVES_BDS_TO_WRITE_BACK_LEMMA THEN
 IRTAC updating_bd_lemmasTheory.UPDATING_BD_APPEND_REQUEST_PRESERVES_BDS_TO_UPDATE_PROCESS_WRITE_BACK_LEMMA THEN
 STAC
]
QED

Theorem UPDATING_BD_L4_IMPLIES_BDS_TO_WRITE_BACK_NOT_EXPANDED_LEMMA:
!device_characteristics channel_id internal_state1 internal_state2 channel1 channel2 device1 device2.
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = updating_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BDS_TO_WRITE_BACK_NOT_EXPANDED device_characteristics device1 device2
Proof
INTRO_TAC THEN
ETAC BDS_TO_WRITE_BACK_NOT_EXPANDED THEN
ETAC BDS_TO_OPERATE_ON_NOT_EXPANDED THEN
INTRO_TAC THEN
Cases_on ‘channel_id' = channel_id’ THENL
[
 LRTAC THEN
 ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN
 LRTAC THEN
 RLTAC THEN
 IRTAC UPDATING_BD_L4_PRESERVES_BDS_TO_WRITE_BACK_LEMMA THEN
 ALL_LRTAC THEN
 REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
 ,
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN
 AIRTAC THEN
 ALL_LRTAC THEN
 REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
]
QED

(*******************************************************************************)

Theorem UPDATING_BD_L4_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA:
!device_characteristics channel_id device1 device2 internal_state1 internal_state2 channel1 channel2.
  PROOF_OBLIGATION_UPDATING_BD_PRESERVES_BD_INTERPRETATION device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = updating_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
IRTAC UPDATING_BD_UPDATING_INTERNAL_STATE_LEMMA THEN
ETAC stateTheory.BD_TRANSFER_RAS_WAS_EQ THEN
SPLIT_ASM_DISJS_TAC THENL
[
 RLTAC THEN LRTAC THEN IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN STAC
 ,
 AXTAC THEN
 ETAC proof_obligationsTheory.PROOF_OBLIGATION_UPDATING_BD_PRESERVES_BD_INTERPRETATION THEN
 AIRTAC THEN
 RLTAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 LRTAC THEN
 INTRO_TAC THEN
 AIRTAC THEN
 STAC
]
QED

(*******************************************************************************)

Theorem UPDATING_BD_L4_PRESERVES_INVARIANT_CONCRETE_L4_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics /\
  PROOF_OBLIGATION_DECLARED_UPDATE_WRITES_BD_WAS device_characteristics /\
  PROOF_OBLIGATION_UPDATING_BD_PRESERVES_BD_INTERPRETATION device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  (internal_state2, channel2) = updating_bd_l4 device_characteristics channel_id internal_state1 channel1 /\
  INVARIANT_CONCRETE_L4 device_characteristics memory device1
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_CONCRETE_L4 THEN
ITAC UPDATING_BD_L4_IMPLIES_BDS_TO_FETCH_NOT_EXPANDED_LEMMA THEN
ITAC UPDATING_BD_L4_IMPLIES_BDS_TO_UPDATE_NOT_EXPANDED_LEMMA THEN
ITAC UPDATING_BD_L4_IMPLIES_BD_TO_UPDATE_TO_BDS_TO_PROCESS_LEMMA THEN
ITAC UPDATING_BD_L4_IMPLIES_BDS_TO_WRITE_BACK_NOT_EXPANDED_LEMMA THEN
ITAC UPDATING_BD_L4_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4_LEMMA THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4_LEMMA THEN
ITAC BDS_TO_UPDATE_NOT_EXPANDED_PRESERVES_INVARIANT_UPDATE_BD_BD_WRITE_L4_LEMMA THEN
ITAC BDS_TO_UPDATE_TO_BDS_TO_PROCESS_PRESERVES_INVARIANT_PROCESS_BD_BD_WRITE_L4_LEMMA THEN
ITAC BDS_TO_WRITE_BACK_NOT_EXPANDED_PRESERVES_INVARIANT_WRITE_BACK_BD_BD_WRITE_L4_LEMMA THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_INVARIANT_FETCH_BD_DMA_WRITE_L4_LEMMA THEN
ITAC BDS_TO_UPDATE_NOT_EXPANDED_PRESERVES_INVARIANT_UPDATE_BD_DMA_WRITE_L4_LEMMA THEN
ITAC BD_TO_UPDATE_TO_BDS_TO_PROCESS_PRESERVES_INVARIANT_PROCESS_BD_DMA_WRITE_L4_LEMMA THEN
STAC
QED

val _ = export_theory();

