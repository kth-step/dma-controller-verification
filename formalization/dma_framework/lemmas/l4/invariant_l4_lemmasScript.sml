open HolKernel Parse boolLib bossLib helper_tactics;
open invariant_l4Theory;

val _ = new_theory "invariant_l4_lemmas";

Theorem INVARIANT_L4_IMPLIES_INVARIANT_L3_LEMMA:
!device_characteristics memory device.
  INVARIANT_L4 device_characteristics memory device
  ==>
  INVARIANT_L3 device_characteristics memory device
Proof
INTRO_TAC THEN
ETAC INVARIANT_L4 THEN
ETAC invariant_l3Theory.INVARIANT_L3 THEN
CONJS_TAC THEN TRY STAC
QED

Theorem INVARIANT_L4_IMPLIES_INVARIANT_CONCRETE_L4_BDS_TO_FETCH_DISJOINT_EXTERNAL_FETCH_BD_REPLY_NO_MEMORY_WRITES_TO_BDS_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics memory device.
  INVARIANT_L4 device_characteristics memory device
  ==>
  INVARIANT_CONCRETE_L4 device_characteristics memory device /\
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device
Proof
INTRO_TAC THEN
ETAC INVARIANT_L4 THEN
ETAC INVARIANT_CONCRETE_L4 THEN
STAC
QED

Theorem INVARIANT_L3_INVARIANT_CONCRETE_L4_IMPLIES_INVARIANT_L4_LEMMA:
!device_characteristics memory device.
  INVARIANT_L3 device_characteristics memory device /\
  INVARIANT_CONCRETE_L4 device_characteristics memory device
  ==>
  INVARIANT_L4 device_characteristics memory device
Proof
INTRO_TAC THEN
ETAC INVARIANT_L4 THEN
ETAC invariant_l3Theory.INVARIANT_L3 THEN
ETAC INVARIANT_CONCRETE_L4 THEN
STAC
QED


(******************************************************************************)


Definition BDS_TO_FETCH_NOT_EXPANDED:
BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory1 memory2 internal_state1 internal_state2 =
!channel_id bds_to_fetch1 bds_to_fetch2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory1 internal_state1 /\
  bds_to_fetch2 = (cverification device_characteristics channel_id).bds_to_fetch memory2 internal_state2
  ==>
  bds_to_fetch2 = bds_to_fetch1 \/
  bds_to_fetch2 = TL bds_to_fetch1 /\ ~NULL bds_to_fetch1
End

Definition BDS_TO_OPERATE_ON_NOT_EXPANDED:
BDS_TO_OPERATE_ON_NOT_EXPANDED device_characteristics device1 device2 queue_type_bd_queue_to_operate_on =
!channel_id bds_to_operate_on1 bds_to_operate_on2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  bds_to_operate_on1 = queue_type_bd_queue_to_operate_on (schannel device1 channel_id).queue /\
  bds_to_operate_on2 = queue_type_bd_queue_to_operate_on (schannel device2 channel_id).queue
  ==>
  LIST1_IN_LIST2 bds_to_operate_on2 bds_to_operate_on1
End

Definition BDS_TO_UPDATE_NOT_EXPANDED:
BDS_TO_UPDATE_NOT_EXPANDED device_characteristics device1 device2 =
  BDS_TO_OPERATE_ON_NOT_EXPANDED device_characteristics device1 device2 queue_type_bds_to_update
End

Definition BDS_TO_PROCESS_NOT_EXPANDED:
BDS_TO_PROCESS_NOT_EXPANDED device_characteristics device1 device2 =
  BDS_TO_OPERATE_ON_NOT_EXPANDED device_characteristics device1 device2 queue_type_bds_to_process
End

Definition BDS_TO_WRITE_BACK_NOT_EXPANDED:
BDS_TO_WRITE_BACK_NOT_EXPANDED device_characteristics device1 device2 =
  BDS_TO_OPERATE_ON_NOT_EXPANDED device_characteristics device1 device2 queue_type_bds_to_write_back
End

Definition BD_TO_FETCH_TO_BDS_TO_UPDATE:
BD_TO_FETCH_TO_BDS_TO_UPDATE device_characteristics memory device1 device2 =
!channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  (schannel device2 channel_id).queue.bds_to_update = (schannel device1 channel_id).queue.bds_to_update \/
  ?bd uf bds.
    (cverification device_characteristics channel_id).bds_to_fetch memory device1.dma_state.internal_state = (bd, uf)::bds /\
    (cverification device_characteristics channel_id).bds_to_fetch memory device2.dma_state.internal_state = bds /\
    (schannel device2 channel_id).queue.bds_to_update = (schannel device1 channel_id).queue.bds_to_update ++ [bd]
End

Definition BD_TO_FETCH_TO_BDS_TO_PROCESS:
BD_TO_FETCH_TO_BDS_TO_PROCESS device_characteristics memory device1 device2 =
!channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  (schannel device2 channel_id).queue.bds_to_process = (schannel device1 channel_id).queue.bds_to_process \/
  ?bd uf bds.
    (cverification device_characteristics channel_id).bds_to_fetch memory device1.dma_state.internal_state = (bd, uf)::bds /\
    (cverification device_characteristics channel_id).bds_to_fetch memory device2.dma_state.internal_state = bds /\
    (schannel device2 channel_id).queue.bds_to_process = (schannel device1 channel_id).queue.bds_to_process ++ [bd]
End

Definition BD_TO_UPDATE_TO_BDS_TO_PROCESS:
BD_TO_UPDATE_TO_BDS_TO_PROCESS device_characteristics device1 device2 =
!channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  (schannel device2 channel_id).queue.bds_to_process = (schannel device1 channel_id).queue.bds_to_process \/
  ?bd bds.
    (schannel device1 channel_id).queue.bds_to_update = bd::bds /\
    (schannel device2 channel_id).queue.bds_to_update = bds /\
    (schannel device2 channel_id).queue.bds_to_process = (schannel device1 channel_id).queue.bds_to_process ++ [bd]
End

Definition BD_TO_PROCESS_TO_BDS_TO_WRITE_BACK:
BD_TO_PROCESS_TO_BDS_TO_WRITE_BACK device_characteristics device1 device2 =
!channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  (schannel device2 channel_id).queue.bds_to_write_back = (schannel device1 channel_id).queue.bds_to_write_back \/
  ?bd bds.
    (schannel device1 channel_id).queue.bds_to_process = bd::bds /\
    (schannel device2 channel_id).queue.bds_to_process = bds /\
    (schannel device2 channel_id).queue.bds_to_write_back = (schannel device1 channel_id).queue.bds_to_write_back ++ [bd]
End

(*******************************************************************************)

Theorem BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_BDS_TO_FETCH_STRUCTURE_LEMMA:
!device_characteristics memory channel_id device1 device2 preceding_bds following_bds bd1 bd2 bds_to_fetch2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  MEM bd2 (preceding_bds ++ following_bds) /\
  preceding_bds ++ [bd1] ++ following_bds = bds_to_fetch2 /\
  bds_to_fetch2 = (cverification device_characteristics channel_id).bds_to_fetch memory device2.dma_state.internal_state
  ==>
  ?preceding_bds following_bds bds_to_fetch1.
    MEM bd2 (preceding_bds ++ following_bds) /\
    preceding_bds ++ [bd1] ++ following_bds = bds_to_fetch1 /\
    bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory device1.dma_state.internal_state
Proof
INTRO_TAC THEN
ETAC BDS_TO_FETCH_NOT_EXPANDED THEN
AIRTAC THEN
SPLIT_ASM_DISJS_TAC THENL
[
 PAXTAC THEN STAC
 ,
 IRTAC lists_lemmasTheory.LIST_STRUCTURE_PRESERVATION_LEMMA THEN AXTAC THEN PAXTAC THEN STAC
]
QED

Theorem BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_MEM_LEMMA:
!device_characteristics memory channel_id internal_state1 internal_state2 bds_to_fetch1 bds_to_fetch2 bd.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory internal_state1 internal_state2 /\
  bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  bds_to_fetch2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2 /\
  MEM bd bds_to_fetch2
  ==>
  MEM bd bds_to_fetch1
Proof
INTRO_TAC THEN
ETAC BDS_TO_FETCH_NOT_EXPANDED THEN
AIRTAC THEN
SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
IRTAC listTheory.MEM_TL THEN
STAC
QED

Theorem BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_DISJOINT_FROM_OTHER_BDS_TO_FETCH_LEMMA:
!device_characteristics memory device1 device2 channel_id bd_was.
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  DISJOINT_FROM_OTHER_BDS_TO_FETCH device_characteristics channel_id memory device1.dma_state.internal_state bd_was
  ==>
  DISJOINT_FROM_OTHER_BDS_TO_FETCH device_characteristics channel_id memory device2.dma_state.internal_state bd_was
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.DISJOINT_FROM_OTHER_BDS_TO_FETCH THEN
INTRO_TAC THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_MEM_LEMMA THEN
AIRTAC THEN
STAC
QED

Theorem BDS_TO_UPDATE_NOT_EXPANDED_PRESERVES_BDS_TO_UPDATE_LEMMA:
!device_characteristics channel_id device1 device2 bd channel1 channel2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BDS_TO_UPDATE_NOT_EXPANDED device_characteristics device1 device2 /\
  channel1 = schannel device1 channel_id /\
  channel2 = schannel device2 channel_id /\
  MEM bd channel2.queue.bds_to_update
  ==>
  MEM bd channel1.queue.bds_to_update
Proof
INTRO_TAC THEN
ETAC BDS_TO_UPDATE_NOT_EXPANDED THEN
ETAC BDS_TO_OPERATE_ON_NOT_EXPANDED THEN
AIRTAC THEN
REPEAT RLTAC THEN
ETAC listsTheory.LIST1_IN_LIST2 THEN
ETAC listTheory.EVERY_MEM THEN
AIRTAC THEN
APP_SCALAR_TAC THEN
STAC
QED

Theorem BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_BD_WRITE_LEMMA:
!device_characteristics internal_state1 internal_state2 memory bd_was.
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory internal_state1 internal_state2 /\
  CONSISTENT_BD_WRITE device_characteristics memory internal_state1 bd_was
  ==>
  CONSISTENT_BD_WRITE device_characteristics memory internal_state2 bd_was
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.CONSISTENT_BD_WRITE THEN
ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
INTRO_TAC THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_MEM_LEMMA THEN
AIRTAC THEN
STAC
QED

Theorem BDS_TO_PROCESS_NOT_EXPANDED_PRESERVES_BDS_TO_PROCESS_LEMMA:
!device_characteristics channel_id device1 device2 bd channel1 channel2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BDS_TO_PROCESS_NOT_EXPANDED device_characteristics device1 device2 /\
  channel1 = schannel device1 channel_id /\
  channel2 = schannel device2 channel_id /\
  MEM bd channel2.queue.bds_to_process
  ==>
  MEM bd channel1.queue.bds_to_process
Proof
INTRO_TAC THEN
ETAC BDS_TO_PROCESS_NOT_EXPANDED THEN
ETAC BDS_TO_OPERATE_ON_NOT_EXPANDED THEN
AIRTAC THEN
REPEAT RLTAC THEN
ETAC listsTheory.LIST1_IN_LIST2 THEN
ETAC listTheory.EVERY_MEM THEN
AIRTAC THEN
APP_SCALAR_TAC THEN
STAC
QED

Theorem BDS_TO_WRITE_BACK_NOT_EXPANDED_PRESERVES_BDS_TO_WRITE_BACK_LEMMA:
!device_characteristics channel_id device1 device2 bd channel1 channel2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BDS_TO_WRITE_BACK_NOT_EXPANDED device_characteristics device1 device2 /\
  channel1 = schannel device1 channel_id /\
  channel2 = schannel device2 channel_id /\
  MEM bd channel2.queue.bds_to_write_back
  ==>
  MEM bd channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
ETAC BDS_TO_WRITE_BACK_NOT_EXPANDED THEN
ETAC BDS_TO_OPERATE_ON_NOT_EXPANDED THEN
AIRTAC THEN
REPEAT RLTAC THEN
ETAC listsTheory.LIST1_IN_LIST2 THEN
ETAC listTheory.EVERY_MEM THEN
AIRTAC THEN
APP_SCALAR_TAC THEN
STAC
QED

Theorem BD_TRANSFER_WAS_WAS_EQ_PRESERVES_RAS_WAS_LEMMA:
!device_characteristics internal_state1 internal_state2 bd ras_was channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BD_TRANSFER_RAS_WAS_EQ device_characteristics internal_state1 internal_state2 /\
  ras_was = (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state2 bd
  ==>
  ras_was = (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state1 bd
Proof
INTRO_TAC THEN
ETAC stateTheory.BD_TRANSFER_RAS_WAS_EQ THEN
AIRTAC THEN
STAC
QED

Theorem BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA:
!device_characteristics internal_state1 internal_state2 memory was.
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory internal_state1 internal_state2 /\
  CONSISTENT_DMA_WRITE device_characteristics memory internal_state1 was
  ==>
  CONSISTENT_DMA_WRITE device_characteristics memory internal_state2 was
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.CONSISTENT_DMA_WRITE THEN
INTRO_TAC THEN
AIRTAC THEN
ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
INTRO_TAC THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_MEM_LEMMA THEN
AIRTAC THEN
STAC
QED

Theorem BDS_TO_FETCH_STRUCTURE_LEMMA:
!device_characteristics channel_id memory device1 bds_to_fetch1 bd' bd_ras' bd_was' uf' bds_to_fetch bd bd_ras bd_was uf.
  MEM ((bd', bd_ras', bd_was'), uf') bds_to_fetch /\
  bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory device1.dma_state.internal_state /\
  bds_to_fetch1 = ((bd, bd_ras, bd_was), uf)::bds_to_fetch
  ==>
  ?preceding_bds following_bds.
    preceding_bds ++ [((bd, bd_ras, bd_was), uf)] ++ following_bds = bds_to_fetch1 /\
    MEM ((bd', bd_ras', bd_was'), uf') (preceding_bds ++ following_bds)
Proof
INTRO_TAC THEN
Q.EXISTS_TAC ‘[]’ THEN
Q.EXISTS_TAC ‘bds_to_fetch’ THEN
ETAC listTheory.APPEND THEN
STAC
QED

Theorem FETCHED_BD_NOT_BD_TO_FETCH_LEMMA:
!device_characteristics memory device1 device2 channel_id bd bd_ras bd_was bds uf.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4 device_characteristics memory device1 /\
  INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4 device_characteristics memory device1 /\
  (cverification device_characteristics channel_id).bds_to_fetch memory device1.dma_state.internal_state = ((bd, bd_ras, bd_was), uf)::bds /\
  (cverification device_characteristics channel_id).bds_to_fetch memory device2.dma_state.internal_state = bds
  ==>
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory device2.dma_state.internal_state bd_was
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
INTRO_TAC THEN
Cases_on ‘channel_id' = channel_id’ THENL
[
 LRTAC THEN
 RLTAC THEN
 RLTAC THEN
 ETAC INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4 THEN
 ONCE_REWRITE_TAC [lists_lemmasTheory.DISJOINT_LISTS_SYM_LEMMA] THEN
 FITAC BDS_TO_FETCH_STRUCTURE_LEMMA THEN
 AXTAC THEN
 FAIRTAC THEN
 STAC
 ,
 ETAC INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4 THEN
 ITAC lists_lemmasTheory.MEM_HD_LEMMA THEN
 FAITAC THEN
 ETAC bd_queuesTheory.DISJOINT_FROM_OTHER_BDS_TO_FETCH THEN
 ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_MEM_LEMMA THEN
 AIRTAC THEN
 STAC
]
QED

Theorem BD_TO_FETCH_TO_BDS_TO_UPDATE_IMPLIES_BD_MEM_BDS_TO_UPDATE_OR_BDS_TO_FETCH_LEMMA:
!device_characteristics memory device1 device2 channel_id bd bd_ras bd_was channel1 channel2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  BD_TO_FETCH_TO_BDS_TO_UPDATE device_characteristics memory device1 device2 /\
  INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4 device_characteristics memory device1 /\
  INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4 device_characteristics memory device1 /\
  channel1 = schannel device1 channel_id /\
  channel2 = schannel device2 channel_id /\
  MEM (bd, bd_ras, bd_was) channel2.queue.bds_to_update
  ==>
  MEM (bd, bd_ras, bd_was) channel1.queue.bds_to_update \/
  ?uf.
    MEM ((bd, bd_ras, bd_was), uf) ((cverification device_characteristics channel_id).bds_to_fetch memory device1.dma_state.internal_state) /\
    WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory device2.dma_state.internal_state bd_was
Proof
INTRO_TAC THEN
ETAC BD_TO_FETCH_TO_BDS_TO_UPDATE THEN
AITAC THEN
SPLIT_ASM_DISJS_TAC THEN TRY (ALL_RLTAC THEN STAC) THEN
ALL_RLTAC THEN
AXTAC THEN
ITAC FETCHED_BD_NOT_BD_TO_FETCH_LEMMA THEN
ALL_LRTAC THEN
ETAC listTheory.MEM_APPEND THEN
ETAC listTheory.MEM THEN
REMOVE_F_DISJUNCTS_TAC THEN
SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 3 THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
REWRITE_TAC [listTheory.MEM] THEN
EXISTS_EQ_TAC THEN
STAC
QED

Theorem BD_TO_FETCH_TO_BDS_TO_PROCESS_IMPLIES_BD_MEM_BDS_TO_PROCESS_OR_BDS_TO_FETCH_LEMMA:
!device_characteristics memory device1 device2 channel_id bd bd_ras bd_was channel1 channel2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  BD_TO_FETCH_TO_BDS_TO_PROCESS device_characteristics memory device1 device2 /\
  INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4 device_characteristics memory device1 /\
  INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4 device_characteristics memory device1 /\
  channel1 = schannel device1 channel_id /\
  channel2 = schannel device2 channel_id /\
  MEM (bd, bd_ras, bd_was) channel2.queue.bds_to_process
  ==>
  MEM (bd, bd_ras, bd_was) channel1.queue.bds_to_process \/
  ?uf.
    MEM ((bd, bd_ras, bd_was), uf) ((cverification device_characteristics channel_id).bds_to_fetch memory device1.dma_state.internal_state) /\
    WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory device2.dma_state.internal_state bd_was
Proof
INTRO_TAC THEN
ETAC BD_TO_FETCH_TO_BDS_TO_PROCESS THEN
AITAC THEN
SPLIT_ASM_DISJS_TAC THEN TRY (ALL_RLTAC THEN STAC) THEN
ALL_RLTAC THEN
AXTAC THEN
ITAC FETCHED_BD_NOT_BD_TO_FETCH_LEMMA THEN
ALL_LRTAC THEN
ETAC listTheory.MEM_APPEND THEN
ETAC listTheory.MEM THEN
REMOVE_F_DISJUNCTS_TAC THEN
SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 3 THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
REWRITE_TAC [listTheory.MEM] THEN
EXISTS_EQ_TAC THEN
STAC
QED

Theorem MEM_BDS_TO_PROCESS_IMPLIES_WRITE_ADDRESS_NOT_BD_TO_FETCH_LEMMA:
!device_characteristics channel_id memory device1 device2 bd bd_ras bd_was.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  INVARIANT_PROCESS_BD_BD_WRITE_L4 device_characteristics memory device1 /\
  MEM (bd, bd_ras, bd_was) (schannel device1 channel_id).queue.bds_to_process
  ==>
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory device2.dma_state.internal_state bd_was
Proof
INTRO_TAC THEN
REWRITE_TAC [GSYM bd_queuesTheory.CONSISTENT_BD_WRITE] THEN
ETAC INVARIANT_PROCESS_BD_BD_WRITE_L4 THEN
ETAC BD_WRITE THEN
FAIRTAC THEN
IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_BD_WRITE_LEMMA THEN
STAC
QED

Theorem BD_TO_PROCESS_TO_BDS_TO_WRITE_BACK_IMPLIES_BD_MEM_BDS_TO_WRITE_BACK_OR_BDS_TO_PROCESS_LEMMA:
!device_characteristics memory device1 device2 channel_id bd bd_ras bd_was channel1 channel2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  BD_TO_PROCESS_TO_BDS_TO_WRITE_BACK device_characteristics device1 device2 /\
  INVARIANT_PROCESS_BD_BD_WRITE_L4 device_characteristics memory device1 /\
  channel1 = schannel device1 channel_id /\
  channel2 = schannel device2 channel_id /\
  MEM (bd, bd_ras, bd_was) channel2.queue.bds_to_write_back
  ==>
  MEM (bd, bd_ras, bd_was) channel1.queue.bds_to_write_back \/
  MEM (bd, bd_ras, bd_was) channel1.queue.bds_to_process /\
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory device2.dma_state.internal_state bd_was
Proof
INTRO_TAC THEN
ETAC BD_TO_PROCESS_TO_BDS_TO_WRITE_BACK THEN
AITAC THEN
SPLIT_ASM_DISJS_TAC THEN TRY (ALL_RLTAC THEN STAC) THEN
ALL_LRTAC THEN
AXTAC THEN
IRTAC lists_lemmasTheory.MEM_APPEND_LEMMA THEN
SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
ETAC listTheory.MEM THEN
REMOVE_F_DISJUNCTS_TAC THEN
RLTAC THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
RLTAC THEN
ITAC lists_lemmasTheory.MEM_HD_LEMMA THEN
CONJS_TAC THEN TRY STAC THEN
IRTAC MEM_BDS_TO_PROCESS_IMPLIES_WRITE_ADDRESS_NOT_BD_TO_FETCH_LEMMA THEN
STAC
QED

Theorem BDS_TO_FETCH_EQ_IMPLIES_BDS_TO_FETCH_NOT_EXPANDED_LEMMA:
!device_characteristics memory internal_state1 internal_state2.
  BDS_TO_FETCH_EQ device_characteristics memory internal_state1 internal_state2
  ==>
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory internal_state1 internal_state2
Proof
INTRO_TAC THEN
ETAC BDS_TO_FETCH_NOT_EXPANDED THEN
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_FETCH_EQ THEN
AIRTAC THEN
STAC
QED

(*******************************************************************************)

Theorem BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4_LEMMA:
!device_characteristics memory device1 device2.
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4 device_characteristics memory device1
  ==>
  INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4 THEN
INTRO_TAC THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_BDS_TO_FETCH_STRUCTURE_LEMMA THEN
AXTAC THEN
FAIRTAC THEN
STAC
QED

(*******************************************************************************)

Theorem BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4_LEMMA:
!device_characteristics memory device1 device2.
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4 device_characteristics memory device1
  ==>
  INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4 THEN
INTRO_TAC THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_MEM_LEMMA THEN
AIRTAC THEN
IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_DISJOINT_FROM_OTHER_BDS_TO_FETCH_LEMMA THEN
STAC
QED

(*******************************************************************************)

Theorem BDS_TO_UPDATE_NOT_EXPANDED_PRESERVES_INVARIANT_UPDATE_BD_BD_WRITE_L4_LEMMA:
!device_characteristics memory device1 device2.
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  BDS_TO_UPDATE_NOT_EXPANDED device_characteristics device1 device2 /\
  INVARIANT_UPDATE_BD_BD_WRITE_L4 device_characteristics memory device1
  ==>
  INVARIANT_UPDATE_BD_BD_WRITE_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_UPDATE_BD_BD_WRITE_L4 THEN
ETAC BD_WRITE THEN
INTRO_TAC THEN
ITAC BDS_TO_UPDATE_NOT_EXPANDED_PRESERVES_BDS_TO_UPDATE_LEMMA THEN
AITAC THEN
IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_BD_WRITE_LEMMA THEN
STAC
QED

Theorem BDS_TO_FETCH_TO_BDS_TO_UPDATE_PRESERVES_INVARIANT_UPDATE_BD_BD_WRITE_L4_LEMMA:
!device_characteristics memory device1 device2.
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  BD_TO_FETCH_TO_BDS_TO_UPDATE device_characteristics memory device1 device2 /\
  INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4 device_characteristics memory device1 /\
  INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4 device_characteristics memory device1 /\
  INVARIANT_UPDATE_BD_BD_WRITE_L4 device_characteristics memory device1
  ==>
  INVARIANT_UPDATE_BD_BD_WRITE_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_UPDATE_BD_BD_WRITE_L4 THEN
ETAC BD_WRITE THEN
INTRO_TAC THEN
ITAC BD_TO_FETCH_TO_BDS_TO_UPDATE_IMPLIES_BD_MEM_BDS_TO_UPDATE_OR_BDS_TO_FETCH_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AIRTAC THEN IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_BD_WRITE_LEMMA THEN STAC
 ,
 AXTAC THEN ETAC bd_queuesTheory.CONSISTENT_BD_WRITE THEN STAC 
]
QED

(*******************************************************************************)

Theorem BDS_TO_PROCESS_NOT_EXPANDED_PRESERVES_INVARIANT_PROCESS_BD_BD_WRITE_L4_LEMMA:
!device_characteristics memory device1 device2.
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  BDS_TO_PROCESS_NOT_EXPANDED device_characteristics device1 device2 /\
  INVARIANT_PROCESS_BD_BD_WRITE_L4 device_characteristics memory device1
  ==>
  INVARIANT_PROCESS_BD_BD_WRITE_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_PROCESS_BD_BD_WRITE_L4 THEN
ETAC BD_WRITE THEN
INTRO_TAC THEN
ITAC BDS_TO_PROCESS_NOT_EXPANDED_PRESERVES_BDS_TO_PROCESS_LEMMA THEN
AITAC THEN
IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_BD_WRITE_LEMMA THEN
STAC
QED

Theorem BDS_TO_FETCH_TO_BDS_TO_PROCESS_PRESERVES_INVARIANT_PROCESS_BD_BD_WRITE_L4_LEMMA:
!device_characteristics memory device1 device2.
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  BD_TO_FETCH_TO_BDS_TO_PROCESS device_characteristics memory device1 device2 /\
  INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4 device_characteristics memory device1 /\
  INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4 device_characteristics memory device1 /\
  INVARIANT_PROCESS_BD_BD_WRITE_L4 device_characteristics memory device1
  ==>
  INVARIANT_PROCESS_BD_BD_WRITE_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_PROCESS_BD_BD_WRITE_L4 THEN
ETAC BD_WRITE THEN
INTRO_TAC THEN
ITAC BD_TO_FETCH_TO_BDS_TO_PROCESS_IMPLIES_BD_MEM_BDS_TO_PROCESS_OR_BDS_TO_FETCH_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AIRTAC THEN IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_BD_WRITE_LEMMA THEN STAC
 ,
 AXTAC THEN ETAC bd_queuesTheory.CONSISTENT_BD_WRITE THEN STAC 
]
QED

Theorem BDS_TO_UPDATE_TO_BDS_TO_PROCESS_PRESERVES_INVARIANT_PROCESS_BD_BD_WRITE_L4_LEMMA:
!device_characteristics memory device1 device2.
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  BD_TO_UPDATE_TO_BDS_TO_PROCESS device_characteristics device1 device2 /\
  INVARIANT_UPDATE_BD_BD_WRITE_L4 device_characteristics memory device1 /\
  INVARIANT_PROCESS_BD_BD_WRITE_L4 device_characteristics memory device1
  ==>
  INVARIANT_PROCESS_BD_BD_WRITE_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_PROCESS_BD_BD_WRITE_L4 THEN
ETAC BD_WRITE THEN
INTRO_TAC THEN
ETAC BD_TO_UPDATE_TO_BDS_TO_PROCESS THEN
LRTAC THEN
AITAC THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AIRTAC THEN IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_BD_WRITE_LEMMA THEN STAC
 ,
 AXTAC THEN
 IRTAC lists_lemmasTheory.MEM_APPEND_LEMMA THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  AIRTAC THEN IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_BD_WRITE_LEMMA THEN STAC
  ,
  ETAC listTheory.MEM THEN
  REMOVE_F_DISJUNCTS_TAC THEN
  RLTAC THEN
  IRTAC lists_lemmasTheory.MEM_HD_LEMMA THEN
  ETAC INVARIANT_UPDATE_BD_BD_WRITE_L4 THEN
  ETAC BD_WRITE THEN
  AIRTAC THEN
  IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_BD_WRITE_LEMMA THEN
  STAC
 ]
]
QED

(*******************************************************************************)

Theorem BDS_TO_WRITE_BACK_NOT_EXPANDED_PRESERVES_INVARIANT_WRITE_BACK_BD_BD_WRITE_L4_LEMMA:
!device_characteristics memory device1 device2.
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  BDS_TO_WRITE_BACK_NOT_EXPANDED device_characteristics device1 device2 /\
  INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 device_characteristics memory device1
  ==>
  INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 THEN
ETAC BD_WRITE THEN
INTRO_TAC THEN
ITAC BDS_TO_WRITE_BACK_NOT_EXPANDED_PRESERVES_BDS_TO_WRITE_BACK_LEMMA THEN
AITAC THEN
IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_BD_WRITE_LEMMA THEN
STAC
QED

Theorem BDS_TO_PROCESS_TO_BDS_TO_WRITE_BACK_PRESERVES_INVARIANT_WRITE_BACK_BD_BD_WRITE_L4_LEMMA:
!device_characteristics memory device1 device2.
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  BD_TO_PROCESS_TO_BDS_TO_WRITE_BACK device_characteristics device1 device2 /\
  INVARIANT_PROCESS_BD_BD_WRITE_L4 device_characteristics memory device1 /\
  INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 device_characteristics memory device1
  ==>
  INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 THEN
ETAC BD_WRITE THEN
INTRO_TAC THEN
ITAC BD_TO_PROCESS_TO_BDS_TO_WRITE_BACK_IMPLIES_BD_MEM_BDS_TO_WRITE_BACK_OR_BDS_TO_PROCESS_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AIRTAC THEN IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_BD_WRITE_LEMMA THEN STAC
 ,
 ETAC bd_queuesTheory.CONSISTENT_BD_WRITE THEN STAC 
]
QED

(*******************************************************************************)

Theorem BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_INVARIANT_FETCH_BD_DMA_WRITE_L4_LEMMA:
!device_characteristics memory device1 device2.
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state /\
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  INVARIANT_FETCH_BD_DMA_WRITE_L4 device_characteristics memory device1
  ==>
  INVARIANT_FETCH_BD_DMA_WRITE_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_FETCH_BD_DMA_WRITE_L4 THEN
INTRO_TAC THEN
ITAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_MEM_LEMMA THEN
ITAC BD_TRANSFER_WAS_WAS_EQ_PRESERVES_RAS_WAS_LEMMA THEN
AIRTAC THEN
IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA THEN
STAC
QED

(*******************************************************************************)

Theorem BDS_TO_UPDATE_NOT_EXPANDED_PRESERVES_INVARIANT_UPDATE_BD_DMA_WRITE_L4_LEMMA:
!device_characteristics memory device1 device2.
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state /\
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  BDS_TO_UPDATE_NOT_EXPANDED device_characteristics device1 device2 /\
  INVARIANT_UPDATE_BD_DMA_WRITE_L4 device_characteristics memory device1
  ==>
  INVARIANT_UPDATE_BD_DMA_WRITE_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_UPDATE_BD_DMA_WRITE_L4 THEN
ETAC DMA_WRITE THEN
INTRO_TAC THEN
ITAC BDS_TO_UPDATE_NOT_EXPANDED_PRESERVES_BDS_TO_UPDATE_LEMMA THEN
ITAC BD_TRANSFER_WAS_WAS_EQ_PRESERVES_RAS_WAS_LEMMA THEN
AIRTAC THEN
IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA THEN
STAC
QED

Theorem BD_TO_FETCH_TO_BDS_TO_UPDATE_PRESERVES_INVARIANT_UPDATE_BD_DMA_WRITE_L4_LEMMA:
!device_characteristics memory device1 device2.
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state /\
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  BD_TO_FETCH_TO_BDS_TO_UPDATE device_characteristics memory device1 device2 /\
  INVARIANT_FETCH_BD_DMA_WRITE_L4 device_characteristics memory device1 /\
  INVARIANT_UPDATE_BD_DMA_WRITE_L4 device_characteristics memory device1
  ==>
  INVARIANT_UPDATE_BD_DMA_WRITE_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_UPDATE_BD_DMA_WRITE_L4 THEN
ETAC DMA_WRITE THEN
INTRO_TAC THEN
ETAC BD_TO_FETCH_TO_BDS_TO_UPDATE THEN
AITAC THEN
ITAC BD_TRANSFER_WAS_WAS_EQ_PRESERVES_RAS_WAS_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 RLTAC THEN AIRTAC THEN IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA THEN STAC
 ,
 RLTAC THEN
 AXTAC THEN
 IRTAC lists_lemmasTheory.MEM_APPEND_LEMMA THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  AIRTAC THEN IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA THEN STAC
  ,
  ETAC listTheory.MEM THEN
  REMOVE_F_DISJUNCTS_TAC THEN
  RLTAC THEN
  IRTAC lists_lemmasTheory.MEM_HD_LEMMA THEN
  ETAC INVARIANT_FETCH_BD_DMA_WRITE_L4 THEN
  AIRTAC THEN
  IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA THEN
  STAC
 ]
]
QED

(*******************************************************************************)

Theorem BDS_TO_PROCESS_NOT_EXPANDED_PRESERVES_INVARIANT_PROCESS_BD_DMA_WRITE_L4_LEMMA:
!device_characteristics memory device1 device2.
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state /\
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  BDS_TO_PROCESS_NOT_EXPANDED device_characteristics device1 device2 /\
  INVARIANT_PROCESS_BD_DMA_WRITE_L4 device_characteristics memory device1
  ==>
  INVARIANT_PROCESS_BD_DMA_WRITE_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_PROCESS_BD_DMA_WRITE_L4 THEN
ETAC DMA_WRITE THEN
INTRO_TAC THEN
ITAC BDS_TO_PROCESS_NOT_EXPANDED_PRESERVES_BDS_TO_PROCESS_LEMMA THEN
ITAC BD_TRANSFER_WAS_WAS_EQ_PRESERVES_RAS_WAS_LEMMA THEN
AIRTAC THEN
IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA THEN
STAC
QED

Theorem BD_TO_FETCH_TO_BDS_TO_PROCESS_PRESERVES_INVARIANT_PROCESS_BD_DMA_WRITE_L4_LEMMA:
!device_characteristics memory device1 device2.
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state /\
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  BD_TO_FETCH_TO_BDS_TO_PROCESS device_characteristics memory device1 device2 /\
  INVARIANT_FETCH_BD_DMA_WRITE_L4 device_characteristics memory device1 /\
  INVARIANT_PROCESS_BD_DMA_WRITE_L4 device_characteristics memory device1
  ==>
  INVARIANT_PROCESS_BD_DMA_WRITE_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_PROCESS_BD_DMA_WRITE_L4 THEN
ETAC DMA_WRITE THEN
INTRO_TAC THEN
ETAC BD_TO_FETCH_TO_BDS_TO_PROCESS THEN
AITAC THEN
ITAC BD_TRANSFER_WAS_WAS_EQ_PRESERVES_RAS_WAS_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 RLTAC THEN AIRTAC THEN IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA THEN STAC
 ,
 RLTAC THEN
 AXTAC THEN
 IRTAC lists_lemmasTheory.MEM_APPEND_LEMMA THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  AIRTAC THEN IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA THEN STAC
  ,
  ETAC listTheory.MEM THEN
  REMOVE_F_DISJUNCTS_TAC THEN
  RLTAC THEN
  IRTAC lists_lemmasTheory.MEM_HD_LEMMA THEN
  ETAC INVARIANT_FETCH_BD_DMA_WRITE_L4 THEN
  AIRTAC THEN
  IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA THEN
  STAC
 ]
]
QED

Theorem BD_TO_UPDATE_TO_BDS_TO_PROCESS_PRESERVES_INVARIANT_PROCESS_BD_DMA_WRITE_L4_LEMMA:
!device_characteristics memory device1 device2.
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state /\
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory device1.dma_state.internal_state device2.dma_state.internal_state /\
  BD_TO_UPDATE_TO_BDS_TO_PROCESS device_characteristics device1 device2 /\
  INVARIANT_UPDATE_BD_DMA_WRITE_L4 device_characteristics memory device1 /\
  INVARIANT_PROCESS_BD_DMA_WRITE_L4 device_characteristics memory device1
  ==>
  INVARIANT_PROCESS_BD_DMA_WRITE_L4 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_PROCESS_BD_DMA_WRITE_L4 THEN
ETAC DMA_WRITE THEN
INTRO_TAC THEN
ETAC BD_TO_UPDATE_TO_BDS_TO_PROCESS THEN
AITAC THEN
ITAC BD_TRANSFER_WAS_WAS_EQ_PRESERVES_RAS_WAS_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 RLTAC THEN AIRTAC THEN IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA THEN STAC
 ,
 RLTAC THEN
 AXTAC THEN
 IRTAC lists_lemmasTheory.MEM_APPEND_LEMMA THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  AIRTAC THEN IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA THEN STAC
  ,
  ETAC listTheory.MEM THEN
  REMOVE_F_DISJUNCTS_TAC THEN
  RLTAC THEN
  IRTAC lists_lemmasTheory.MEM_HD_LEMMA THEN
  ETAC INVARIANT_UPDATE_BD_DMA_WRITE_L4 THEN
  ETAC DMA_WRITE THEN
  AIRTAC THEN
  IRTAC BDS_TO_FETCH_NOT_EXPANDED_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA THEN
  STAC
 ]
]
QED

(*******************************************************************************)

Theorem CHANNELS_EQ_IMPLIES_BDS_TO_UPDATE_NOT_EXPANDED_LEMMA:
!device_characteristics device1 device2.
  CHANNELS_EQ device1 device2
  ==>
  BDS_TO_UPDATE_NOT_EXPANDED device_characteristics device1 device2
Proof
INTRO_TAC THEN
ETAC BDS_TO_UPDATE_NOT_EXPANDED THEN
ETAC BDS_TO_OPERATE_ON_NOT_EXPANDED THEN
INTRO_TAC THEN
ETAC stateTheory.CHANNELS_EQ THEN
ETAC stateTheory.schannel THEN
RLTAC THEN
RLTAC THEN
LRTAC THEN
REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
QED

Theorem CHANNELS_EQ_IMPLIES_BDS_TO_PROCESS_NOT_EXPANDED_LEMMA:
!device_characteristics device1 device2.
  CHANNELS_EQ device1 device2
  ==>
  BDS_TO_PROCESS_NOT_EXPANDED device_characteristics device1 device2
Proof
INTRO_TAC THEN
ETAC BDS_TO_PROCESS_NOT_EXPANDED THEN
ETAC BDS_TO_OPERATE_ON_NOT_EXPANDED THEN
INTRO_TAC THEN
ETAC stateTheory.CHANNELS_EQ THEN
ETAC stateTheory.schannel THEN
RLTAC THEN
RLTAC THEN
LRTAC THEN
REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
QED

Theorem CHANNELS_EQ_IMPLIES_BDS_TO_WRITE_BACK_NOT_EXPANDED_LEMMA:
!device_characteristics device1 device2.
  CHANNELS_EQ device1 device2
  ==>
  BDS_TO_WRITE_BACK_NOT_EXPANDED device_characteristics device1 device2
Proof
INTRO_TAC THEN
ETAC BDS_TO_WRITE_BACK_NOT_EXPANDED THEN
ETAC BDS_TO_OPERATE_ON_NOT_EXPANDED THEN
INTRO_TAC THEN
ETAC stateTheory.CHANNELS_EQ THEN
ETAC stateTheory.schannel THEN
RLTAC THEN
RLTAC THEN
LRTAC THEN
REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
QED

Theorem BDS_TO_FETCH_NOT_EXPANDED_REFL_LEMMA:
!device_characteristics memory internal_state.
  BDS_TO_FETCH_NOT_EXPANDED device_characteristics memory memory internal_state internal_state
Proof
REPEAT GEN_TAC THEN
ETAC BDS_TO_FETCH_NOT_EXPANDED THEN
INTRO_TAC THEN
STAC
QED

val _ = export_theory();
