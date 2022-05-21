open HolKernel Parse boolLib bossLib helper_tactics;
open l3Theory invariant_l3Theory;

val _ = new_theory "fetching_bd_l3_preserves_invariant_concrete_l3_lemmas";

Theorem FETCHING_BD_L3_PRESERVING_REQUESTS_OR_ADDING_READ_REQUEST_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  (channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd \/
   channel2.pending_accesses.requests.fetching_bd = NONE \/
   ?addresses tag. channel2.pending_accesses.requests.fetching_bd = SOME (request_read addresses tag)) /\
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC l3Theory.fetching_bd_l3 THENL
[
 PTAC concreteTheory.fetching_bd_fetch_bd_concrete THENL
 [
  PTAC operationsTheory.append_bds_to_process THEN EQ_PAIR_ASM_TAC THEN LRTAC THEN RECORD_TAC THEN STAC
  ,
  EQ_PAIR_ASM_TAC THEN PTAC operationsTheory.append_bds_to_update THEN LRTAC THEN RECORD_TAC THEN STAC
  ,
  EQ_PAIR_ASM_TAC THEN STAC
 ]
 ,
 EQ_PAIR_ASM_TAC THEN
 PTAC operationsTheory.fetching_bd_set_request THEN TRY STAC THEN
 LRTAC THEN
 RECORD_TAC THEN
 CONJS_TAC THEN TRY STAC THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 EXISTS_EQ_TAC
 ,
 PTAC concreteTheory.fetching_bd_fetch_bd_concrete THENL
 [
  EQ_PAIR_ASM_TAC THEN
  PTAC operationsTheory.append_bds_to_process THEN
  PTAC operationsTheory.fetching_bd_clear_reply THEN
  LRTAC THEN
  LRTAC THEN
  RECORD_TAC THEN
  STAC
  ,
  EQ_PAIR_ASM_TAC THEN
  PTAC operationsTheory.append_bds_to_update THEN
  PTAC operationsTheory.fetching_bd_clear_reply THEN
  LRTAC THEN
  LRTAC THEN
  RECORD_TAC THEN
  STAC
  ,
  EQ_PAIR_ASM_TAC THEN
  RLTAC THEN
  RLTAC THEN
  PTAC operationsTheory.fetching_bd_clear_reply THEN
  LRTAC THEN
  RECORD_TAC THEN
  STAC
 ]
]
QED

Theorem FETCHING_BD_L3_NOT_ADDING_WRITE_REQUEST_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  !address_bytes tag.
    MEM (request_write address_bytes tag) (channel_pending_requests channel2.pending_accesses.requests)
    ==>
    MEM (request_write address_bytes tag) (channel_pending_requests channel1.pending_accesses.requests) 
Proof
INTRO_TAC THEN
INTRO_TAC THEN
IRTAC FETCHING_BD_L3_PRESERVING_REQUESTS_OR_ADDING_READ_REQUEST_LEMMA THEN
ETAC operationsTheory.channel_pending_requests THEN
SPLIT_ASM_DISJS_TAC THEN ALL_LRTAC THEN TRY STAC THENL
[
 REPEAT (PTAC operationsTheory.collect_pending_fetch_bd_request) THENL
 [
  ETAC listTheory.MEM_APPEND THEN
  SPLIT_ASM_DISJS_TAC THEN
   STAC
  ,
  ETAC listTheory.MEM_APPEND THEN
  SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
  ETAC listTheory.MEM THEN
  SOLVE_F_ASM_TAC
 ]
 ,
 AXTAC THEN
 LRTAC THEN
 REPEAT (PTAC operationsTheory.collect_pending_fetch_bd_request) THEN
  ETAC listTheory.MEM_APPEND THEN
  SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
   ETAC listTheory.MEM THEN REMOVE_F_DISJUNCTS_TAC THEN IRTAC stateTheory.interconnect_request_type_distinct THEN SOLVE_F_ASM_TAC
]
QED

Theorem FETCHING_BD_L3_PRESERVES_MEM_WRITE_REQUESTS_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 address_bytes tag
 channel1 channel2 requests1 requests2 device1 device2 write_requests1 write_requests2.
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  requests2 = channel_requests device_characteristics device2 /\
  requests1 = channel_requests device_characteristics device1 /\
  write_requests2 = FILTER WRITE_REQUEST requests2 /\
  write_requests1 = FILTER WRITE_REQUEST requests1 /\
  MEM (request_write address_bytes tag) write_requests2
  ==>
  MEM (request_write address_bytes tag) write_requests1
Proof
INTRO_TAC THEN
IRTAC invariant_l3_lemmasTheory.MEM_FILTER_WRITE_REQUEST_IMPLIES_REQUEST_LEMMA THEN
IRTAC (REWRITE_RULE [GSYM stateTheory.schannel] dma_pending_requests_lemmasTheory.MEM_DMA_PENDING_REQUESTS_CHANNELS_IMP_SOME_VALID_CHANNEL_LEMMA) THEN
AXTAC THEN
Cases_on ‘channel_id = channel_id'’ THENL
[
 RLTAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA THEN
 ALL_LRTAC THEN
 IRTAC FETCHING_BD_L3_NOT_ADDING_WRITE_REQUEST_LEMMA THEN
 RW_HYPS_TAC operationsTheory.channel_pending_requests THEN
 ETAC operationsTheory.collect_pending_requests THEN
 EQ_PAIR_ASM_TAC THEN
 ALL_LRTAC THEN
 AIRTAC THEN
 IRTAC (REWRITE_RULE [operationsTheory.channel_pending_requests] invariant_l3_lemmasTheory.WRITE_REQUEST_IN_CHANNEL_REQUESTS_IMPLIES_IN_CHANNEL_WRITE_REQUESTS_LEMMA) THEN
 STAC
 ,
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN
 PAT_X_ASSUM “x <> y” (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [boolTheory.EQ_SYM_EQ] thm)) THEN
 AIRTAC THEN
 LRTAC THEN
 LRTAC THEN
 PTAC operationsTheory.collect_pending_requests THEN
 EQ_PAIR_ASM_TAC THEN
 NLRTAC 4 THEN
 IRTAC (REWRITE_RULE [operationsTheory.channel_pending_requests] invariant_l3_lemmasTheory.WRITE_REQUEST_IN_CHANNEL_REQUESTS_IMPLIES_IN_CHANNEL_WRITE_REQUESTS_LEMMA) THEN
 STAC
]
QED

Theorem FETCHING_BD_L3_PRESERVES_WRITE_REQUESTS_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2
 channel1 channel2 requests1 requests2 device1 device2 write_requests1 write_requests2.
  channel1 = schannel device1 channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  requests1 = channel_requests device_characteristics device1 /\
  requests2 = channel_requests device_characteristics device2 /\
  write_requests1 = FILTER WRITE_REQUEST requests1 /\
  write_requests2 = FILTER WRITE_REQUEST requests2
  ==>
  CHANNEL_SET write_requests2 SUBSET CHANNEL_SET write_requests1
Proof
INTRO_TAC THEN
ETAC pred_setTheory.SUBSET_DEF THEN
ETAC CHANNEL_SET THEN
ETAC invariant_l3_lemmasTheory.SET_ETA_LEMMA THEN
ETAC pred_setTheory.GSPEC_ETA THEN
REWRITE_TAC [invariant_l3_lemmasTheory.IN_MEM_ABS_EQ_MEM_LEMMA] THEN
INTRO_TAC THEN
FITAC invariant_l3_lemmasTheory.MEM_WRITE_REQUESTS_IMPLIES_WRITE_REQUEST_LEMMA THEN
AXTAC THEN
LRTAC THEN
IRTAC FETCHING_BD_L3_PRESERVES_MEM_WRITE_REQUESTS_LEMMA THEN
STAC
QED

Theorem FETCHING_BD_L3_NOT_ADDING_WRITE_REQUESTS_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2
 channel1 channel2 channel_id requests1 requests2 requests_was1 requests_was2 was.
  channel1 = schannel device1 channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  requests1 = channel_requests device_characteristics device1 /\
  requests2 = channel_requests device_characteristics device2 /\
  requests_was1 = MAP request_to_write_addresses requests1 /\
  requests_was2 = MAP request_to_write_addresses requests2 /\
  MEM was requests_was2
  ==>
  MEM was requests_was1 \/ was = []
Proof
INTRO_TAC THEN
ITAC FETCHING_BD_L3_PRESERVES_WRITE_REQUESTS_LEMMA THEN
FIRTAC invariant_l3_lemmasTheory.NO_WRITE_ADDRESSES_OR_WRITE_REQUEST_LEMMA THEN
SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
AXTAC THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
IRTAC invariant_l3_lemmasTheory.WRITE_REQUEST_SUBSET_TRANSFERS_MEMBER_LEMMA THEN
STAC
QED

Theorem FETCHING_BD_UPDATING_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  (!channel_id memory.
     VALID_CHANNEL_ID device_characteristics channel_id
     ==>
     (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 =
     (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2) \/
  ?fetch_result.
    ((internal_state2, SOME fetch_result) = (coperation device_characteristics channel_id).fetch_bd internal_state1 NONE /\
     INTERNAL_BDS device_characteristics) \/
    (?reply.
       (internal_state2, SOME fetch_result) = (coperation device_characteristics channel_id).fetch_bd internal_state1 (SOME reply) /\
       channel1.pending_accesses.replies.fetching_bd = SOME reply /\
       EXTERNAL_BDS device_characteristics)
Proof
INTRO_TAC THEN
PTAC fetching_bd_l3 THENL
[
 PTAC concreteTheory.fetching_bd_fetch_bd_concrete THENL
 [
  EQ_PAIR_ASM_TAC THEN RLTAC THEN MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN PAXTAC THEN STAC
  ,
  EQ_PAIR_ASM_TAC THEN RLTAC THEN MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN PAXTAC THEN STAC
  ,
  EQ_PAIR_ASM_TAC THEN RLTAC THEN MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
  INTRO_TAC THEN
  Cases_on ‘channel_id = channel_id'’ THENL
  [
   RLTAC THEN PTAC proof_obligationsTheory.PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT THEN AIRTAC THEN STAC
   ,
   PTAC proof_obligationsTheory.PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE THEN FAIRTAC THEN AIRTAC THEN STAC
  ]
 ]
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
 IRTAC fetching_bd_lemmasTheory.NOT_IS_NONE_IMPLIES_EXISTS_SOME_LEMMA THEN
 AXTAC THEN
 LRTAC THEN
 LRTAC THEN
 PTAC concreteTheory.fetching_bd_fetch_bd_concrete THENL
 [
  EQ_PAIR_ASM_TAC THEN
  RLTAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  PAXTAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  PAXTAC THEN STAC
  ,
  EQ_PAIR_ASM_TAC THEN
  RLTAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  PAXTAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  PAXTAC THEN STAC
  ,
  EQ_PAIR_ASM_TAC THEN RLTAC THEN MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
  INTRO_TAC THEN
  Cases_on ‘channel_id = channel_id'’ THENL
  [
   RLTAC THEN PTAC proof_obligationsTheory.PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT THEN AIRTAC THEN STAC
   ,
   PTAC proof_obligationsTheory.PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE THEN FAIRTAC THEN AIRTAC THEN STAC
  ]
 ]
]
QED

Theorem FETCHING_BD_L3_PRESERVES_BDS_TO_FETCH_OR_REMOVES_HEAD_LEMMA:
!device_characteristics memory internal_state1 internal_state2
 channel1 channel2 channel_id bds_to_fetch.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  EXTERNAL_BD_ADDRESSES device_characteristics channel_id memory internal_state1 channel1 /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BDS_TO_FETCH_DISJOINT bds_to_fetch /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  !channel_id bds_to_fetch1 bds_to_fetch2.
    VALID_CHANNEL_ID device_characteristics channel_id /\
    bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
    bds_to_fetch2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2
    ==>
    bds_to_fetch2 = bds_to_fetch1 \/
    ?bd. bd::bds_to_fetch2 = bds_to_fetch1
Proof
INTRO_TAC THEN
ITAC FETCHING_BD_UPDATING_BDS_TO_FETCH_LEMMA THEN
SPLIT_ASM_DISJS_TAC THEN TRY (INTRO_TAC THEN AIRTAC THEN STAC) THEN
AXTAC THEN
INTRO_TAC THEN
Cases_on ‘channel_id = channel_id'’ THENL
[
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 RLTAC THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  ITAC fetching_bd_lemmasTheory.FETCHING_BD_IMPLIES_NON_EMPTY_BDS_TO_FETCH_LEMMA THEN
  PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC (mk_var ("memory", (type_of o #1 o dest_forall o concl) thm)) thm)) THEN AXTAC THEN
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT THEN
  Q.EXISTS_TAC ‘bd’ THEN
  AIRTAC THEN
  AITAC THEN
  LRTAC THEN
  NLRTAC 2 THEN
  AIRTAC THEN
  LRTAC THEN
  LRTAC THEN
  STAC
  ,
  AXTAC THEN
  ITAC fetching_bd_lemmasTheory.FETCHING_BD_IMPLIES_NON_EMPTY_BDS_TO_FETCH_LEMMA THEN
  PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC (mk_var ("memory", (type_of o #1 o dest_forall o concl) thm)) thm)) THEN AXTAC THEN
  ASSUME_TAC (SPEC_ALL fetching_bd_lemmasTheory.FETCH_BD_ADDRESSES_EQ_ADDRESSES_TAG_LEMMA) THEN
  AXTAC THEN
  Q.EXISTS_TAC ‘bd’ THEN
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT THEN
  PTAC EXTERNAL_BD_ADDRESSES THEN
  AITAC THEN
  AIRTAC THEN
  AITAC THEN
  PAT_X_ASSUM “bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1” (fn thm => ASSUME_TAC thm THEN RLTAC THEN RLTAC THEN LRTAC) THEN
  AIRTAC THEN
  LRTAC THEN
  STAC
 ]
 ,
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  FAIRTAC THEN AIRTAC THEN STAC
  ,
  AXTAC THEN FAIRTAC THEN AIRTAC THEN STAC
 ]
]
QED

Theorem BDS_TO_FETCH_DISJOINT_IMPLIES_TAIL_BDS_TO_FETCH_DISJOINT_LEMMA:
!h t.
  BDS_TO_FETCH_DISJOINT (h::t)
  ==>
  BDS_TO_FETCH_DISJOINT t
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.BDS_TO_FETCH_DISJOINT THEN
INTRO_TAC THEN
RLTAC THEN
PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (Q.SPECL [‘bd1’, ‘bd_ras1’, ‘bd_was1’, ‘uf1’] thm)) THEN
PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (Q.SPECL [‘bd2’, ‘bd_ras2’, ‘bd_was2’, ‘uf2’] thm)) THEN
PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (Q.SPECL [‘h::preceding_bds’, ‘following_bds’] thm)) THEN
INST_IMP_ASM_GOAL_TAC THEN
ETAC listTheory.APPEND THEN
ETAC listTheory.MEM THEN
STAC
QED

Theorem FETCHING_BD_L3_NOT_ADDING_BDS_TO_FETCH_LEMMA:
!device_characteristics memory internal_state1 internal_state2
 channel1 channel2 channel_id bds_to_fetch.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  EXTERNAL_BD_ADDRESSES device_characteristics channel_id memory internal_state1 channel1 /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BDS_TO_FETCH_DISJOINT bds_to_fetch /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  !channel_id bds_to_fetch1 bds_to_fetch2 bd.
    VALID_CHANNEL_ID device_characteristics channel_id /\
    bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
    bds_to_fetch2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2 /\
    MEM bd bds_to_fetch2
    ==>
    MEM bd bds_to_fetch1
Proof
INTRO_TAC THEN
INTRO_TAC THEN
ITAC FETCHING_BD_L3_PRESERVES_BDS_TO_FETCH_OR_REMOVES_HEAD_LEMMA THEN
AIRTAC THEN
SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
AXTAC THEN
RLTAC THEN
ASM_REWRITE_TAC [listTheory.MEM]
QED

Theorem FETCHING_BD_L3_PRESERVES_WRITE_ADDRESS_NOT_BD_TO_FETCH_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 was bds_to_fetch.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  EXTERNAL_BD_ADDRESSES device_characteristics channel_id memory internal_state1 channel1 /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BDS_TO_FETCH_DISJOINT bds_to_fetch /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory internal_state1 was
  ==>
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory internal_state2 was
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
INTRO_TAC THEN
ITAC FETCHING_BD_L3_NOT_ADDING_BDS_TO_FETCH_LEMMA THEN
AITAC THEN
AIRTAC THEN
STAC
QED

Theorem FETCHING_BD_UPDATING_INTERNAL_STATE_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  internal_state2 = internal_state1 \/
  ?reply fetch_result.
    (internal_state2, fetch_result) = (coperation device_characteristics channel_id).fetch_bd internal_state1 reply
Proof
INTRO_TAC THEN
PTAC fetching_bd_l3 THENL
[
 PTAC concreteTheory.fetching_bd_fetch_bd_concrete THEN
  EQ_PAIR_ASM_TAC THEN MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN PAXTAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 PTAC concreteTheory.fetching_bd_fetch_bd_concrete THEN
  EQ_PAIR_ASM_TAC THEN MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN PAXTAC THEN STAC 
]
QED

Theorem FETCHING_BD_L3_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 was bds_to_fetch.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  EXTERNAL_BD_ADDRESSES device_characteristics channel_id memory internal_state1 channel1 /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BDS_TO_FETCH_DISJOINT bds_to_fetch /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  CONSISTENT_DMA_WRITE device_characteristics memory internal_state1 was
  ==>
  CONSISTENT_DMA_WRITE device_characteristics memory internal_state2 was
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.CONSISTENT_DMA_WRITE THEN
INTRO_TAC THEN
AIRTAC THEN
ITAC FETCHING_BD_L3_PRESERVES_WRITE_ADDRESS_NOT_BD_TO_FETCH_LEMMA THEN
STAC
QED

Theorem FETCHING_BD_L3_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id bds_to_fetch.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device1 /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  BDS_TO_FETCH_DISJOINT bds_to_fetch /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device1
  ==>
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC NO_MEMORY_WRITES_TO_BDS THEN
INTRO_TAC THEN
ITAC FETCHING_BD_L3_NOT_ADDING_WRITE_REQUESTS_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AIRTAC THEN
 ITAC invariant_l3_lemmasTheory.INVARIANT_EXTERNAL_FETCH_BD_REPLY_IMPLIES_EXTERNAL_BD_ADDRESSES_LEMMA THEN
 IRTAC FETCHING_BD_L3_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 STAC
 ,
 LRTAC THEN
 REWRITE_TAC [bd_queues_lemmasTheory.CONSISTENT_DMA_WRITE_EMPTY_WRITE_ADDRESSES_LEMMA]
] 
QED



(*******************************************************************************)

Theorem FETCHING_BD_L3_PRESERVES_INTERNAL_STATE_OR_FETCHES_PARITAL_BD_OR_FETCHES_COMPLETE_BD_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  EXTERNAL_BD_ADDRESSES device_characteristics channel_id memory internal_state1 channel1 /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  (EXTERNAL_BDS device_characteristics /\ IS_NONE channel1.pending_accesses.replies.fetching_bd) \/
  (INTERNAL_BDS device_characteristics /\
   (internal_state2, NONE) = (coperation device_characteristics channel_id).fetch_bd internal_state1 NONE) \/
  (EXTERNAL_BDS device_characteristics /\
   (internal_state2, NONE) = (coperation device_characteristics channel_id).fetch_bd internal_state1 channel1.pending_accesses.replies.fetching_bd) \/
  (?bd. INTERNAL_BD_FETCH device_characteristics channel_id internal_state1 internal_state2 bd /\
        EXTERNAL_BD_FETCH device_characteristics memory channel_id internal_state1 channel1 internal_state2 bd)
Proof
INTRO_TAC THEN
PTAC fetching_bd_l3 THENL
[
 PTAC concreteTheory.fetching_bd_fetch_bd_concrete THENL
 [
  REPEAT (MATCH_MP_TAC boolTheory.OR_INTRO_THM2) THEN
  REWRITE_TAC [EXTERNAL_BD_FETCH] THEN
  ITAC state_lemmasTheory.INTERNAL_BDS_IMPLIES_NOT_EXTERNAL_BDS_LEMMA THEN
  ASM_REWRITE_TAC [] THEN
  ASM_REWRITE_TAC [INTERNAL_BD_FETCH] THEN
  EQ_PAIR_ASM_TAC THEN
  RLTAC THEN
  EXISTS_EQ_TAC
  ,
  REPEAT (MATCH_MP_TAC boolTheory.OR_INTRO_THM2) THEN
  REWRITE_TAC [EXTERNAL_BD_FETCH] THEN
  ITAC state_lemmasTheory.INTERNAL_BDS_IMPLIES_NOT_EXTERNAL_BDS_LEMMA THEN
  ASM_REWRITE_TAC [] THEN
  ASM_REWRITE_TAC [INTERNAL_BD_FETCH] THEN
  EQ_PAIR_ASM_TAC THEN
  RLTAC THEN
  EXISTS_EQ_TAC
  ,
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN EQ_PAIR_ASM_TAC THEN STAC
 ]
 ,
 IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN STAC
 ,
 PTAC concreteTheory.fetching_bd_fetch_bd_concrete THENL
 [
  REPEAT (MATCH_MP_TAC boolTheory.OR_INTRO_THM2) THEN
  EQ_PAIR_ASM_TAC THEN
  RLTAC THEN
  ITAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
  REWRITE_TAC [INTERNAL_BD_FETCH] THEN
  ITAC state_lemmasTheory.EXTERNAL_BDS_IMPLIES_NOT_INTERNAL_BDS_LEMMA THEN
  ASM_REWRITE_TAC [EXTERNAL_BD_FETCH] THEN
  IRTAC fetching_bd_lemmasTheory.NOT_IS_NONE_IMPLIES_EXISTS_SOME_LEMMA THEN
  AXTAC THEN
  ETAC EXTERNAL_BD_ADDRESSES THEN
  ASSUME_TAC (SPEC_ALL fetching_bd_lemmasTheory.FETCH_BD_ADDRESSES_EQ_ADDRESSES_TAG_LEMMA) THEN
  AXTAC THEN
  AITAC THEN
  PAXTAC THEN
  LRTAC THEN
  STAC
  ,
  REPEAT (MATCH_MP_TAC boolTheory.OR_INTRO_THM2) THEN
  EQ_PAIR_ASM_TAC THEN
  RLTAC THEN
  ITAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
  REWRITE_TAC [INTERNAL_BD_FETCH] THEN
  ITAC state_lemmasTheory.EXTERNAL_BDS_IMPLIES_NOT_INTERNAL_BDS_LEMMA THEN
  ASM_REWRITE_TAC [EXTERNAL_BD_FETCH] THEN
  IRTAC fetching_bd_lemmasTheory.NOT_IS_NONE_IMPLIES_EXISTS_SOME_LEMMA THEN
  AXTAC THEN
  ETAC EXTERNAL_BD_ADDRESSES THEN
  ASSUME_TAC (SPEC_ALL fetching_bd_lemmasTheory.FETCH_BD_ADDRESSES_EQ_ADDRESSES_TAG_LEMMA) THEN
  AXTAC THEN
  AITAC THEN
  PAXTAC THEN
  LRTAC THEN
  STAC
  ,
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
  IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
  EQ_PAIR_ASM_TAC THEN
  STAC
 ]
]
QED

Theorem FETCHING_BD_L3_PRESERVES_BD_QUEUES_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  EXTERNAL_BDS device_characteristics /\
  IS_NONE channel1.pending_accesses.replies.fetching_bd /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  internal_state2 = internal_state1 /\
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC fetching_bd_l3 THENL
[
 IRTAC state_lemmasTheory.EXTERNAL_BDS_IMPLIES_NOT_INTERNAL_BDS_LEMMA THEN CONTR_ASMS_TAC
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 PTAC operationsTheory.fetching_bd_set_request THEN TRY STAC THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
]
QED

Theorem FETCHING_BD_L3_NO_BD_PRESERVES_BD_QUEUES_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 bds_to_fetch1 bds_to_fetch2.
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  INTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  (internal_state2, NONE) = (coperation device_characteristics channel_id).fetch_bd internal_state1 NONE /\
  bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  bds_to_fetch2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2
  ==>
  bds_to_fetch2 = bds_to_fetch1 /\
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC fetching_bd_l3 THEN
PTAC concreteTheory.fetching_bd_fetch_bd_concrete THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 2 THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT THEN
AIRTAC THEN
STAC
QED

Theorem FETCHING_BD_L3_NO_BD_PRESERVES_BD_QUEUES_EXTERNAL_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 bds_to_fetch1 bds_to_fetch2.
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  (internal_state2, NONE) = (coperation device_characteristics channel_id).fetch_bd internal_state1 channel1.pending_accesses.replies.fetching_bd /\
  bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  bds_to_fetch2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2
  ==>
  bds_to_fetch2 = bds_to_fetch1 /\
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC fetching_bd_l3 THENL
[
 IRTAC state_lemmasTheory.EXTERNAL_BDS_IMPLIES_NOT_INTERNAL_BDS_LEMMA THEN CONTR_ASMS_TAC
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 PTAC operationsTheory.fetching_bd_set_request THEN TRY STAC THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 PTAC concreteTheory.fetching_bd_fetch_bd_concrete THENL
 [
  ALL_LRTAC THEN EQ_PAIR_ASM_TAC THEN IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC
  ,
  ALL_LRTAC THEN EQ_PAIR_ASM_TAC THEN IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC
  ,
  EQ_PAIR_ASM_TAC THEN
  NRLTAC 2 THEN
  PTAC operationsTheory.fetching_bd_clear_reply THEN
  LRTAC THEN
  RECORD_TAC THEN
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT THEN
  AIRTAC THEN
  STAC
 ]
]
QED

Theorem FETCHING_BD_L3_NOT_ADDING_BDS_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2
 channel1 channel2 channel_bd_queues1 channel_bd_queues2 bds_to_fetch1 bds_to_fetch2.
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  EXTERNAL_BD_ADDRESSES device_characteristics channel_id memory internal_state1 channel1 /\
  BDS_TO_FETCH_DISJOINT bds_to_fetch1 /\
  bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  bds_to_fetch2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2 /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  channel_bd_queues1 = channel_bd_queues device_characteristics channel_id memory internal_state1 channel1 /\
  channel_bd_queues2 = channel_bd_queues device_characteristics channel_id memory internal_state2 channel2
  ==>
  CHANNEL_SET channel_bd_queues2 SUBSET CHANNEL_SET channel_bd_queues1
Proof
INTRO_TAC THEN
ETAC CHANNEL_SET THEN
ETAC pred_setTheory.SUBSET_DEF THEN
REWRITE_TAC [invariant_l3_lemmasTheory.SET_ETA_LEMMA, pred_setTheory.GSPEC_ETA, invariant_l3_lemmasTheory.IN_MEM_ABS_EQ_MEM_LEMMA] THEN
INTRO_TAC THEN
ETAC channel_bd_queues THEN
LETS_TAC THEN
ITAC FETCHING_BD_L3_PRESERVES_INTERNAL_STATE_OR_FETCHES_PARITAL_BD_OR_FETCHES_COMPLETE_BD_LEMMA THEN
SPLIT_ASM_DISJS_TAC THEN1
 (IRTAC FETCHING_BD_L3_PRESERVES_BD_QUEUES_LEMMA THEN ALL_LRTAC THEN STAC) THEN1
 (ITAC FETCHING_BD_L3_NO_BD_PRESERVES_BD_QUEUES_LEMMA THEN ALL_LRTAC THEN STAC) THEN1
 (ITAC FETCHING_BD_L3_NO_BD_PRESERVES_BD_QUEUES_EXTERNAL_LEMMA THEN ALL_LRTAC THEN STAC) THEN
AXTAC THEN
ITAC fetching_bd_lemmasTheory.FETCHING_BD_L3_BD_SHIFTS_BD_QUEUES_LEMMA THEN
PAT_X_ASSUM “bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1” (fn thm => ASSUME_TAC thm THEN RLTAC) THEN
PAT_X_ASSUM “bds_to_fetch2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2” (fn thm => ASSUME_TAC thm THEN RLTAC) THEN
IRTAC listTheory.CONS THEN
RLTAC THEN
WEAKEN_TAC (fn _ => true) THEN
PAT_X_ASSUM “VALID_CHANNEL_ID device_characteristics channel_id” (fn _ => ALL_TAC) THEN
PAT_X_ASSUM “PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics” (fn _ => ALL_TAC) THEN
PAT_X_ASSUM “PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics” (fn _ => ALL_TAC) THEN
PAT_X_ASSUM “PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics” (fn _ => ALL_TAC) THEN
PAT_X_ASSUM “PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics” (fn _ => ALL_TAC) THEN
PAT_X_ASSUM “PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics” (fn _ => ALL_TAC) THEN
PAT_X_ASSUM “PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics” (fn _ => ALL_TAC) THEN
ETAC listTheory.HD THEN
ETAC listTheory.TL THEN
PAT_X_ASSUM “EXTERNAL_BD_FETCH device_characteristics memory channel_id internal_state1 channel1 internal_state2 bd” (fn _ => ALL_TAC) THEN
PAT_X_ASSUM “INTERNAL_BD_FETCH device_characteristics channel_id internal_state1 internal_state2 bd” (fn _ => ALL_TAC) THEN
PAT_X_ASSUM “EXTERNAL_BD_ADDRESSES device_characteristics channel_id memory internal_state1 channel1” (fn _ => ALL_TAC) THEN
ALL_LRTAC THEN
ETAC listTheory.MEM_APPEND THEN
WEAKEN_TAC is_eq THEN
ETAC listTheory.MAP THEN
ETAC listTheory.MEM THEN
SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
 LRTAC THEN ETAC listTheory.MEM_APPEND THEN ETAC listTheory.MEM THEN REMOVE_F_DISJUNCTS_TAC THEN SPLIT_ASM_DISJS_TAC THEN STAC
QED

Theorem FETCHING_BD_L3_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA:
!device_characteristics channel_id memory device1 device2 internal_state1 internal_state2 channel1 channel2.
  PROOF_OBLIGATION_FETCHING_BD_PRESERVES_BD_INTERPRETATION device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
IRTAC FETCHING_BD_UPDATING_INTERNAL_STATE_LEMMA THEN
ETAC stateTheory.BD_TRANSFER_RAS_WAS_EQ THEN
SPLIT_ASM_DISJS_TAC THENL
[
 RLTAC THEN LRTAC THEN IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN STAC
 ,
 AXTAC THEN
 ETAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHING_BD_PRESERVES_BD_INTERPRETATION THEN
 AIRTAC THEN
 RLTAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 LRTAC THEN
 INTRO_TAC THEN
 AIRTAC THEN
 STAC
]
QED

Theorem FETCHING_BD_L3_IMPLIES_OTHER_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics channel_id memory device1 device2 internal_state1 internal_state2 channel1 channel2.
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  OTHER_BDS_TO_FETCH_EQ device_characteristics channel_id memory internal_state1 internal_state2
Proof
INTRO_TAC THEN
IRTAC FETCHING_BD_UPDATING_INTERNAL_STATE_LEMMA THEN
ETAC stateTheory.OTHER_BDS_TO_FETCH_EQ THEN
SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
AXTAC THEN
ETAC proof_obligationsTheory.PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE THEN
INTRO_TAC THEN
PAT_X_ASSUM “channel_id' <> channel_id” (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [boolTheory.EQ_SYM_EQ] thm)) THEN
FAIRTAC THEN
AIRTAC THEN
STAC
QED

Theorem FETCHING_BD_L3_PRESERVES_INVARIANT_BDS_TO_FETCH_DISJOINT_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device1 /\
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device1
  ==>
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC invariant_l3Theory.INVARIANT_BDS_TO_FETCH_DISJOINT THEN
ITAC invariant_l3_lemmasTheory.INVARIANT_EXTERNAL_FETCH_BD_REPLY_IMPLIES_EXTERNAL_BD_ADDRESSES_LEMMA THEN
INTRO_TAC THEN
Cases_on ‘channel_id = channel_id'’ THENL
[
 RLTAC THEN
 AITAC THEN
 RLTAC THEN
 ITAC FETCHING_BD_L3_PRESERVES_BDS_TO_FETCH_OR_REMOVES_HEAD_LEMMA THEN
 FAIRTAC THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  LRTAC THEN IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN LRTAC THEN RLTAC THEN STAC
  ,
  AXTAC THEN
  RLTAC THEN
  IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
  LRTAC THEN
  RLTAC THEN
  IRTAC BDS_TO_FETCH_DISJOINT_IMPLIES_TAIL_BDS_TO_FETCH_DISJOINT_LEMMA THEN
  STAC
 ]
 ,
 FITAC FETCHING_BD_L3_IMPLIES_OTHER_BDS_TO_FETCH_EQ_LEMMA THEN
 ETAC stateTheory.OTHER_BDS_TO_FETCH_EQ THEN
 AITAC THEN
 AIRTAC THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN RLTAC THEN
 STAC
]
QED

Theorem FETCHING_BD_L3_PRESERVES_NOT_DMA_BDS_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id bds_to_fetch.
  PROOF_OBLIGATION_FETCHING_BD_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device1 /\
  internal_state1 = device1.dma_state.internal_state /\
  BDS_TO_FETCH_DISJOINT bds_to_fetch /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  channel1 = schannel device1 channel_id /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  NOT_DMA_BDS device_characteristics memory device1
  ==>
  NOT_DMA_BDS device_characteristics memory device2
Proof
REWRITE_TAC [NOT_DMA_BDS, GSYM invariant_l3_lemmasTheory.CHANNEL_BD_QUEUES_EQ_CHANNEL_BDS_LEMMA] THEN
INTRO_TAC THEN
ITAC invariant_l3_lemmasTheory.INVARIANT_EXTERNAL_FETCH_BD_REPLY_IMPLIES_EXTERNAL_BD_ADDRESSES_LEMMA THEN
INTRO_TAC THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC_ALL thm)) THEN
INST_IMP_ASM_GOAL_TAC THEN
CONJS_TAC THEN TRY STAC THENL
[
 FITAC FETCHING_BD_L3_IMPLIES_OTHER_BDS_TO_FETCH_EQ_LEMMA THEN
 FITAC FETCHING_BD_L3_NOT_ADDING_BDS_LEMMA THEN
 ITAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 RLTAC THEN
 ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_CHANNEL_EQ_LEMMA THEN
 FIRTAC invariant_l3_lemmasTheory.UPDATE_DEVICE_STATE_NOT_ADDING_BDS_LEMMA THEN
 ITAC invariant_l3_lemmasTheory.CHANNEL_BD_QUEUES_SUBSET_TRANSFERS_MEM_LEMMA THEN
 STAC
 ,
 FIRTAC FETCHING_BD_L3_IMPLIES_BD_TRANSFER_RAS_WAS_EQ_LEMMA THEN 
 IRTAC invariant_l3_lemmasTheory.BD_TRANSFER_RAS_WAS_PRESERVES_BD_DMA_WRITE_ADDRESSES_LEMMA THEN
 STAC
 ,
 WEAKEN_TAC (fn term => Term.compare (term, “VALID_CHANNEL_ID device_characteristics channel_id_dma_bd”) = EQUAL) THEN
 FITAC FETCHING_BD_L3_IMPLIES_OTHER_BDS_TO_FETCH_EQ_LEMMA THEN
 FITAC FETCHING_BD_L3_NOT_ADDING_BDS_LEMMA THEN
 ITAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
 RLTAC THEN
 ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_CHANNEL_EQ_LEMMA THEN
 FIRTAC invariant_l3_lemmasTheory.UPDATE_DEVICE_STATE_NOT_ADDING_BDS_LEMMA THEN
 ITAC invariant_l3_lemmasTheory.CHANNEL_BD_QUEUES_SUBSET_TRANSFERS_MEM_LEMMA THEN
 STAC
]
QED

Theorem FETCHING_BD_L3_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device1
  ==>
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device2
Proof
INTRO_TAC THEN
ETAC MEMORY_WRITES_PRESERVES_BDS_TO_FETCH THEN
IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA THEN
STAC
QED

Theorem FETCHING_BD_L3_EXTERNAL_IMPLIES_PENDING_ACCESSES_REPLIES_FETCHING_BD_POST_NONE_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  EXTERNAL_BDS device_characteristics /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  channel2.pending_accesses.replies.fetching_bd = NONE
Proof
INTRO_TAC THEN
PTAC fetching_bd_l3 THENL
[
 IRTAC state_lemmasTheory.EXTERNAL_BDS_IMPLIES_NOT_INTERNAL_BDS_LEMMA THEN CONTR_ASMS_TAC
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 PTAC operationsTheory.fetching_bd_set_request THEN
 LRTAC THEN
 RECORD_TAC THEN
 PTAC optionTheory.IS_NONE_DEF THEN
 TRY STAC THEN
 SOLVE_F_ASM_TAC
 ,
 PTAC operationsTheory.fetching_bd_clear_reply THEN
 PTAC concreteTheory.fetching_bd_fetch_bd_concrete THENL
 [
  EQ_PAIR_ASM_TAC THEN RLTAC THEN ALL_LRTAC THEN PTAC operationsTheory.append_bds_to_process THEN RECORD_TAC THEN STAC
  ,
  EQ_PAIR_ASM_TAC THEN RLTAC THEN ALL_LRTAC THEN PTAC operationsTheory.append_bds_to_update THEN RECORD_TAC THEN STAC
  ,
  EQ_PAIR_ASM_TAC THEN RLTAC THEN ALL_LRTAC THEN RECORD_TAC THEN STAC
 ]
]
QED

Theorem FETCHING_BD_L3_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  PROOF_OBLIGATION_FETCH_BD_PRESERVES_OTHER_FETCH_BD_ADDRESSES device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device1
  ==>
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device2
Proof
INTRO_TAC THEN
REWRITE_TAC [INVARIANT_EXTERNAL_FETCH_BD_REPLY] THEN
INTRO_TAC THEN
Cases_on ‘channel_id = channel_id'’ THENL
[
 RLTAC THEN
 IRTAC FETCHING_BD_L3_EXTERNAL_IMPLIES_PENDING_ACCESSES_REPLIES_FETCHING_BD_POST_NONE_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_CHANNEL_EQ_LEMMA THEN
 RLTAC THEN
 RLTAC THEN
 IRTAC optionTheory.NOT_SOME_NONE THEN
 SOLVE_F_ASM_TAC
 ,
 ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN
 PAT_X_ASSUM “x <> y” (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [boolTheory.EQ_SYM_EQ] thm)) THEN
 AITAC THEN
 LRTAC THEN
 IRTAC FETCHING_BD_UPDATING_INTERNAL_STATE_LEMMA THEN
 AXTAC THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  RLTAC THEN
  IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
  RLTAC THEN
  LRTAC THEN
  ETAC INVARIANT_EXTERNAL_FETCH_BD_REPLY THEN
  AIRTAC THEN
  STAC
  ,
  AXTAC THEN
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCH_BD_PRESERVES_OTHER_FETCH_BD_ADDRESSES THEN
  FAIRTAC THEN
  FAITAC THEN
  IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
  RLTAC THEN
  LRTAC THEN
  ETAC INVARIANT_EXTERNAL_FETCH_BD_REPLY THEN
  AIRTAC THEN
  STAC
 ]
]
QED

Theorem FETCHING_BD_L3_CLEARS_REQUESTS_OR_SETS_TO_FETCH_BD_ADDRESSES_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ device_characteristics /\
  PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS device_characteristics /\
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  channel2.pending_accesses.requests.fetching_bd = NONE \/
  ?addresses tag.
    channel2.pending_accesses.requests.fetching_bd = SOME (request_read addresses tag) /\
    (coperation device_characteristics channel_id).fetch_bd_addresses internal_state1 = (addresses, tag) /\
    internal_state2 = internal_state1
Proof
INTRO_TAC THEN
PTAC fetching_bd_l3 THENL
[
 IRTAC state_lemmasTheory.INTERNAL_BDS_IMPLIES_NOT_EXTERNAL_BDS_LEMMA THEN CONTR_ASMS_TAC
 ,
 EQ_PAIR_ASM_TAC THEN
 LRTAC THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 Cases_on ‘fetch_bd_addresses = []’ THENL
 [
  LRTAC THEN
  ETAC bd_queues_lemmasTheory.BD_READ_ADDRESSES_EMPTY_LEMMA THEN
  LRTAC THEN
  LRTAC THEN
  ETAC operationsTheory.fetching_bd_set_request THEN
  LRTAC THEN
  REWRITE_TAC [] THEN
  RECORD_TAC THEN
  EXISTS_EQ_TAC
  ,
  ITAC fetching_bd_lemmasTheory.NOT_EMPTY_FETCH_BD_ADDRESSES_FIRST_BD_RAS_LEMMA THEN
  PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC (mk_var ("memory", (type_of o #1 o dest_forall o concl) thm)) thm)) THEN
  AXTAC THEN
  LRTAC THEN
  PTAC bd_queuesTheory.bd_read_addresses THEN
  RLTAC THEN
  IRTAC lists_lemmasTheory.LIST_IN_LIST_FILTER_MEM_IMPLIES_EQ_LEMMA THEN
  LRTAC THEN
  PTAC operationsTheory.fetching_bd_set_request THEN
  LRTAC THEN
  RECORD_TAC THEN
  PAXTAC THEN
  STAC
 ]
 ,
 PTAC operationsTheory.fetching_bd_clear_reply THEN
 PTAC concreteTheory.fetching_bd_fetch_bd_concrete THENL
 [
  EQ_PAIR_ASM_TAC THEN PTAC operationsTheory.append_bds_to_process THEN ALL_LRTAC THEN RECORD_TAC THEN STAC
  ,
  EQ_PAIR_ASM_TAC THEN PTAC operationsTheory.append_bds_to_update THEN ALL_LRTAC THEN RECORD_TAC THEN STAC  
  ,
  EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN RECORD_TAC THEN STAC  
 ]
]
QED

Theorem FETCHING_BD_L3_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
  PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS device_characteristics /\
  PROOF_OBLIGATION_FETCH_BD_PRESERVES_OTHER_FETCH_BD_ADDRESSES device_characteristics /\
  PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device1
  ==>
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES THEN
INTRO_TAC THEN
FITAC FETCHING_BD_L3_CLEARS_REQUESTS_OR_SETS_TO_FETCH_BD_ADDRESSES_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 Cases_on ‘channel_id = channel_id'’ THENL
 [
  RLTAC THEN
  IRTAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_CHANNEL_EQ_LEMMA THEN
  RLTAC THEN
  LRTAC THEN
  IRTAC optionTheory.NOT_SOME_NONE THEN
  SOLVE_F_ASM_TAC
  ,
  ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN
  PAT_X_ASSUM “x <> y” (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [boolTheory.EQ_SYM_EQ] thm)) THEN
  AITAC THEN
  LRTAC THEN
  FIRTAC FETCHING_BD_UPDATING_INTERNAL_STATE_LEMMA THEN
  SPLIT_ASM_DISJS_TAC THENL
  [
   RLTAC THEN
   RLTAC THEN
   IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
   RLTAC THEN
   AIRTAC THEN
   STAC
   ,
   AXTAC THEN
   PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCH_BD_PRESERVES_OTHER_FETCH_BD_ADDRESSES THEN
   FAIRTAC THEN
   FAITAC THEN
   AIRTAC THEN
   IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
   RLTAC THEN
   LRTAC THEN
   STAC
  ]
 ]
 ,
 AXTAC THEN
 Cases_on ‘channel_id = channel_id'’ THENL
 [
  RLTAC THEN
  ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_CHANNEL_EQ_LEMMA THEN
  RLTAC THEN
  LRTAC THEN
  ETAC optionTheory.SOME_11 THEN
  ETAC stateTheory.interconnect_request_type_11 THEN
  NRLTAC 2 THEN
  IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
  STAC
  ,
  ITAC internal_operation_lemmasTheory.UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA THEN
  PAT_X_ASSUM “x <> y” (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [boolTheory.EQ_SYM_EQ] thm)) THEN
  AITAC THEN
  LRTAC THEN
  FIRTAC FETCHING_BD_UPDATING_INTERNAL_STATE_LEMMA THEN
  SPLIT_ASM_DISJS_TAC THENL
  [
   RLTAC THEN
   RM_ASM_IDS_TAC THEN
   LRTAC THEN
   IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN
   LRTAC THEN
   AIRTAC THEN
   STAC
   ,
   AXTAC THEN AIRTAC THEN IRTAC internal_operation_lemmasTheory.UPDATE_INTERNAL_DEVICE_STATE_LEMMA THEN STAC
  ]
 ]
]
QED

Theorem INVARIANT_BDS_TO_FETCH_DISJOINT_IMPLIES_BDS_TO_FETCH_DISJOINT_LEMMA:
!device_characteristics memory device.
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device
  ==>
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    BDS_TO_FETCH_DISJOINT ((cverification device_characteristics channel_id).bds_to_fetch memory device.dma_state.internal_state)
Proof
INTRO_TAC THEN
INTRO_TAC THEN
ETAC INVARIANT_BDS_TO_FETCH_DISJOINT THEN
AIRTAC THEN
STAC
QED

Theorem FETCHING_BD_L3_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA:
!device_characteristics memory device1 device2 internal_state1 internal_state2 channel1 channel2 channel_id.
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
  VALID_CHANNEL_ID device_characteristics channel_id /\
  internal_state1 = device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  INVARIANT_CONCRETE_L3 device_characteristics memory device1
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_CONCRETE_L3 THEN
ITAC INVARIANT_BDS_TO_FETCH_DISJOINT_IMPLIES_BDS_TO_FETCH_DISJOINT_LEMMA THEN
AITAC THEN
ITAC FETCHING_BD_L3_PRESERVES_INVARIANT_BDS_TO_FETCH_DISJOINT_LEMMA THEN
FITAC FETCHING_BD_L3_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA THEN
FITAC FETCHING_BD_L3_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA THEN
FITAC FETCHING_BD_L3_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA THEN
FITAC FETCHING_BD_L3_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA THEN
STAC
QED

val _ = export_theory();

