open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory;
open operationsTheory;

val _ = new_theory "dma_pending_requests_lemmas";

Theorem MEM_LIST1_IMPLIES_MEM_APPENDS_LEMMA:
!l1 l2 l3 l4 e.
  MEM e l1
  ==>
  MEM e (l1 ++ l2 ++ l3 ++ l4)
Proof
INTRO_TAC THEN
ASM_REWRITE_TAC [listTheory.MEM_APPEND]
QED

Theorem MEM_LIST2_IMPLIES_MEM_APPENDS_LEMMA:
!l1 l2 l3 l4 e.
  MEM e l2
  ==>
  MEM e (l1 ++ l2 ++ l3 ++ l4)
Proof
INTRO_TAC THEN
ASM_REWRITE_TAC [listTheory.MEM_APPEND]
QED

Theorem MEM_LIST3_IMPLIES_MEM_APPENDS_LEMMA:
!l1 l2 l3 l4 e.
  MEM e l3
  ==>
  MEM e (l1 ++ l2 ++ l3 ++ l4)
Proof
INTRO_TAC THEN
ASM_REWRITE_TAC [listTheory.MEM_APPEND]
QED

Theorem MEM_LIST4_IMPLIES_MEM_APPENDS_LEMMA:
!l1 l2 l3 l4 e.
  MEM e l4
  ==>
  MEM e (l1 ++ l2 ++ l3 ++ l4)
Proof
INTRO_TAC THEN
ASM_REWRITE_TAC [listTheory.MEM_APPEND]
QED

Theorem MEM_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX_IMP_SOME_CHANNEL_LEMMA:
!max_index channels request frs urs trs wrs.
  (frs, urs, trs, wrs) = collect_pending_requests_channels_index channels max_index /\
  MEM request (frs ++ urs ++ trs ++ wrs)
  ==>
  ?index channel frs urs trs wrs.
     index <=+ max_index /\
     channel = THE (channels index) /\
     (frs, urs, trs, wrs) = collect_pending_requests channel.pending_accesses.requests /\
     MEM request (frs ++ urs ++ trs ++ wrs)
Proof
ABS_APP_TAC THEN
MATCH_MP_TAC wordsTheory.WORD_INDUCT THEN
APP_SCALAR_TAC THEN
CONJ_TAC THENL
[
 INTRO_TAC THEN
 PTAC collect_pending_requests_channels_index THENL
 [
  PAXTAC THEN
  ALL_LRTAC THEN
  ASM_REWRITE_TAC [wordsTheory.WORD_LOWER_EQ_REFL]
  ,
  CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
 ]
 ,
 INTRO_TAC THEN
 INTRO_TAC THEN
 INTRO_TAC THEN
 PTAC collect_pending_requests_channels_index THENL
 [
  ALL_LRTAC THEN
  PAXTAC THEN
  ASM_REWRITE_TAC [wordsTheory.WORD_LOWER_EQ_REFL]
  ,
  ETAC wordsTheory.n2w_SUC THEN
  ETAC wordsTheory.WORD_ADD_SUB THEN
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 4 THEN
  ETAC listTheory.MEM_APPEND THEN
  SPLIT_ASM_DISJS_TAC THENL
  [
   IRTAC MEM_LIST1_IMPLIES_MEM_APPENDS_LEMMA THEN
   PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPECL [“update_requests : ('c, 'd) interconnect_request_type list”, “transfer_requests : ('c, 'd) interconnect_request_type list”, “write_back_requests : ('c, 'd) interconnect_request_type list”] thm)) THEN
   AIRTAC THEN
   AXTAC THEN
   PAXTAC THEN
   IRTAC (REWRITE_RULE [wordsTheory.n2w_SUC] word_lemmasTheory.NON_ZERO_SUC_LT_IMP_LT_SUC_LEMMA) THEN
   STAC
   ,
   WEAKEN_TAC is_eq THEN
   PAXTAC THEN
   REWRITE_TAC [wordsTheory.WORD_LOWER_EQ_REFL, listTheory.MEM_APPEND] THEN
   STAC
   ,
   IRTAC MEM_LIST2_IMPLIES_MEM_APPENDS_LEMMA THEN
   PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPECL [“fetch_requests : ('c, 'd) interconnect_request_type list”, “transfer_requests : ('c, 'd) interconnect_request_type list”, “write_back_requests : ('c, 'd) interconnect_request_type list”] thm)) THEN
   AIRTAC THEN
   AXTAC THEN
   PAXTAC THEN
   IRTAC (REWRITE_RULE [wordsTheory.n2w_SUC] word_lemmasTheory.NON_ZERO_SUC_LT_IMP_LT_SUC_LEMMA) THEN
   STAC
   ,
   WEAKEN_TAC is_eq THEN
   PAXTAC THEN
   REWRITE_TAC [wordsTheory.WORD_LOWER_EQ_REFL, listTheory.MEM_APPEND] THEN
   STAC
   ,
   IRTAC MEM_LIST3_IMPLIES_MEM_APPENDS_LEMMA THEN
   PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPECL [“fetch_requests : ('c, 'd) interconnect_request_type list”, “update_requests : ('c, 'd) interconnect_request_type list”, “write_back_requests : ('c, 'd) interconnect_request_type list”] thm)) THEN
   AIRTAC THEN
   AXTAC THEN
   PAXTAC THEN
   IRTAC (REWRITE_RULE [wordsTheory.n2w_SUC] word_lemmasTheory.NON_ZERO_SUC_LT_IMP_LT_SUC_LEMMA) THEN
   STAC
   ,
   WEAKEN_TAC is_eq THEN
   PAXTAC THEN
   REWRITE_TAC [wordsTheory.WORD_LOWER_EQ_REFL, listTheory.MEM_APPEND] THEN
   STAC
   ,
   IRTAC MEM_LIST4_IMPLIES_MEM_APPENDS_LEMMA THEN
   PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPECL [“fetch_requests : ('c, 'd) interconnect_request_type list”, “update_requests : ('c, 'd) interconnect_request_type list”, “transfer_requests : ('c, 'd) interconnect_request_type list”] thm)) THEN
   AIRTAC THEN
   AXTAC THEN
   PAXTAC THEN
   IRTAC (REWRITE_RULE [wordsTheory.n2w_SUC] word_lemmasTheory.NON_ZERO_SUC_LT_IMP_LT_SUC_LEMMA) THEN
   STAC
   ,
   WEAKEN_TAC is_eq THEN
   PAXTAC THEN
   REWRITE_TAC [wordsTheory.WORD_LOWER_EQ_REFL, listTheory.MEM_APPEND] THEN
   STAC
  ]
 ]
]
QED

Theorem MEM_DMA_PENDING_REQUESTS_CHANNELS_IMP_SOME_VALID_CHANNEL_LEMMA:
!device_characteristics device pending_accesses request.
  pending_accesses = channel_requests device_characteristics device /\
  MEM request pending_accesses
  ==>
  ?channel_id channel frs urs trs wrs.
    VALID_CHANNEL_ID device_characteristics channel_id /\
    channel = schannel device channel_id /\
    (frs, urs, trs, wrs) = collect_pending_requests channel.pending_accesses.requests /\
    MEM request (frs ++ urs ++ trs ++ wrs)
Proof
INTRO_TAC THEN
PTAC channel_requests THEN
ITAC MEM_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX_IMP_SOME_CHANNEL_LEMMA THEN
REPEAT (WEAKEN_TAC (not o is_exists)) THEN
AXTAC THEN
REWRITE_TAC [stateTheory.schannel, VALID_CHANNEL_ID] THEN
PAXTAC THEN
STAC
QED

Theorem MEM_CHANNEL_REQUESTS_IMPLIES_SOME_VALID_CHANNEL_PENDING_REQUESTS_LEMMA:
!device_characteristics device pending_accesses request.
  pending_accesses = channel_requests device_characteristics device /\
  MEM request pending_accesses
  ==>
  ?channel_id channel channel_requests.
    VALID_CHANNEL_ID device_characteristics channel_id /\
    channel = schannel device channel_id /\
    channel_requests = channel_pending_requests channel.pending_accesses.requests /\
    MEM request channel_requests
Proof
INTRO_TAC THEN
REWRITE_TAC [channel_pending_requests] THEN
IRTAC MEM_DMA_PENDING_REQUESTS_CHANNELS_IMP_SOME_VALID_CHANNEL_LEMMA THEN
AXTAC THEN
PTAC collect_pending_requests THEN
EQ_PAIR_ASM_TAC THEN
NLRTAC 4 THEN
PAXTAC THEN
STAC
QED






Theorem MEM_DMA_PENDING_REQUESTS_CHANNELS_IMP_SOME_VALID_CHANNEL_OR_REGISTER_ACCESS_LEMMA:
!device_characteristics device pending_accesses request.
  pending_accesses = dma_pending_requests device_characteristics device /\
  MEM request pending_accesses
  ==>
  (?channel_id channel frs urs trs wrs.
     VALID_CHANNEL_ID device_characteristics channel_id /\
     channel = schannel device channel_id /\
     (frs, urs, trs, wrs) = collect_pending_requests channel.pending_accesses.requests /\
     MEM request (frs ++ urs ++ trs ++ wrs)) \/
  MEM request device.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
PTAC dma_pending_requests THEN
LRTAC THEN
RW_HYPS_TAC listTheory.MEM_APPEND THEN
SPLIT_ASM_DISJS_TAC THENL
[
 IRTAC MEM_DMA_PENDING_REQUESTS_CHANNELS_IMP_SOME_VALID_CHANNEL_LEMMA THEN STAC
 ,
 STAC
]
QED

Theorem DMA_PENDING_REQUEST_IMPLIES_VALID_CHANNEL_REQUEST_OR_REGISTER_ACCESS_LEMMA:
!device_characteristics device pending_accesses request.
  pending_accesses = dma_pending_requests device_characteristics device /\
  MEM request pending_accesses
  ==>
  (?channel_id channel channel_requests.
     VALID_CHANNEL_ID device_characteristics channel_id /\
     channel = schannel device channel_id /\
     channel_requests = channel_pending_requests channel.pending_accesses.requests /\
     MEM request channel_requests) \/
  MEM request device.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
PTAC dma_pending_requests THEN
LRTAC THEN
RW_HYPS_TAC listTheory.MEM_APPEND THEN
SPLIT_ASM_DISJS_TAC THENL
[
 IRTAC MEM_CHANNEL_REQUESTS_IMPLIES_SOME_VALID_CHANNEL_PENDING_REQUESTS_LEMMA THEN STAC
 ,
 STAC
]
QED

Theorem DMA_PENDING_REQUEST_FROM_VALID_CHANNEL_LEMMA:
!device_characteristics device request.
  MEM request (dma_pending_requests device_characteristics device)
  ==>
  (?channel_id frs urs trs wrs.
    (frs, urs, trs, wrs) = collect_pending_requests (schannel device channel_id).pending_accesses.requests /\
    MEM request (frs ++ urs ++ trs ++ wrs) /\
    VALID_CHANNEL_ID device_characteristics channel_id) \/
  MEM request device.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
FITAC MEM_DMA_PENDING_REQUESTS_CHANNELS_IMP_SOME_VALID_CHANNEL_OR_REGISTER_ACCESS_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AXTAC THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
 PAXTAC THEN
 STAC
 ,
 STAC
]
QED

Theorem DMA_PENDING_REQUEST_FROM_VALID_CHANNEL_REQUESTS_LEMMA:
!device_characteristics device request.
  MEM request (dma_pending_requests device_characteristics device)
  ==>
  (?channel_id pending_requests.
    pending_requests = channel_pending_requests (schannel device channel_id).pending_accesses.requests /\
    MEM request pending_requests /\
    VALID_CHANNEL_ID device_characteristics channel_id) \/
  MEM request device.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
FITAC DMA_PENDING_REQUEST_IMPLIES_VALID_CHANNEL_REQUEST_OR_REGISTER_ACCESS_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AXTAC THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
 PAXTAC THEN
 STAC
 ,
 STAC
]
QED







Definition INDEXED_PENDING_ACCESSES_EQ:
INDEXED_PENDING_ACCESSES_EQ device1 device2 max_index =
  !index.
    index <=+ max_index
    ==>
    (schannel device1 index).pending_accesses = (schannel device2 index).pending_accesses
End

Theorem INDEXED_PENDING_ACCESSES_EQ_SUC_IMPLIES_INDEXED_PENDING_ACCESSES_EQ_LEMMA:
!device1 device2 n.
  SUC n < dimword (: 'a) /\
  INDEXED_PENDING_ACCESSES_EQ device1 device2 (n2w (SUC n) : 'a word)
  ==>
  INDEXED_PENDING_ACCESSES_EQ device1 device2 (n2w n)
Proof
INTRO_TAC THEN
ETAC INDEXED_PENDING_ACCESSES_EQ THEN
INTRO_TAC THEN
ITAC word_lemmasTheory.LEQ_IMPLIES_LEQ_SUC_LEMMA THEN
AIRTAC THEN
STAC
QED

Theorem INDEXED_PENDING_ACCESSES_EQ_IMPLIES_MAX_INDEX_EQ_PENDING_ACCESSES_LEMMA:
!device1 device2 (max_index : 'a word).
  INDEXED_PENDING_ACCESSES_EQ device1 device2 max_index
  ==>
  (schannel device1 max_index).pending_accesses = (schannel device2 max_index).pending_accesses
Proof
INTRO_TAC THEN
ETAC INDEXED_PENDING_ACCESSES_EQ THEN
ASSUME_TAC (SPEC “max_index : 'a word” wordsTheory.WORD_LOWER_EQ_REFL) THEN
AIRTAC THEN
STAC
QED

Theorem INDEXED_PENDING_ACCESSES_EQ_IMPLIES_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX_EQ_LEMMA:
!max_index device1 device2.
  INDEXED_PENDING_ACCESSES_EQ device1 device2 max_index
  ==>
  collect_pending_requests_channels_index device1.dma_state.channels max_index =
  collect_pending_requests_channels_index device2.dma_state.channels max_index
Proof
ABS_APP_TAC THEN
MATCH_MP_TAC wordsTheory.WORD_INDUCT THEN
APP_SCALAR_TAC THEN
CONJ_TAC THENL
[
 INTRO_TAC THEN
 PTAC collect_pending_requests_channels_index THEN PTAC collect_pending_requests_channels_index THENL
 [
  ETAC INDEXED_PENDING_ACCESSES_EQ THEN
  ASSUME_TAC (SPEC “0w” wordsTheory.WORD_LOWER_EQ_REFL) THEN
  AIRTAC THEN
  ETAC (GSYM stateTheory.schannel) THEN
  RLTAC THEN
  RLTAC THEN
  RLTAC THEN
  RLTAC THEN
  RLTAC THEN
  STAC
  ,
  CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
 ]
 ,
 INTRO_TAC THEN
 INTRO_TAC THEN
 INTRO_TAC THEN
 ITAC INDEXED_PENDING_ACCESSES_EQ_IMPLIES_MAX_INDEX_EQ_PENDING_ACCESSES_LEMMA THEN
 IRTAC INDEXED_PENDING_ACCESSES_EQ_SUC_IMPLIES_INDEXED_PENDING_ACCESSES_EQ_LEMMA THEN
 AIRTAC THEN
 ONCE_REWRITE_TAC [collect_pending_requests_channels_index] THEN LETS_TAC THEN IF_SPLIT_TAC THENL
 [
  LRTAC THEN
  ETAC (GSYM stateTheory.schannel) THEN
  RLTAC THEN
  RLTAC THEN
  RLTAC THEN
  RLTAC THEN
  STAC
  ,
  ETAC wordsTheory.n2w_SUC THEN
  ETAC wordsTheory.WORD_ADD_SUB THEN
  WEAKEN_TAC is_neg THEN
  ETAC (GSYM stateTheory.schannel) THEN
  RLTAC THEN
  RLTAC THEN
  RLTAC THEN
  RLTAC THEN
  LRTAC THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  STAC
 ]
]
QED

Theorem MEMORY_REQUESTS_REPLIES_EQ_IMPLIES_DMA_PENDING_REQUESTS_EQ_LEMMA:
!device_characteristics device1 device2.
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device1 device2
  ==>
  dma_pending_requests device_characteristics device1 =
  dma_pending_requests device_characteristics device2
Proof
INTRO_TAC THEN
REPEAT (PTAC operationsTheory.dma_pending_requests) THEN
REPEAT (PTAC channel_requests) THEN
ETAC MEMORY_REQUESTS_REPLIES_EQ THEN
LRTAC THEN
REWRITE_TAC [listTheory.APPEND_11] THEN
RW_HYPS_TAC VALID_CHANNEL_ID THEN
ETAC INDEXED_PENDING_ACCESSES_EQ THEN
IRTAC INDEXED_PENDING_ACCESSES_EQ_IMPLIES_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX_EQ_LEMMA THEN
LRTAC THEN
LRTAC THEN
EQ_PAIR_ASM_TAC THEN
STAC
QED

Theorem MEMORY_REQUESTS_REPLIES_EQ_IMPLIES_COLLECT_PENDING_REQUESTS_EQ_LEMMA:
!device_characteristics channel_id device1 device2 channel1 channel2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device1 device2 /\
  channel1 = schannel device1 channel_id /\
  channel2 = schannel device2 channel_id
  ==>
  collect_pending_requests channel2.pending_accesses.requests = collect_pending_requests channel1.pending_accesses.requests
Proof
INTRO_TAC THEN
ETAC MEMORY_REQUESTS_REPLIES_EQ THEN
AIRTAC THEN
ETAC operationsTheory.collect_pending_requests THEN
STAC
QED

Theorem MEMORY_REQUESTS_REPLIES_EQ_IMPLIES_CHANNEL_PENDING_REQUESTS_EQ_LEMMA:
!device_characteristics channel_id device1 device2 channel1 channel2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device1 device2 /\
  channel1 = schannel device1 channel_id /\
  channel2 = schannel device2 channel_id
  ==>
  channel_pending_requests channel2.pending_accesses.requests = channel_pending_requests channel1.pending_accesses.requests
Proof
INTRO_TAC THEN
ETAC MEMORY_REQUESTS_REPLIES_EQ THEN
AIRTAC THEN
ETAC operationsTheory.channel_pending_requests THEN
STAC
QED

Theorem MEMORY_REQUESTS_REPLIES_EQ_IMPLIES_COLLECT_PENDING_REQUESTS_CHANNELS_EQ_IND_LEMMA:
!channels1 channel_id.
  (\channels1 channel_id.
    !device_characteristics channels2 device1 device2 index.
      VALID_CHANNEL_ID device_characteristics channel_id /\
      MEMORY_REQUESTS_REPLIES_EQ device_characteristics device1 device2 /\
      channels1 = device1.dma_state.channels /\
      channels2 = device2.dma_state.channels
      ==>
      collect_pending_requests_channels_index channels1 channel_id =
      collect_pending_requests_channels_index channels2 channel_id) channels1 channel_id
Proof
MATCH_MP_TAC operationsTheory.collect_pending_requests_channels_index_ind THEN
REPEAT CONJ_TAC THENL
[
 APP_SCALAR_TAC THEN
 INTRO_TAC THEN
 INTRO_TAC THEN
 ONCE_REWRITE_TAC [operationsTheory.collect_pending_requests_channels_index] THEN
 LETS_TAC THEN
 IF_SPLIT_TAC THENL
 [
  WEAKEN_TAC is_forall THEN
  LRTAC THEN
  IRTAC MEMORY_REQUESTS_REPLIES_EQ_IMPLIES_COLLECT_PENDING_REQUESTS_EQ_LEMMA THEN
  ALL_LRTAC THEN
  ETAC stateTheory.schannel THEN
  STAC
  ,
  ITAC MEMORY_REQUESTS_REPLIES_EQ_IMPLIES_COLLECT_PENDING_REQUESTS_EQ_LEMMA THEN
  ETAC stateTheory.schannel THEN
  AITAC THEN
  IRTAC state_lemmasTheory.NEQ_ZERO_INDEX_PRESERVES_VALID_CHANNEL_ID_LEMMA THEN
  AITAC THEN
  ALL_LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  STAC
 ]
]
QED

Theorem MEMORY_REQUESTS_REPLIES_EQ_IMPLIES_COLLECT_PENDING_REQUESTS_CHANNELS_EQ_LEMMA:
!device_characteristics device1 device2 channels1 channels2 channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device1 device2 /\
  channels1 = device1.dma_state.channels /\
  channels2 = device2.dma_state.channels
  ==>
  collect_pending_requests_channels_index channels1 channel_id =
  collect_pending_requests_channels_index channels2 channel_id
Proof
REWRITE_TAC [BETA_RULE MEMORY_REQUESTS_REPLIES_EQ_IMPLIES_COLLECT_PENDING_REQUESTS_CHANNELS_EQ_IND_LEMMA]
QED





















































Theorem INDEX_FETCHING_BD_SOME_REQUEST_IMPLIES_MEM_REQUEST_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX_LEMMA:
!max_index i request device frs urs trs wrs.
  i <=+ max_index /\
  (schannel device i).pending_accesses.requests.fetching_bd = SOME request /\
  (frs, urs, trs, wrs) = collect_pending_requests_channels_index device.dma_state.channels max_index
  ==>
  MEM request frs
Proof
ABS_APP_TAC THEN
MATCH_MP_TAC wordsTheory.WORD_INDUCT THEN
APP_SCALAR_TAC THEN
CONJ_TAC THENL
[
 INTRO_TAC THEN
 PTAC operationsTheory.collect_pending_requests_channels_index THENL
 [
  ETAC wordsTheory.WORD_LS_word_0 THEN
  EQ_PAIR_ASM_TAC THEN
  ALL_RLTAC THEN
  ETAC stateTheory.schannel THEN
  RLTAC THEN
  PTAC operationsTheory.collect_pending_requests THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  ETAC operationsTheory.collect_pending_fetch_bd_request THEN
  RLTAC THEN
  REWRITE_TAC [listTheory.MEM]
  ,
  CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
 ]
 ,
 INTRO_TAC THEN
 INTRO_TAC THEN
 INTRO_TAC THEN
 ETAC wordsTheory.n2w_SUC THEN
 IRTAC word_lemmasTheory.WORD_LEQ_SUC_IMPLIES_LEQ_OR_EQ_SUC_LEMMA THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  PTAC operationsTheory.collect_pending_requests_channels_index THENL
  [
   IRTAC word_lemmasTheory.SUC_EQ_ZERO_IMPLIES_F_LEMMA THEN
   SOLVE_F_ASM_TAC
   ,
   ETAC wordsTheory.WORD_ADD_SUB THEN
   AIRTAC THEN
   EQ_PAIR_ASM_TAC THEN
   ASM_REWRITE_TAC [listTheory.MEM_APPEND]
  ]
  ,
  PTAC operationsTheory.collect_pending_requests_channels_index THENL
  [
   EQ_PAIR_ASM_TAC THEN
   NRLTAC 4 THEN
   LRTAC THEN
   ETAC stateTheory.schannel THEN
   LRTAC THEN
   RLTAC THEN
   PTAC operationsTheory.collect_pending_requests THEN
   LRTAC THEN
   ETAC operationsTheory.collect_pending_fetch_bd_request THEN
   EQ_PAIR_ASM_TAC THEN
   RLTAC THEN
   REWRITE_TAC [listTheory.MEM]
   ,
   EQ_PAIR_ASM_TAC THEN
   ETAC wordsTheory.WORD_ADD_SUB THEN
   RLTAC THEN
   ETAC stateTheory.schannel THEN
   RLTAC THEN
   PTAC operationsTheory.collect_pending_requests THEN
   LRTAC THEN
   EQ_PAIR_ASM_TAC THEN
   ETAC operationsTheory.collect_pending_fetch_bd_request THEN
   RLTAC THEN
   ASM_REWRITE_TAC [listTheory.MEM, listTheory.MEM_APPEND]
  ]
 ]
]
QED

Theorem SOME_FETCHING_BD_REQUEST_IMPLIES_MEM_DMA_PENDING_REQUESTS_LEMMA:
!device_characteristics device i request.
  VALID_CHANNEL_ID device_characteristics i /\
  (schannel device i).pending_accesses.requests.fetching_bd = SOME request
  ==>
  MEM request (dma_pending_requests device_characteristics device)
Proof
INTRO_TAC THEN
REWRITE_TAC [operationsTheory.dma_pending_requests, channel_requests] THEN
LETS_TAC THEN
PTAC stateTheory.VALID_CHANNEL_ID THEN
IRTAC INDEX_FETCHING_BD_SOME_REQUEST_IMPLIES_MEM_REQUEST_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX_LEMMA THEN
ASM_REWRITE_TAC [listTheory.MEM_APPEND]
QED

Theorem SOME_PENDING_FETCHING_BD_REQUEST_IMPLIES_MEM_CHANNEL_REQUESTS_LEMMA:
!device_characteristics device channel_id requests request.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  requests = channel_requests device_characteristics device /\
  (schannel device channel_id).pending_accesses.requests.fetching_bd = SOME request
  ==>
  MEM request requests
Proof
INTRO_TAC THEN
PTAC operationsTheory.channel_requests THEN
ETAC VALID_CHANNEL_ID THEN
IRTAC INDEX_FETCHING_BD_SOME_REQUEST_IMPLIES_MEM_REQUEST_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX_LEMMA THEN
ASM_REWRITE_TAC [listTheory.MEM_APPEND]
QED







Theorem INDEX_MEM_UPDATING_BD_IMPLIES_MEM_REQUEST_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX_LEMMA:
!max_index i request device frs urs trs wrs.
  i <=+ max_index /\
  MEM request (schannel device i).pending_accesses.requests.updating_bd /\
  (frs, urs, trs, wrs) = collect_pending_requests_channels_index device.dma_state.channels max_index
  ==>
  MEM request urs
Proof
ABS_APP_TAC THEN
MATCH_MP_TAC wordsTheory.WORD_INDUCT THEN
APP_SCALAR_TAC THEN
CONJ_TAC THENL
[
 INTRO_TAC THEN
 PTAC operationsTheory.collect_pending_requests_channels_index THENL
 [
  ETAC wordsTheory.WORD_LS_word_0 THEN
  EQ_PAIR_ASM_TAC THEN
  ALL_RLTAC THEN
  ETAC stateTheory.schannel THEN
  RLTAC THEN
  PTAC operationsTheory.collect_pending_requests THEN
  EQ_PAIR_ASM_TAC THEN
  STAC
  ,
  CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
 ]
 ,
 INTRO_TAC THEN
 INTRO_TAC THEN
 INTRO_TAC THEN
 ETAC wordsTheory.n2w_SUC THEN
 IRTAC word_lemmasTheory.WORD_LEQ_SUC_IMPLIES_LEQ_OR_EQ_SUC_LEMMA THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  PTAC operationsTheory.collect_pending_requests_channels_index THENL
  [
   IRTAC word_lemmasTheory.SUC_EQ_ZERO_IMPLIES_F_LEMMA THEN
   SOLVE_F_ASM_TAC
   ,
   ETAC wordsTheory.WORD_ADD_SUB THEN
   AIRTAC THEN
   EQ_PAIR_ASM_TAC THEN
   ASM_REWRITE_TAC [listTheory.MEM_APPEND]
  ]
  ,
  PTAC operationsTheory.collect_pending_requests_channels_index THENL
  [
   EQ_PAIR_ASM_TAC THEN
   NRLTAC 4 THEN
   LRTAC THEN
   ETAC stateTheory.schannel THEN
   LRTAC THEN
   RLTAC THEN
   PTAC operationsTheory.collect_pending_requests THEN
   EQ_PAIR_ASM_TAC THEN
   STAC
   ,
   EQ_PAIR_ASM_TAC THEN
   ETAC wordsTheory.WORD_ADD_SUB THEN
   RLTAC THEN
   ETAC stateTheory.schannel THEN
   RLTAC THEN
   PTAC operationsTheory.collect_pending_requests THEN
   EQ_PAIR_ASM_TAC THEN
   LRTAC THEN
   ASM_REWRITE_TAC [listTheory.MEM, listTheory.MEM_APPEND]
  ]
 ]
]
QED

Theorem MEM_UPDATING_BD_REQUEST_IMPLIES_MEM_DMA_PENDING_REQUESTS_LEMMA:
!device_characteristics device i request.
  VALID_CHANNEL_ID device_characteristics i /\
  MEM request (schannel device i).pending_accesses.requests.updating_bd
  ==>
  MEM request (dma_pending_requests device_characteristics device)
Proof
INTRO_TAC THEN
REWRITE_TAC [operationsTheory.dma_pending_requests, channel_requests] THEN
LETS_TAC THEN
PTAC stateTheory.VALID_CHANNEL_ID THEN
IRTAC INDEX_MEM_UPDATING_BD_IMPLIES_MEM_REQUEST_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX_LEMMA THEN
ASM_REWRITE_TAC [listTheory.MEM_APPEND]
QED

Theorem MEM_UPDATING_BD_REQUEST_IMPLIES_MEM_CHANNEL_REQUESTS_LEMMA:
!device_characteristics device channel_id requests request.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  requests = channel_requests device_characteristics device /\
  MEM request (schannel device channel_id).pending_accesses.requests.updating_bd
  ==>
  MEM request requests
Proof
INTRO_TAC THEN
PTAC operationsTheory.channel_requests THEN
ETAC VALID_CHANNEL_ID THEN
IRTAC INDEX_MEM_UPDATING_BD_IMPLIES_MEM_REQUEST_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX_LEMMA THEN
ASM_REWRITE_TAC [listTheory.MEM_APPEND]
QED









Theorem INDEX_MEM_TRANSFERRING_DATA_IMPLIES_MEM_REQUEST_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX_LEMMA:
!max_index i request device frs urs trs wrs.
  i <=+ max_index /\
  MEM request (schannel device i).pending_accesses.requests.transferring_data /\
  (frs, urs, trs, wrs) = collect_pending_requests_channels_index device.dma_state.channels max_index
  ==>
  MEM request trs
Proof
ABS_APP_TAC THEN
MATCH_MP_TAC wordsTheory.WORD_INDUCT THEN
APP_SCALAR_TAC THEN
CONJ_TAC THENL
[
 INTRO_TAC THEN
 PTAC operationsTheory.collect_pending_requests_channels_index THENL
 [
  ETAC wordsTheory.WORD_LS_word_0 THEN
  EQ_PAIR_ASM_TAC THEN
  ALL_RLTAC THEN
  ETAC stateTheory.schannel THEN
  RLTAC THEN
  PTAC operationsTheory.collect_pending_requests THEN
  EQ_PAIR_ASM_TAC THEN
  STAC
  ,
  CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
 ]
 ,
 INTRO_TAC THEN
 INTRO_TAC THEN
 INTRO_TAC THEN
 ETAC wordsTheory.n2w_SUC THEN
 IRTAC word_lemmasTheory.WORD_LEQ_SUC_IMPLIES_LEQ_OR_EQ_SUC_LEMMA THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  PTAC operationsTheory.collect_pending_requests_channels_index THENL
  [
   IRTAC word_lemmasTheory.SUC_EQ_ZERO_IMPLIES_F_LEMMA THEN
   SOLVE_F_ASM_TAC
   ,
   ETAC wordsTheory.WORD_ADD_SUB THEN
   AIRTAC THEN
   EQ_PAIR_ASM_TAC THEN
   ASM_REWRITE_TAC [listTheory.MEM_APPEND]
  ]
  ,
  PTAC operationsTheory.collect_pending_requests_channels_index THENL
  [
   EQ_PAIR_ASM_TAC THEN
   NRLTAC 4 THEN
   LRTAC THEN
   ETAC stateTheory.schannel THEN
   LRTAC THEN
   RLTAC THEN
   PTAC operationsTheory.collect_pending_requests THEN
   EQ_PAIR_ASM_TAC THEN
   STAC
   ,
   EQ_PAIR_ASM_TAC THEN
   ETAC wordsTheory.WORD_ADD_SUB THEN
   RLTAC THEN
   ETAC stateTheory.schannel THEN
   RLTAC THEN
   PTAC operationsTheory.collect_pending_requests THEN
   EQ_PAIR_ASM_TAC THEN
   LRTAC THEN
   ASM_REWRITE_TAC [listTheory.MEM, listTheory.MEM_APPEND]
  ]
 ]
]
QED

Theorem MEM_TRANSFERRING_DATA_REQUEST_IMPLIES_MEM_DMA_PENDING_REQUESTS_LEMMA:
!device_characteristics device i request.
  VALID_CHANNEL_ID device_characteristics i /\
  MEM request (schannel device i).pending_accesses.requests.transferring_data
  ==>
  MEM request (dma_pending_requests device_characteristics device)
Proof
INTRO_TAC THEN
REWRITE_TAC [operationsTheory.dma_pending_requests, channel_requests] THEN
LETS_TAC THEN
PTAC stateTheory.VALID_CHANNEL_ID THEN
IRTAC INDEX_MEM_TRANSFERRING_DATA_IMPLIES_MEM_REQUEST_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX_LEMMA THEN
ASM_REWRITE_TAC [listTheory.MEM_APPEND]
QED

Theorem MEM_TRANSFERRING_DATA_REQUEST_IMPLIES_MEM_CHANNEL_REQUESTS_LEMMA:
!device_characteristics device channel_id requests request.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  requests = channel_requests device_characteristics device /\
  MEM request (schannel device channel_id).pending_accesses.requests.transferring_data
  ==>
  MEM request requests
Proof
INTRO_TAC THEN
PTAC operationsTheory.channel_requests THEN
ETAC VALID_CHANNEL_ID THEN
IRTAC INDEX_MEM_TRANSFERRING_DATA_IMPLIES_MEM_REQUEST_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX_LEMMA THEN
ASM_REWRITE_TAC [listTheory.MEM_APPEND]
QED








Theorem INDEX_MEM_WRITING_BACK_BD_IMPLIES_MEM_REQUEST_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX_LEMMA:
!max_index i request device frs urs trs wrs.
  i <=+ max_index /\
  MEM request (schannel device i).pending_accesses.requests.writing_back_bd /\
  (frs, urs, trs, wrs) = collect_pending_requests_channels_index device.dma_state.channels max_index
  ==>
  MEM request wrs
Proof
ABS_APP_TAC THEN
MATCH_MP_TAC wordsTheory.WORD_INDUCT THEN
APP_SCALAR_TAC THEN
CONJ_TAC THENL
[
 INTRO_TAC THEN
 PTAC operationsTheory.collect_pending_requests_channels_index THENL
 [
  ETAC wordsTheory.WORD_LS_word_0 THEN
  EQ_PAIR_ASM_TAC THEN
  ALL_RLTAC THEN
  ETAC stateTheory.schannel THEN
  RLTAC THEN
  PTAC operationsTheory.collect_pending_requests THEN
  EQ_PAIR_ASM_TAC THEN
  STAC
  ,
  CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
 ]
 ,
 INTRO_TAC THEN
 INTRO_TAC THEN
 INTRO_TAC THEN
 ETAC wordsTheory.n2w_SUC THEN
 IRTAC word_lemmasTheory.WORD_LEQ_SUC_IMPLIES_LEQ_OR_EQ_SUC_LEMMA THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  PTAC operationsTheory.collect_pending_requests_channels_index THENL
  [
   IRTAC word_lemmasTheory.SUC_EQ_ZERO_IMPLIES_F_LEMMA THEN
   SOLVE_F_ASM_TAC
   ,
   ETAC wordsTheory.WORD_ADD_SUB THEN
   AIRTAC THEN
   EQ_PAIR_ASM_TAC THEN
   ASM_REWRITE_TAC [listTheory.MEM_APPEND]
  ]
  ,
  PTAC operationsTheory.collect_pending_requests_channels_index THENL
  [
   EQ_PAIR_ASM_TAC THEN
   NRLTAC 4 THEN
   LRTAC THEN
   ETAC stateTheory.schannel THEN
   LRTAC THEN
   RLTAC THEN
   PTAC operationsTheory.collect_pending_requests THEN
   EQ_PAIR_ASM_TAC THEN
   STAC
   ,
   EQ_PAIR_ASM_TAC THEN
   ETAC wordsTheory.WORD_ADD_SUB THEN
   RLTAC THEN
   ETAC stateTheory.schannel THEN
   RLTAC THEN
   PTAC operationsTheory.collect_pending_requests THEN
   EQ_PAIR_ASM_TAC THEN
   LRTAC THEN
   ASM_REWRITE_TAC [listTheory.MEM, listTheory.MEM_APPEND]
  ]
 ]
]
QED

Theorem MEM_WRITING_BACK_BD_REQUEST_IMPLIES_MEM_DMA_PENDING_REQUESTS_LEMMA:
!device_characteristics device i request.
  VALID_CHANNEL_ID device_characteristics i /\
  MEM request (schannel device i).pending_accesses.requests.writing_back_bd
  ==>
  MEM request (dma_pending_requests device_characteristics device)
Proof
INTRO_TAC THEN
REWRITE_TAC [operationsTheory.dma_pending_requests, channel_requests] THEN
LETS_TAC THEN
PTAC stateTheory.VALID_CHANNEL_ID THEN
IRTAC INDEX_MEM_WRITING_BACK_BD_IMPLIES_MEM_REQUEST_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX_LEMMA THEN
ASM_REWRITE_TAC [listTheory.MEM_APPEND]
QED

Theorem MEM_WRITING_BACK_BD_REQUEST_IMPLIES_MEM_CHANNEL_REQUESTS_LEMMA:
!device_characteristics device channel_id requests request.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  requests = channel_requests device_characteristics device /\
  MEM request (schannel device channel_id).pending_accesses.requests.writing_back_bd
  ==>
  MEM request requests
Proof
INTRO_TAC THEN
PTAC operationsTheory.channel_requests THEN
ETAC VALID_CHANNEL_ID THEN
IRTAC INDEX_MEM_WRITING_BACK_BD_IMPLIES_MEM_REQUEST_COLLECT_PENDING_REQUESTS_CHANNELS_INDEX_LEMMA THEN
ASM_REWRITE_TAC [listTheory.MEM_APPEND]
QED








Theorem DMA_PENDING_REQUEST_FROM_VALID_SCHANNEL_LEMMA:
!device_characteristics device request.
  MEM request (dma_pending_requests device_characteristics device)
  ==>
  (?channel_id frs urs trs wrs.
    (frs, urs, trs, wrs) = collect_pending_requests (schannel device channel_id).pending_accesses.requests /\
    MEM request (frs ++ urs ++ trs ++ wrs) /\
    VALID_CHANNEL_ID device_characteristics channel_id) \/
  MEM request device.dma_state.pending_register_related_memory_requests
Proof
REWRITE_TAC [stateTheory.schannel, DMA_PENDING_REQUEST_FROM_VALID_CHANNEL_LEMMA]
QED

Theorem COLLECT_PENDING_REQUESTS_IN_CHANNEL_REQUESTS_LEMMA:
!device_characteristics device requests channel_id request frs urs trs wrs.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  requests = channel_requests device_characteristics device /\
  (frs, urs, trs, wrs) = collect_pending_requests (schannel device channel_id).pending_accesses.requests /\
  MEM request (frs ++ urs ++ trs ++ wrs)
  ==>
  MEM request requests
Proof
INTRO_TAC THEN
ETAC operationsTheory.collect_pending_requests THEN
EQ_PAIR_ASM_TAC THEN
ALL_LRTAC THEN
ETAC listTheory.MEM_APPEND THEN
SPLIT_ASM_DISJS_TAC THENL
[
 MATCH_MP_TAC SOME_PENDING_FETCHING_BD_REQUEST_IMPLIES_MEM_CHANNEL_REQUESTS_LEMMA THEN
 EXISTS_EQ_TAC THEN
 PAXTAC THEN
 PTAC operationsTheory.collect_pending_fetch_bd_request THENL
 [
  ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
  ,
  ETAC listTheory.MEM THEN REMOVE_F_DISJUNCTS_TAC THEN STAC
 ]
 ,
 IRTAC MEM_UPDATING_BD_REQUEST_IMPLIES_MEM_CHANNEL_REQUESTS_LEMMA THEN STAC
 ,
 IRTAC MEM_TRANSFERRING_DATA_REQUEST_IMPLIES_MEM_CHANNEL_REQUESTS_LEMMA THEN STAC
 ,
 IRTAC MEM_WRITING_BACK_BD_REQUEST_IMPLIES_MEM_CHANNEL_REQUESTS_LEMMA THEN STAC
]
QED

Theorem CHANNEL_PENDING_REQUESTS_IN_CHANNEL_REQUESTS_LEMMA:
!device_characteristics device requests channel_id request pending_requests.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  requests = channel_requests device_characteristics device /\
  pending_requests = channel_pending_requests (schannel device channel_id).pending_accesses.requests /\
  MEM request pending_requests
  ==>
  MEM request requests
Proof
INTRO_TAC THEN
PTAC channel_pending_requests THEN
ITAC (REWRITE_RULE [collect_pending_requests] COLLECT_PENDING_REQUESTS_IN_CHANNEL_REQUESTS_LEMMA) THEN
STAC
QED

Theorem PENDING_WRITE_REQUEST_IS_CHANNEL_REQUEST_LEMMA:
!device_characteristics channel_id device address_bytes write_tag requests requests_was frs urs trs wrs.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (frs, urs, trs, wrs) = collect_pending_requests (schannel device channel_id).pending_accesses.requests /\
  MEM (request_write address_bytes write_tag) (frs ++ urs ++ trs ++ wrs) /\
  requests = channel_requests device_characteristics device /\
  requests_was = MAP request_to_write_addresses requests
  ==>
  MEM (MAP FST address_bytes) requests_was
Proof
INTRO_TAC THEN
IRTAC COLLECT_PENDING_REQUESTS_IN_CHANNEL_REQUESTS_LEMMA THEN
IRTAC internal_operation_lemmasTheory.REQUEST_WAS_IN_REQUESTS_WAS_LEMMA THEN
STAC
QED

Theorem CHANNEL_PENDING_WRITE_REQUEST_IS_CHANNEL_REQUEST_LEMMA:
!device_characteristics channel_id device address_bytes write_tag requests requests_was pending_requests.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  pending_requests = channel_pending_requests (schannel device channel_id).pending_accesses.requests /\
  MEM (request_write address_bytes write_tag) pending_requests /\
  requests = channel_requests device_characteristics device /\
  requests_was = MAP request_to_write_addresses requests
  ==>
  MEM (MAP FST address_bytes) requests_was
Proof
INTRO_TAC THEN
PTAC channel_pending_requests THEN
IRTAC (REWRITE_RULE [collect_pending_requests] PENDING_WRITE_REQUEST_IS_CHANNEL_REQUEST_LEMMA) THEN
STAC
QED

val _ = export_theory();
