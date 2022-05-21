open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory operationsTheory;

val _ = new_theory "append_bds_lemmas";

Theorem APPEND_BDS_CHANNEL_PRESERVES_PENDING_ACCESSES_LEMMA:
!channel1 channel2 bds_to_fetch.
  channel2 = append_bds_channel channel1 bds_to_fetch
  ==>
  channel2.pending_accesses = channel1.pending_accesses
Proof
INTRO_TAC THEN
PTAC append_bds_channel THENL
[
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 STAC
]
QED

Theorem APPEND_BDS_CHANNEL_PRESERVES_CHANNELS_PENDING_ACCESSES_LEMMA:
!channels1 channels2 channel_id1 channel1 channel2 bds_to_fetch.
  channel1 = THE (channels1 channel_id1) /\
  channel2 = append_bds_channel channel1 bds_to_fetch /\
  channels2 = (channel_id1 =+ SOME channel2) channels1
  ==>
  !channel_id2. (THE (channels2 channel_id2)).pending_accesses = (THE (channels1 channel_id2)).pending_accesses
Proof
INTRO_TAC THEN
GEN_TAC THEN
ITAC APPEND_BDS_CHANNEL_PRESERVES_PENDING_ACCESSES_LEMMA THEN
ETAC combinTheory.UPDATE_def THEN
ALL_LRTAC THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 ETAC optionTheory.option_CLAUSES THEN STAC
 ,
 STAC
]
QED

Theorem APPEND_BDS_CHANNELS_INDEX_PRESERVES_PENDING_ACCESSES_IND_LEMMA:
!dma_characteristics memory channels1 internal_state channel_id.
  (\dma_characteristics memory channels1 internal_state channel_id.
    !channels2.
    channels2 = append_bds_channels_index dma_characteristics memory channels1 internal_state channel_id
    ==>
    !channel_id. (THE (channels2 channel_id)).pending_accesses = (THE (channels1 channel_id)).pending_accesses)
    dma_characteristics memory channels1 internal_state channel_id
Proof
MATCH_MP_TAC append_bds_channels_index_ind THEN
APP_SCALAR_TAC THEN
REPEAT CONJ_TAC THEN (
 INTRO_TAC THEN
 INTRO_TAC THEN
 PTAC append_bds_channels_index THENL
 [
  IRTAC APPEND_BDS_CHANNEL_PRESERVES_CHANNELS_PENDING_ACCESSES_LEMMA THEN STAC
  ,
  AITAC THEN
  AIRTAC THEN
  IRTAC APPEND_BDS_CHANNEL_PRESERVES_CHANNELS_PENDING_ACCESSES_LEMMA THEN
  STAC
 ])
QED

Theorem APPEND_BDS_CHANNELS_INDEX_PRESERVES_PENDING_ACCESSES_LEMMA:
!channel_id dma_characteristics channels1 channels2 internal_state memory.
  channels2 = append_bds_channels_index dma_characteristics memory channels1 internal_state channel_id
  ==>
  !channel_id. (THE (channels2 channel_id)).pending_accesses = (THE (channels1 channel_id)).pending_accesses
Proof
REWRITE_TAC [BETA_RULE APPEND_BDS_CHANNELS_INDEX_PRESERVES_PENDING_ACCESSES_IND_LEMMA]
QED

Theorem APPEND_BDS_CHANNELS_PRESERVES_PENDING_ACCESSES_LEMMA:
!dma_characteristics channels1 channels2 internal_state memory.
  channels2 = append_bds_channels dma_characteristics memory channels1 internal_state
  ==>
  !channel_id. (THE (channels2 channel_id)).pending_accesses = (THE (channels1 channel_id)).pending_accesses
Proof
INTRO_TAC THEN
PTAC append_bds_channels THEN
IRTAC APPEND_BDS_CHANNELS_INDEX_PRESERVES_PENDING_ACCESSES_LEMMA THEN
STAC
QED

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA:
!device_characteristics memory device1 device2.
  device2 = dma_append_external_abstract_bds device_characteristics memory device1
  ==>
  device2.dma_state.pending_register_related_memory_requests = device1.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
PTAC dma_append_external_abstract_bds THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REPLIES_LEMMA:
!device_characteristics memory device1 device2.
  device2 = dma_append_external_abstract_bds device_characteristics memory device1
  ==>
  device2.dma_state.pending_register_related_memory_replies = device1.dma_state.pending_register_related_memory_replies
Proof
INTRO_TAC THEN
PTAC dma_append_external_abstract_bds THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA:
!device_characteristics memory_option device1 device2.
  device2 = dma_append_internal_abstract_bds device_characteristics memory_option device1
  ==>
  device2.dma_state.pending_register_related_memory_requests = device1.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
PTAC dma_append_internal_abstract_bds THENL
[
 STAC
 ,
 ITAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA THEN STAC
]
QED

Theorem DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REPLIES_LEMMA:
!device_characteristics memory_option device1 device2.
  device2 = dma_append_internal_abstract_bds device_characteristics memory_option device1
  ==>
  device2.dma_state.pending_register_related_memory_replies = device1.dma_state.pending_register_related_memory_replies
Proof
INTRO_TAC THEN
PTAC dma_append_internal_abstract_bds THENL
[
 STAC
 ,
 ITAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REPLIES_LEMMA THEN STAC
]
QED



Theorem APPEND_BDS_CHANNEL_EXTENDS_ABSTRACT_BDS_TO_FETCH_OR_PRESERVES_CHANNEL_LEMMA:
!channel1 channel2 abstract_bds.
  channel2 = append_bds_channel channel1 abstract_bds
  ==>
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL channel1 channel2 abstract_bds
Proof
INTRO_TAC THEN
PTAC EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL THEN
PTAC operationsTheory.append_bds_channel THENL
[
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
 AXTAC THEN
 PTAC EXTENDED_ABSTRACT_BDS_TO_FETCH THEN
 REWRITE_TAC [EXTENDED_BDS, APPENDED_BDS] THEN
 CONJ_TAC THENL
 [
  ALL_LRTAC THEN PAXTAC THEN STAC
  ,
  STAC
 ]
 ,
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 REWRITE_TAC [NOT_EXTENDED_ABSTRACT_BDS_TO_FETCH_AND_UNCHANGED_CHANNEL] THEN
 REWRITE_TAC [EXTENDED_BDS] THEN
 ALL_LRTAC THEN
 ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
 STAC
]
QED

Theorem APPEND_BDS_CHANNEL_EXTENDS_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_ZERO_LEMMA:
!device_characteristics memory internal_state channels1 channels2 channel1 channel2 bds_to_fetch.
  bds_to_fetch = (cverification device_characteristics 0w).bds_to_fetch memory internal_state /\
  channel1 = THE (channels1 0w) /\
  channel2 = append_bds_channel channel1 bds_to_fetch /\
  channels2 = (0w =+ SOME channel2) channels1
  ==>
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS device_characteristics memory internal_state channels1 channels2 0w /\
  PRESERVED_CHANNELS channels1 channels2 0w /\
  DEFINED_PRESERVED_CHANNELS channels1 channels2 0w
Proof
INTRO_TAC THEN
ITAC internal_operation_lemmasTheory.UPDATING_CHANNEL_ZERO_IMPLIES_DEFINED_PRESERVED_CHANNELS_ZERO_LEMMA THEN
CONJS_TAC THEN TRY STAC THENL
[
 ETAC EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS THEN
 INTRO_TAC THEN
 ETAC wordsTheory.WORD_LS_word_0 THEN
 LRTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN
 IRTAC APPEND_BDS_CHANNEL_EXTENDS_ABSTRACT_BDS_TO_FETCH_OR_PRESERVES_CHANNEL_LEMMA THEN
 LRTAC THEN LRTAC THEN
 ETAC combinTheory.UPDATE_def THEN
 APP_SCALAR_TAC THEN
 ASM_REWRITE_TAC [optionTheory.THE_DEF]
 ,
 PTAC PRESERVED_CHANNELS THEN
 INTRO_TAC THEN
 ETAC wordsTheory.WORD_HIGHER THEN
 IRTAC wordsTheory.WORD_LOWER_NOT_EQ THEN
 ALL_LRTAC THEN
 REWRITE_TAC [combinTheory.UPDATE_def] THEN
 APP_SCALAR_TAC THEN
 STAC
]
QED

Theorem UPDATING_SUC_PRESERVES_CHANNELS_LEMMA:
!n (index : 'b word) channel1 channel2 channel channels1 channels2.
  SUC n < dimword (: 'b) /\
  index <=+ n2w n /\
  channels2 = ((n2w n + 1w) =+ SOME channel) channels1 /\
  channel1 = THE (channels1 index) /\
  channel2 = THE (channels2 index)
  ==>
  channel1 = channel2
Proof
INTRO_TAC THEN
IRTAC word_lemmasTheory.LEQ_MAX_IMPLIES_DISTINCT_GT_MAX_LEMMA THEN
ALL_LRTAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
RW_HYP_LEMMA_TAC boolTheory.EQ_SYM_EQ THEN
STAC
QED

Theorem UPDATING_NEXT_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_IMPLIES_CHANNEL_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory internal_state channels channels1 channels2 n index channel1' channel2' bds_to_fetch' channel2.
  SUC n < dimword (: 'channel_index_width) /\
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS device_characteristics memory internal_state channels channels2 (n2w n) /\
  channels = ((n2w n + 1w) =+ SOME channel2) channels1 /\
  index <=+ n2w n /\
  bds_to_fetch' = (cverification device_characteristics index).bds_to_fetch memory internal_state /\
  channel2' = THE (channels2 index) /\
  channel1' = THE (channels1 index)
  ==>
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL channel1' channel2' bds_to_fetch'
Proof
INTRO_TAC THEN
ETAC EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS THEN
AITAC THEN
ITAC UPDATING_SUC_PRESERVES_CHANNELS_LEMMA THEN
STAC
QED

Theorem APPEND_BDS_CHANNEL_AND_PRESERVED_CHANNELS_IMPLIES_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_LEMMA:
!(channels1 : ('channel_index_width) channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels  : ('channel_index_width) channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels2 : ('channel_index_width) channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 n bds_to_fetch channel1 channel2 channel2'.
  SUC n < dimword (: 'channel_index_width) /\
  PRESERVED_CHANNELS channels channels2 (n2w n) /\
  channels = ((n2w n + 1w) =+ SOME channel2) channels1 /\
  channel1 = THE (channels1 (n2w n + 1w)) /\
  channel2 = append_bds_channel channel1 bds_to_fetch /\
  channel2' = THE (channels2 (n2w n + 1w))
  ==>
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL channel1 channel2' bds_to_fetch
Proof
INTRO_TAC THEN
ITAC APPEND_BDS_CHANNEL_EXTENDS_ABSTRACT_BDS_TO_FETCH_OR_PRESERVES_CHANNEL_LEMMA THEN
ITAC internal_operation_lemmasTheory.UPDATING_ACCESSED_CHANNEL_AND_PRESERVED_CHANNELS_IMPLIES_SAME_CHANNELS_LEMMA THEN
RLTAC THEN
STAC
QED

Theorem EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_SUC_LEMMA:
!n
 (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory internal_state channel1 channel2 channels1 channels channels2 bds_to_fetch.
  SUC n < dimword (: 'channel_index_width) /\
  bds_to_fetch = (cverification device_characteristics (n2w n + 1w)).bds_to_fetch memory internal_state /\
  channel1 = THE (channels1 (n2w n + 1w)) /\
  channel2 = append_bds_channel channel1 bds_to_fetch /\
  channels = ((n2w n + 1w) =+ SOME channel2) channels1 /\
  PRESERVED_CHANNELS channels channels2 (n2w n) /\
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS device_characteristics memory internal_state channels channels2 (n2w n)
  ==>
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS device_characteristics memory internal_state channels1 channels2 (n2w n + 1w)
Proof
INTRO_TAC THEN
REWRITE_TAC [EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS] THEN
INTRO_TAC THEN
IRTAC word_lemmasTheory.WORD_LEQ_SUC_IMPLIES_LEQ_OR_EQ_SUC_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 IRTAC UPDATING_NEXT_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_IMPLIES_CHANNEL_LEMMA THEN
 STAC
 ,
 LRTAC THEN
 RLTAC THEN
 RLTAC THEN
 FITAC APPEND_BDS_CHANNEL_AND_PRESERVED_CHANNELS_IMPLIES_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_LEMMA THEN
 STAC
]
QED

Theorem APPEND_BDS_CHANNEL_NOT_ZERO_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_LEMMA:
!n
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
(channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
(channels' : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
(channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 memory internal_state bds_to_fetch channel channel'.
  SUC n < dimword (: 'channel_index_width) /\
  (!channels1 channels2.
     APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS
       device_characteristics memory channels1 channels2 internal_state (n2w n)) /\
  n2w n + 1w <> 0w /\
  bds_to_fetch = (cverification device_characteristics (n2w n + 1w)).bds_to_fetch memory internal_state /\
  channel = THE (channels1 (n2w n + 1w)) /\
  channel' = append_bds_channel channel bds_to_fetch /\
  channels' = (((n2w n + 1w) =+ SOME channel')) channels1 /\
  channels2 = append_bds_channels_index device_characteristics.dma_characteristics memory channels' internal_state (n2w n)
  ==>
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS device_characteristics memory internal_state channels1 channels2 (n2w n + 1w)
Proof
INTRO_TAC THEN
RW_HYPS_TAC APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS THEN
AIRTAC THEN
IRTAC EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_SUC_LEMMA THEN
STAC
QED

Theorem APPEND_BDS_CHANNEL_NOT_ZERO_PRESERVED_CHANNELS_LEMMA:
!n
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
(channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
(channels  : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
(channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 memory internal_state bds_to_fetch channel1 channel2.
  SUC n < dimword (: 'channel_index_width) /\
  (!channels1 channels2.
     APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS
       device_characteristics memory channels1 channels2 internal_state (n2w n)) /\
  bds_to_fetch = (cverification device_characteristics (n2w n + 1w)).bds_to_fetch memory internal_state /\
  channel1 = THE (channels1 (n2w n + 1w)) /\
  channel2 = append_bds_channel channel1 bds_to_fetch /\
  channels = ((n2w n + 1w) =+ SOME channel2) channels1 /\
  n2w n + 1w <> 0w /\
  channels2 = append_bds_channels_index device_characteristics.dma_characteristics memory channels internal_state (n2w n)
  ==>
  PRESERVED_CHANNELS channels1 channels2 (n2w n + 1w)
Proof
INTRO_TAC THEN
RW_HYPS_TAC APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS THEN
FAITAC THEN
FIRTAC internal_operation_lemmasTheory.PRESERVED_CHANNELS_IMPLIES_NEXT_INDEX_LEMMA THEN
STAC
QED

Theorem APPEND_BDS_CHANNELS_SUC_IMPLIES_DEFINED_PRESERVED_CHANNELS_LEMMA:
!n
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
(channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
(channels  : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
(channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 memory internal_state channel.
  SUC n < dimword (: 'channel_index_width) /\
  (!channels1 channels2.
     APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS
       device_characteristics memory channels1 channels2 internal_state (n2w n)) /\
  n2w n + 1w <> 0w /\
  channels = ((n2w n + 1w) =+ SOME channel) channels1 /\
  channels2 = append_bds_channels_index device_characteristics.dma_characteristics memory channels internal_state (n2w n)
  ==>
  DEFINED_PRESERVED_CHANNELS channels1 channels2 (n2w n + 1w)
Proof
INTRO_TAC THEN
RW_HYPS_TAC APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS THEN
AIRTAC THEN
ETAC DEFINED_PRESERVED_CHANNELS THEN
CONJS_TAC THENL
[
 INTRO_TAC THEN
 ETAC wordsTheory.WORD_LOWER_OR_EQ THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  IRTAC word_lemmasTheory.WORD_LT_SUC_IMPLIES_LEQ_LEMMA THEN
  AIRTAC THEN
  STAC
  ,
  ITAC word_lemmasTheory.EQ_SUC_IMPLIES_GT_LEMMA THEN
  FAIRTAC THEN
  RLTAC THEN
  LRTAC THEN
  LRTAC THEN
  REWRITE_TAC [combinTheory.UPDATE_def] THEN
  APP_SCALAR_TAC THEN
  REWRITE_TAC [optionTheory.IS_SOME_DEF]
 ]
 ,
 INTRO_TAC THEN
 ITAC (REWRITE_RULE [GSYM wordsTheory.WORD_HIGHER] wordsTheory.WORD_LOWER_NOT_EQ) THEN 
 IRTAC word_lemmasTheory.GT_SUC_IMPLIES_GT_LEMMA THEN 
 FAIRTAC THEN
 RLTAC THEN
 LRTAC THEN
 REWRITE_TAC [combinTheory.UPDATE_def] THEN
 APP_SCALAR_TAC THEN
 STAC
]
QED

Theorem APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_INDUCTION_LEMMA:
!n device_characteristics memory internal_state.
  SUC n < dimword (: 'b)
  ==>
  (!channels1 channels2.
    APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS
      device_characteristics memory channels1 channels2 internal_state (n2w n : 'b word))
  ==>
  (!channels1 channels2.
    APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS
      device_characteristics memory channels1 channels2 internal_state (n2w (SUC n)))
Proof
INTRO_TAC THEN
INTRO_TAC THEN
REWRITE_TAC [APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS] THEN
INTRO_TAC THEN
PTAC operationsTheory.append_bds_channels_index THENL
[
 RLTAC THEN
 ETAC (GSYM stateTheory.cverification) THEN
 ITAC APPEND_BDS_CHANNEL_EXTENDS_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_ZERO_LEMMA THEN
 STAC
 ,
 ETAC wordsTheory.n2w_SUC THEN
 ETAC wordsTheory.WORD_ADD_SUB THEN
 ETAC (GSYM stateTheory.cverification) THEN
 ITAC APPEND_BDS_CHANNEL_NOT_ZERO_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_LEMMA THEN
 ITAC APPEND_BDS_CHANNEL_NOT_ZERO_PRESERVED_CHANNELS_LEMMA THEN
 ITAC APPEND_BDS_CHANNELS_SUC_IMPLIES_DEFINED_PRESERVED_CHANNELS_LEMMA THEN
 STAC
]
QED

Theorem APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_LEMMA:
!index device_characteristics memory channels1 channels2 internal_state.
  APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS
    device_characteristics memory channels1 channels2 internal_state index
Proof
ABS_APP_TAC THEN
MATCH_MP_TAC wordsTheory.WORD_INDUCT THEN
BETA_TAC THEN
CONJ_TAC THENL
[
 REPEAT GEN_TAC THEN
 PTAC APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS THEN
 INTRO_TAC THEN
 PTAC operationsTheory.append_bds_channels_index THEN (TRY (CONTR_NEG_ASM_TAC boolTheory.EQ_REFL)) THEN
 ETAC (GSYM stateTheory.cverification) THEN
 IRTAC APPEND_BDS_CHANNEL_EXTENDS_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_ZERO_LEMMA THEN
 STAC
 ,
 INTRO_TAC THEN
 INTRO_TAC THEN
 REPEAT GEN_TAC THEN
 ITAC APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_INDUCTION_LEMMA THEN
 INST_IMP_ASM_GOAL_TAC THEN
 STAC
]
QED

Theorem APPEND_BDS_CHANNELS_IMPLIES_IS_SOME_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 memory internal_state index.
  channels2 = append_bds_channels device_characteristics.dma_characteristics memory channels1 internal_state /\
  VALID_CHANNEL_ID device_characteristics index
  ==>
  IS_SOME (channels2 index)
Proof
INTRO_TAC THEN
PTAC append_bds_channels THEN
IRTAC (REWRITE_RULE [APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS] APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_LEMMA) THEN
ETAC DEFINED_PRESERVED_CHANNELS THEN
IRTAC state_lemmasTheory.VALID_CHANNEL_ID_IMPLIES_LEQ_MAX_LEMMA THEN
AIRTAC THEN
STAC
QED

Theorem APPEND_BDS_CHANNELS_IMPLIES_EQ_IS_SOME_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 memory internal_state channel_id.
  channels2 = append_bds_channels device_characteristics.dma_characteristics memory channels1 internal_state /\
  ~VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  IS_SOME (channels2 channel_id) = IS_SOME (channels1 channel_id)
Proof
INTRO_TAC THEN
PTAC append_bds_channels THEN
IRTAC (REWRITE_RULE [APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS] APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_LEMMA) THEN
ETAC DEFINED_PRESERVED_CHANNELS THEN
IRTAC state_lemmasTheory.NOT_VALID_CHANNEL_ID_IMPLIES_INDEX_GT_MAX_LEMMA THEN
FAIRTAC THEN
STAC
QED

Theorem APPEND_BDS_CHANNELS_IMPLIES_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 memory internal_state.
  channels2 = append_bds_channels device_characteristics.dma_characteristics memory channels1 internal_state
  ==>
  !index channel1 channel2 bds_to_fetch.
    VALID_CHANNEL_ID device_characteristics index /\
    bds_to_fetch = (cverification device_characteristics index).bds_to_fetch memory internal_state /\
    channel1 = THE (channels1 index) /\
    channel2 = THE (channels2 index) 
    ==>
    EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL channel1 channel2 bds_to_fetch
Proof
INTRO_TAC THEN
INTRO_TAC THEN
PTAC append_bds_channels THEN
ITAC (REWRITE_RULE [APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS]
      APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_LEMMA) THEN
ETAC EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS THEN
IRTAC state_lemmasTheory.VALID_CHANNEL_ID_IMPLIES_LEQ_MAX_LEMMA THEN
AIRTAC THEN
STAC
QED

Theorem APPEND_BDS_CHANNELS_EXTENDS_OR_PRESERVES_ALL_CHANNELS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 memory internal_state channel_id channel1 channel2 bds_to_fetch.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channels2 = append_bds_channels device_characteristics.dma_characteristics memory channels1 internal_state /\
  channel1 = THE (channels1 channel_id) /\
  channel2 = THE (channels2 channel_id) /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state
  ==>
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL channel1 channel2 bds_to_fetch
Proof
INTRO_TAC THEN
IRTAC APPEND_BDS_CHANNELS_IMPLIES_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_LEMMA THEN
AIRTAC THEN
STAC
QED

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id channel1 channel2 bds_to_fetch.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  device2 = dma_append_external_abstract_bds device_characteristics memory device1 /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory device1.dma_state.internal_state /\
  channel1 = schannel device1 channel_id /\
  channel2 = schannel device2 channel_id
  ==>
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL channel1 channel2 bds_to_fetch
Proof
INTRO_TAC THEN
PTAC dma_append_external_abstract_bds THEN
LRTAC THEN
ETAC schannel THEN
RECORD_TAC THEN
MATCH_MP_TAC APPEND_BDS_CHANNELS_EXTENDS_OR_PRESERVES_ALL_CHANNELS_LEMMA THEN
PAXTAC THEN
STAC
QED

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_SOME_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  device2 = dma_append_external_abstract_bds device_characteristics memory device1
  ==>
  IS_SOME (device2.dma_state.channels channel_id)
Proof
INTRO_TAC THEN
PTAC dma_append_external_abstract_bds THEN
MATCH_MP_TAC APPEND_BDS_CHANNELS_IMPLIES_IS_SOME_LEMMA THEN
LRTAC THEN
RECORD_TAC THEN
PAXTAC THEN
EXISTS_EQ_TAC THEN
STAC
QED

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_SOME_PRESERVED_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id.
  ~VALID_CHANNEL_ID device_characteristics channel_id /\
  device2 = dma_append_external_abstract_bds device_characteristics memory device1
  ==>
  IS_SOME (device2.dma_state.channels channel_id) = IS_SOME (device1.dma_state.channels channel_id)
Proof
INTRO_TAC THEN
PTAC dma_append_external_abstract_bds THEN
MATCH_MP_TAC APPEND_BDS_CHANNELS_IMPLIES_EQ_IS_SOME_LEMMA THEN
LRTAC THEN
RECORD_TAC THEN
PAXTAC THEN
EXISTS_EQ_TAC THEN
STAC
QED

val _ = export_theory();

