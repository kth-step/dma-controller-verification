open HolKernel Parse boolLib bossLib helper_tactics;
open L23EQTheory stateTheory access_propertiesTheory;

val _ = new_theory "collect_dma_state_lemmas";

Theorem L23EQ_IMPLIES_EQ_CHANNEL_STATE_COMPONENTS_LEMMA:
!device_characteristics memory device2 device3 channel2 channel3 channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  L23EQ device_characteristics memory device2 device3 /\
  channel2 = schannel device2 channel_id /\
  channel3 = schannel device3 channel_id
  ==>
  channel_state_components channel3 = channel_state_components channel2
Proof
INTRO_TAC THEN
REPEAT (PTAC operationsTheory.channel_state_components) THEN
ALL_LRTAC THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
ETAC L23EQ THEN
ETAC stateTheory.BDS_TO_UPDATE_EQ THEN
AITAC THEN
ETAC stateTheory.BDS_TO_PROCESS_EQ THEN
AITAC THEN
ETAC stateTheory.BDS_TO_WRITE_BACK_EQ THEN
AITAC THEN
ETAC stateTheory.MEMORY_REQUESTS_REPLIES_EQ THEN
AITAC THEN
STAC
QED

Theorem L23EQ_CHANNEL_STATE_COMPONENTS_PRESERVES_COLLECTED_STATE_COMPONENTS_LEMMA:
!device_characteristics memory device2 device3 channels2 channels3 channel2
 channel3 channel_id state_components2 state_components3
 collected_state_components channels_state_components2 channels_state_components3.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  L23EQ device_characteristics memory device2 device3 /\
  channels2 = device2.dma_state.channels /\
  channels3 = device3.dma_state.channels /\
  channel2 = THE (channels2 channel_id) /\
  channel3 = THE (channels3 channel_id) /\
  state_components2 = channel_state_components channel2 /\
  state_components3 = channel_state_components channel3 /\
  channels_state_components2 = (channel_id =+ SOME state_components2) collected_state_components /\
  channels_state_components3 = (channel_id =+ SOME state_components3) collected_state_components
  ==>
  channels_state_components3 = channels_state_components2
Proof
INTRO_TAC THEN
FIRTAC L23EQ_IMPLIES_EQ_CHANNEL_STATE_COMPONENTS_LEMMA THEN
ETAC stateTheory.schannel THEN
ALL_LRTAC THEN
STAC
QED

Theorem COLLECTED_STATE_COMPONENTS_IND_LEMMA:
!device_characteristics memory device21 device31.
  L23EQ device_characteristics memory device21 device31
  ==>
  !channels21 channel_id collected_state_components.
    (\channels21 collected_state_components channel_id.
      !channels31.
        channels21 = device21.dma_state.channels /\
        channels31 = device31.dma_state.channels /\
        VALID_CHANNEL_ID device_characteristics channel_id
        ==>
        collect_channel_state_components_index channels31 collected_state_components channel_id =
        collect_channel_state_components_index channels21 collected_state_components channel_id) channels21 collected_state_components channel_id
Proof
INTRO_TAC THEN
MATCH_MP_TAC operationsTheory.collect_channel_state_components_index_ind THEN
APP_SCALAR_TAC THEN
INTRO_TAC THEN
INTRO_TAC THEN
ETAC operationsTheory.collect_channel_state_components_index THEN
LETS_TAC THEN
IF_SPLIT_TAC THENL
[
 LRTAC THEN
 WEAKEN_TAC is_forall THEN
 FITAC L23EQ_IMPLIES_EQ_CHANNEL_STATE_COMPONENTS_LEMMA THEN
 IRTAC L23EQ_CHANNEL_STATE_COMPONENTS_PRESERVES_COLLECTED_STATE_COMPONENTS_LEMMA THEN
 STAC
 ,
 ITAC L23EQ_CHANNEL_STATE_COMPONENTS_PRESERVES_COLLECTED_STATE_COMPONENTS_LEMMA THEN
 RLTAC THEN
 AITAC THEN
 IRTAC state_lemmasTheory.VALID_CHANNEL_ID_NOT_ZERO_IMPLIES_VALID_CHANNEL_PRE_LEMMA THEN
 AIRTAC THEN
 STAC
]
QED

Theorem COLLECTED_STATE_COMPONENTS_LEMMA:
!device_characteristics memory device21 device31.
  L23EQ device_characteristics memory device21 device31
  ==>
  !channels21 channels31 channel_id collected_state_components.
    channels21 = device21.dma_state.channels /\
    channels31 = device31.dma_state.channels /\
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    collect_channel_state_components_index channels31 collected_state_components channel_id =
    collect_channel_state_components_index channels21 collected_state_components channel_id
Proof
INTRO_TAC THEN
IRTAC (BETA_RULE COLLECTED_STATE_COMPONENTS_IND_LEMMA) THEN
STAC
QED

Theorem L23EQ_IMPLIES_COLLECT_CHANNEL_STATE_INDEX_EQ_LEMMA:
!device_characteristics memory device21 device31 max_index.
  L23EQ device_characteristics memory device21 device31 /\
  max_index = device_characteristics.dma_characteristics.max_index
  ==>
  !channels_state_components.
    collect_channel_state_components_index device31.dma_state.channels channels_state_components max_index =
    collect_channel_state_components_index device21.dma_state.channels channels_state_components max_index
Proof
INTRO_TAC THEN
GEN_TAC THEN
ITAC COLLECTED_STATE_COMPONENTS_LEMMA THEN
ITAC state_lemmasTheory.MAX_INDEX_VALID_CHANNEL_LEMMA THEN
AIRTAC THEN
STAC
QED

Theorem L23EQ_IMPLIES_COLLECT_CHANNELS_STATE_EQ_LEMMA:
!device_characteristics memory device21 device31.
  L23EQ device_characteristics memory device21 device31
  ==>
  collect_channels_state device_characteristics.dma_characteristics device31.dma_state.channels =
  collect_channels_state device_characteristics.dma_characteristics device21.dma_state.channels
Proof
INTRO_TAC THEN
PTAC operationsTheory.collect_channels_state THEN
PTAC operationsTheory.collect_channels_state THEN
ITAC L23EQ_IMPLIES_COLLECT_CHANNEL_STATE_INDEX_EQ_LEMMA THEN
QLRTAC THEN
RLTAC THEN
STAC
QED

Theorem L23EQ_IMPLIES_COLLECT_DMA_STATE_EQ_LEMMA:
!device_characteristics memory device21 device31.
  L23EQ device_characteristics memory device21 device31
  ==>
  collect_dma_state device_characteristics.dma_characteristics device31.dma_state =
  collect_dma_state device_characteristics.dma_characteristics device21.dma_state
Proof
INTRO_TAC THEN
REPEAT (PTAC operationsTheory.collect_dma_state) THEN
ITAC L23EQ_IMPLIES_COLLECT_CHANNELS_STATE_EQ_LEMMA THEN
LRTAC THEN
RLTAC THEN
LRTAC THEN
ITAC L23EQ_lemmasTheory.L23EQ_IMPLIES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_EQ_LEMMA THEN
LRTAC THEN
RLTAC THEN
LRTAC THEN
IRTAC L23EQ_lemmasTheory.L23EQ_IMPLIES_PENDING_REGISTER_RELATED_MEMORY_REPLIES_EQ_LEMMA THEN
LRTAC THEN
RLTAC THEN
LRTAC THEN
STAC
QED

Theorem L23EQ_IMPLIES_CHANNELS_TO_PIPELINES_EQ_LEMMA:
!device_characteristics memory device2 device3.
  L23EQ device_characteristics memory device2 device3
  ==>
  collect_channels_state device_characteristics.dma_characteristics device2.dma_state.channels = collect_channels_state device_characteristics.dma_characteristics device3.dma_state.channels
Proof
INTRO_TAC THEN
IRTAC L23EQ_IMPLIES_COLLECT_DMA_STATE_EQ_LEMMA THEN
ETAC operationsTheory.collect_dma_state THEN
LETS_TAC THEN
ALL_LRTAC THEN
EQ_PAIR_ASM_TAC THEN
STAC
QED

Theorem COLLECTED_STATE_COMPONENTS_PRESERVED_INDUCTION_LEMMA:
!channels collected_state_components1 channel_id1.
 (\channels collected_state_components1 channel_id1.
   !collected_state_components2 channel_id2 .
     collected_state_components2 = (collect_channel_state_components_index channels collected_state_components1 channel_id1) /\
     MEASURE_CHANNEL_ID channel_id1 channel_id2
     ==>
     THE (collected_state_components2 channel_id2) = THE (collected_state_components1 channel_id2)
 ) channels collected_state_components1 channel_id1
Proof
REPEAT GEN_TAC THEN
MATCH_MP_TAC operationsTheory.collect_channel_state_components_index_ind THEN
APP_SCALAR_TAC THEN
INTRO_TAC THEN
INTRO_TAC THEN
ETAC operationsTheory.collect_channel_state_components_index THEN
LETS_TAC THEN
IF_SPLIT_TAC THENL
[
 WEAKEN_TAC is_forall THEN
 ALL_LRTAC THEN
 ETAC operationsTheory.MEASURE_CHANNEL_ID THEN
 REWRITE_TAC [combinTheory.UPDATE_def] THEN
 APP_SCALAR_TAC THEN
 ETAC wordsTheory.WORD_LO_word_0 THEN
 LEMMA_ASM_TAC boolTheory.EQ_SYM_EQ THEN
 ASM_REWRITE_TAC []
 ,
 RW_HYPS_TAC operationsTheory.MEASURE_CHANNEL_ID THEN
 ITAC wordsTheory.WORD_LOWER_NOT_EQ THEN
 AITAC THEN
 IRTAC word_lemmasTheory.NEQ_ZERO_LE_IMPLIES_PRED_LE_LEMMA THEN
 AITAC THEN
 LRTAC THEN
 LRTAC THEN
 REWRITE_TAC [combinTheory.UPDATE_def] THEN
 APP_SCALAR_TAC THEN
 ASM_REWRITE_TAC []
]
QED

Theorem COLLECTED_STATE_COMPONENTS_PRESERVED_LEMMA:
!channels collected_state_components1 collected_state_components2 channel_id1 channel_id2.
  collected_state_components2 = (collect_channel_state_components_index channels collected_state_components1 channel_id1) /\
  MEASURE_CHANNEL_ID channel_id1 channel_id2
  ==>
  THE (collected_state_components2 channel_id2) = THE (collected_state_components1 channel_id2)
Proof
INTRO_TAC THEN
IRTAC (BETA_RULE COLLECTED_STATE_COMPONENTS_PRESERVED_INDUCTION_LEMMA) THEN
STAC
QED

Theorem EQ_BD_QUEUES_COLLECTED_STATE_COMPONENTS_INDUCTION_LEMMA:
!device_characteristics device1 device2.
  (!channel_id. VALID_CHANNEL_ID device_characteristics channel_id
     ==>
     (THE (device2.dma_state.channels channel_id)).queue = (THE (device1.dma_state.channels channel_id)).queue)
  ==>
  !channels1 collected_state_components11 channel_id1.
 (\channels1 collected_state_components11 channel_id1.
   !channels2 collected_state_components21 channel_id2 collected_state_components12 collected_state_components22.
     VALID_CHANNEL_ID device_characteristics channel_id1 /\
     channels1 = device1.dma_state.channels /\
     channels2 = device2.dma_state.channels /\
     collected_state_components12 = (collect_channel_state_components_index channels1 collected_state_components11 channel_id1) /\
     collected_state_components22 = (collect_channel_state_components_index channels2 collected_state_components21 channel_id1) /\
     channel_id2 <=+ channel_id1
     ==>
     SND (THE (collected_state_components22 channel_id2)) = SND (THE (collected_state_components12 channel_id2))
 ) channels1 collected_state_components11 channel_id1
Proof
INTRO_TAC THEN
MATCH_MP_TAC operationsTheory.collect_channel_state_components_index_ind THEN
APP_SCALAR_TAC THEN
INTRO_TAC THEN
INTRO_TAC THEN
ETAC operationsTheory.collect_channel_state_components_index THEN
LETS_TAC THEN
IF_SPLIT_TAC THENL
[
 LRTAC THEN
 WEAKEN_TAC is_forall THEN
 AIRTAC THEN
 ALL_RLTAC THEN
 ALL_LRTAC THEN
 ETAC operationsTheory.channel_state_components THEN
 LETS_TAC THEN
 ALL_LRTAC THEN
 ETAC combinTheory.UPDATE_def THEN
 APP_SCALAR_TAC THEN
 ETAC wordsTheory.WORD_LS_word_0 THEN
 LRTAC THEN
 REWRITE_TAC [optionTheory.THE_DEF]
 ,
 ETAC wordsTheory.WORD_LOWER_OR_EQ  THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  AITAC THEN
  INST_IMP_ASM_GOAL_TAC THEN
  ITAC state_lemmasTheory.VALID_CHANNEL_ID_NOT_ZERO_IMPLIES_VALID_CHANNEL_PRE_LEMMA THEN
  ITAC word_lemmasTheory.LE_IMPLIES_LEQ_PRED_LEMMA THEN
  ASM_REWRITE_TAC [VALID_CHANNEL_ID]
  ,
   WEAKEN_TAC is_forall THEN
   RLTAC THEN
   ITAC word_lemmasTheory.NEQ_ZERO_EQ_IMPLIES_PRE_LE_LEMMA THEN
   IRTAC word_lemmasTheory.NEQ_ZERO_EQ_IMPLIES_PRE_LE_LEMMA THEN
   IRTAC (REWRITE_RULE [operationsTheory.MEASURE_CHANNEL_ID] COLLECTED_STATE_COMPONENTS_PRESERVED_LEMMA) THEN
   IRTAC (REWRITE_RULE [operationsTheory.MEASURE_CHANNEL_ID] COLLECTED_STATE_COMPONENTS_PRESERVED_LEMMA) THEN
   ALL_LRTAC THEN
   REWRITE_TAC [combinTheory.UPDATE_def] THEN
   BETA_TAC THEN
   REWRITE_TAC [] THEN
   AIRTAC THEN
   ETAC operationsTheory.channel_state_components THEN
   LRTAC THEN
   LETS_TAC THEN
   ASM_REWRITE_TAC [optionTheory.THE_DEF]
  ]
 ]
QED

Theorem EQ_BD_QUEUES_COLLECTED_STATE_COMPONENTS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  (!channel_id.
     VALID_CHANNEL_ID device_characteristics channel_id ==> (schannel device2 channel_id).queue = (schannel device1 channel_id).queue)
  ==>
  !channel_id1 channel_id2 channels1 channels2
   collected_state_components11 collected_state_components21 collected_state_components12 collected_state_components22.
     VALID_CHANNEL_ID device_characteristics channel_id1 /\
     channels1 = device1.dma_state.channels /\
     channels2 = device2.dma_state.channels /\
     collected_state_components12 = (collect_channel_state_components_index channels1 collected_state_components11 channel_id1) /\
     collected_state_components22 = (collect_channel_state_components_index channels2 collected_state_components21 channel_id1) /\
     channel_id2 <=+ channel_id1
     ==>
     SND (THE (collected_state_components22 channel_id2)) = SND (THE (collected_state_components12 channel_id2))
Proof
REWRITE_TAC [stateTheory.schannel] THEN
INTRO_TAC THEN
IRTAC (BETA_RULE EQ_BD_QUEUES_COLLECTED_STATE_COMPONENTS_INDUCTION_LEMMA) THEN
STAC
QED

Theorem COLLECT_CHANNEL_STATE_CHANNEL_ID_IMPLIES_COLLECTED_STATE_COMPONENTS_EQ_INDUCTION_LEMMA:
!channels channel_id1 collected_state_components1.
   (\channels collected_state_components1 channel_id1.
   !          collected_state_components2 channel_id2.
   channel_id1 <+ channel_id2 /\
   collected_state_components2 = collect_channel_state_components_index channels collected_state_components1 channel_id1
   ==>
   collected_state_components2 channel_id2 = collected_state_components1 channel_id2)
    channels collected_state_components1 channel_id1
Proof
MATCH_MP_TAC operationsTheory.collect_channel_state_components_index_ind THEN
APP_SCALAR_TAC THEN
INTRO_TAC THEN
INTRO_TAC THEN
ETAC operationsTheory.collect_channel_state_components_index THEN
LETS_TAC THEN
IF_SPLIT_TAC THENL
[
 IRTAC wordsTheory.WORD_LOWER_NOT_EQ THEN
 ALL_LRTAC THEN
 REWRITE_TAC [combinTheory.UPDATE_def] THEN
 BETA_TAC THEN
 ASM_REWRITE_TAC [operationsTheory.channel_state_components]
 ,
 ITAC word_lemmasTheory.NEQ_ZERO_LE_IMPLIES_PRED_LE_LEMMA THEN
 AITAC THEN
 AITAC THEN
 ALL_LRTAC THEN
 REWRITE_TAC [combinTheory.UPDATE_def] THEN
 BETA_TAC THEN
 IRTAC wordsTheory.WORD_LOWER_NOT_EQ THEN
 IRTAC wordsTheory.WORD_LOWER_NOT_EQ THEN
 ASM_REWRITE_TAC []
]
QED

Theorem COLLECT_CHANNEL_STATE_CHANNEL_ID_IMPLIES_COLLECTED_STATE_COMPONENTS_EQ_LEMMA:
!channels channel_id1 channel_id2
 collected_state_components1 collected_state_components2.
  channel_id1 <+ channel_id2 /\
  collected_state_components2 = collect_channel_state_components_index channels collected_state_components1 channel_id1
  ==>
  collected_state_components2 channel_id2 = collected_state_components1 channel_id2
Proof
INTRO_TAC THEN
IRTAC (BETA_RULE COLLECT_CHANNEL_STATE_CHANNEL_ID_IMPLIES_COLLECTED_STATE_COMPONENTS_EQ_INDUCTION_LEMMA) THEN
STAC
QED

Definition COLLECTED_STATE_QUEUES_EQ:
COLLECTED_STATE_QUEUES_EQ device_characteristics collected_state_components1 collected_state_components2 =
!i.
  VALID_CHANNEL_ID device_characteristics i
  ==>
  SND (THE (collected_state_components1 i)) = SND (THE (collected_state_components2 i))
End

Definition COLLECTED_STATE_COMPONENTS_EQ:
COLLECTED_STATE_COMPONENTS_EQ collected_state_components1 collected_state_components2 =
!i. collected_state_components1 i = collected_state_components2 i
End

Theorem COLLECTED_STATE_COMPONENTS_EQ_LEMMA:
!collected_state_components.
  COLLECTED_STATE_COMPONENTS_EQ collected_state_components collected_state_components
Proof
REWRITE_TAC [COLLECTED_STATE_COMPONENTS_EQ]
QED

Definition QUEUES_EQ:
QUEUES_EQ
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
(device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
(device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) =
!channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  (schannel device2 channel_id).queue = (schannel device1 channel_id).queue
End

Theorem COLLECTED_STATE_QUEUES_EQ_LEMMA:
!device_characteristics collected_state_components.
  COLLECTED_STATE_QUEUES_EQ device_characteristics collected_state_components collected_state_components
Proof
REWRITE_TAC [COLLECTED_STATE_QUEUES_EQ]
QED

Theorem COLLECTED_STATE_QUEUES_EQ_SYM_LEMMA:
!device_characteristics collected_state_components1 collected_state_components2.
  COLLECTED_STATE_QUEUES_EQ device_characteristics collected_state_components1 collected_state_components2 =
  COLLECTED_STATE_QUEUES_EQ device_characteristics collected_state_components2 collected_state_components1
Proof
REWRITE_TAC [COLLECTED_STATE_QUEUES_EQ] THEN
REPEAT GEN_TAC THEN
EQ_TAC THEN
 INTRO_TAC THEN
 INTRO_TAC THEN
 AIRTAC THEN
 STAC
QED

Theorem COLLECT_CHANNEL_STATE_COMPONENTS_INDEX_IMPLIES_COLLECTED_STATE_QUEUES_EQ_LEMMA:
!device_characteristics device1 device2 max_index
 collected_state_components11 collected_state_components21
 collected_state_components12 collected_state_components22.
  QUEUES_EQ device_characteristics device1 device2 /\
  max_index = device_characteristics.dma_characteristics.max_index /\
  collected_state_components12 = collect_channel_state_components_index device1.dma_state.channels collected_state_components11 max_index /\
  collected_state_components22 = collect_channel_state_components_index device2.dma_state.channels collected_state_components21 max_index
  ==>
  COLLECTED_STATE_QUEUES_EQ device_characteristics collected_state_components12 collected_state_components22
Proof
INTRO_TAC THEN
PTAC COLLECTED_STATE_QUEUES_EQ THEN
INTRO_TAC THEN
IRTAC (REWRITE_RULE [GSYM QUEUES_EQ] EQ_BD_QUEUES_COLLECTED_STATE_COMPONENTS_LEMMA) THEN
ITAC state_lemmasTheory.VALID_CHANNEL_ID_IMPLIES_LEQ_MAX_LEMMA THEN
ITAC state_lemmasTheory.SOME_MAX_INDEX_IMP_VALID_CHANNEL_ID_LEMMA THEN
AIRTAC THEN
STAC
QED

Theorem QUEUES_EQ_COLLECT_CHANNELS_STATE_IMPLIES_QUEUES_EQ_LEMMA:
!device_characteristics device1 device2 collected_state_components1 collected_state_components2.
  QUEUES_EQ device_characteristics device1 device2 /\
  collected_state_components1 = collect_channels_state device_characteristics.dma_characteristics device1.dma_state.channels /\
  collected_state_components2 = collect_channels_state device_characteristics.dma_characteristics device2.dma_state.channels
  ==>
  COLLECTED_STATE_QUEUES_EQ device_characteristics collected_state_components1 collected_state_components2
Proof
INTRO_TAC THEN
ETAC operationsTheory.collect_channels_state THEN
LETS_TAC THEN
IRTAC COLLECT_CHANNEL_STATE_COMPONENTS_INDEX_IMPLIES_COLLECTED_STATE_QUEUES_EQ_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_IMPLIES_QUEUES_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 device1 device2
 (serviced_request : 8 word list # ('interconnect_address_width, 'tag_width) interconnect_request_type).
  device2 = dma_request_served device_characteristics device1 serviced_request
  ==>
  QUEUES_EQ device_characteristics device2 device1
Proof
INTRO_TAC THEN
ETAC QUEUES_EQ THEN
INTRO_TAC THEN
IRTAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_PRESERVES_PIPELINES_LEMMA THEN
STAC
QED

Theorem PIPELINES_EQ_IMPLIES_PIPELINE_BDS_EQ_LEMMA:
!pipelines1 pipelines2 channel_id.
  pipelines1 channel_id = pipelines2 channel_id
  ==>
  pipeline_bds pipelines2 channel_id = pipeline_bds pipelines1 channel_id
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.pipeline_bds THEN
STAC
QED

Theorem COLLECT_CHANNEL_STATE_COMPONENTS_INDEX_INVALID_CHANNEL_PRESERVES_COLLECTED_STATE_COMPONENTS_LEMMA:
!device_characteristics channels collected_state_components1 collected_state_components2 channel_id.
  collected_state_components2 = collect_channel_state_components_index channels collected_state_components1 device_characteristics.dma_characteristics.max_index
  ==>
  ~VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  collected_state_components2 channel_id = collected_state_components1 channel_id
Proof
INTRO_TAC THEN
INTRO_TAC THEN
ETAC VALID_CHANNEL_ID THEN
ETAC wordsTheory.WORD_NOT_LOWER_EQUAL THEN
IRTAC COLLECT_CHANNEL_STATE_CHANNEL_ID_IMPLIES_COLLECTED_STATE_COMPONENTS_EQ_LEMMA THEN
STAC
QED

Theorem INVALID_CHANNEL_ID_COLLECT_CHANNELS_STATE_IMPLIES_COLLECTED_STATE_COMPONENTS_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 collected_state_components1 collected_state_components2
 channels1 channels2 channel_id.
  ~VALID_CHANNEL_ID device_characteristics channel_id /\
  collected_state_components1 = collect_channels_state device_characteristics.dma_characteristics channels1 /\
  collected_state_components2 = collect_channels_state device_characteristics.dma_characteristics channels2
  ==>
  collected_state_components2 channel_id = collected_state_components1 channel_id
Proof
REPEAT INTRO_TAC THEN
ETAC operationsTheory.collect_channels_state THEN
LETS_TAC THEN
IRTAC COLLECT_CHANNEL_STATE_COMPONENTS_INDEX_INVALID_CHANNEL_PRESERVES_COLLECTED_STATE_COMPONENTS_LEMMA THEN
AITAC THEN
IRTAC COLLECT_CHANNEL_STATE_COMPONENTS_INDEX_INVALID_CHANNEL_PRESERVES_COLLECTED_STATE_COMPONENTS_LEMMA THEN
AITAC THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_PRESERVES_PIPELINE_BDS_CHANNEL_ID_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id pipelines1 pipelines2
 (serviced_request : 8 word list # ('interconnect_address_width, 'tag_width) interconnect_request_type).
  device2 = dma_request_served device_characteristics device1 serviced_request /\
  pipelines1 = collect_channels_state device_characteristics.dma_characteristics device1.dma_state.channels /\
  pipelines2 = collect_channels_state device_characteristics.dma_characteristics device2.dma_state.channels
  ==>
  pipeline_bds pipelines2 channel_id = pipeline_bds pipelines1 channel_id
Proof
INTRO_TAC THEN
Cases_on ‘VALID_CHANNEL_ID device_characteristics channel_id’ THENL
[
 IRTAC DMA_REQUEST_SERVED_IMPLIES_QUEUES_EQ_LEMMA THEN
 IRTAC QUEUES_EQ_COLLECT_CHANNELS_STATE_IMPLIES_QUEUES_EQ_LEMMA THEN
 PTAC COLLECTED_STATE_QUEUES_EQ THEN
 AIRTAC THEN
 ETAC bd_queuesTheory.pipeline_bds THEN
 LETS_TAC THEN
 NLRTAC 2 THEN
 ETAC pairTheory.SND THEN
 EQ_PAIR_ASM_TAC THEN
 STAC
 ,
 MATCH_MP_TAC PIPELINES_EQ_IMPLIES_PIPELINE_BDS_EQ_LEMMA THEN
 MATCH_MP_TAC INVALID_CHANNEL_ID_COLLECT_CHANNELS_STATE_IMPLIES_COLLECTED_STATE_COMPONENTS_EQ_LEMMA THEN
 WEAKEN_TAC is_eq THEN
 ALL_LRTAC THEN
 EXISTS_EQ_TAC THEN
 STAC
]
QED

Theorem DMA_REQUEST_SERVED_PRESERVES_PIPELINE_BDS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 pipelines1 pipelines2
 (serviced_request : 8 word list # ('interconnect_address_width, 'tag_width) interconnect_request_type).
  device2 = dma_request_served device_characteristics device1 serviced_request /\
  pipelines1 = collect_channels_state device_characteristics.dma_characteristics device1.dma_state.channels /\
  pipelines2 = collect_channels_state device_characteristics.dma_characteristics device2.dma_state.channels
  ==>
  pipeline_bds pipelines2 = pipeline_bds pipelines1
Proof
INTRO_TAC THEN
REWRITE_TAC [boolTheory.FUN_EQ_THM] THEN
GEN_TAC THEN
IRTAC DMA_REQUEST_SERVED_PRESERVES_PIPELINE_BDS_CHANNEL_ID_LEMMA THEN
STAC
QED

val _ = export_theory();

