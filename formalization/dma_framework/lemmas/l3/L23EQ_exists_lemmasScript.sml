open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory operationsTheory L23EQTheory;

val _ = new_theory "L23EQ_exists_lemmas";

Definition set_bds_to_fetch_channel:
  (set_bds_to_fetch_channel bds_to_fetch NONE = NONE) /\
  (set_bds_to_fetch_channel bds_to_fetch (SOME channel) =
     SOME (channel with queue := channel.queue with bds_to_fetch := bds_to_fetch))
End

Definition set_bds_to_fetch_channels:
set_bds_to_fetch_channels device_characteristics memory internal_state channels channel_id =
  let bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state in
  let channel = set_bds_to_fetch_channel bds_to_fetch (channels channel_id) in
  let channels = (channel_id =+ channel) channels in
    channels
End

val set_bds_to_fetch_channels_index_tgoal = Hol_defn "set_bds_to_fetch_channels_index" ‘
set_bds_to_fetch_channels_index device_characteristics memory internal_state channels i =
  let channels = set_bds_to_fetch_channels device_characteristics memory internal_state channels i in
    if i = 0w then
      channels
    else
      set_bds_to_fetch_channels_index device_characteristics memory internal_state channels (i - 1w)’

Definition MEASURE_CHANNEL_ID_SET_BDS_TO_FETCH_CHANNELS_INDEX:
MEASURE_CHANNEL_ID_SET_BDS_TO_FETCH_CHANNELS_INDEX
  (device_characteristics1, memory1, internal_state1, channels1, channel_id1)
  (device_characteristics2, memory2, internal_state2, channels2, channel_id2) =
   MEASURE_CHANNEL_ID channel_id1 channel_id2
End

Definition measure_channel_id_set_bds_to_fetch_channels_index:
measure_channel_id_set_bds_to_fetch_channels_index (devuce_characteristics, memory, internal_state, channels, channel_id) =
  measure_channel_id channel_id
End

Theorem WF_MEASURE_CHANNEL_ID_SET_BDS_TO_FETCH_CHANNELS_INDEX_LEMMA:
WF (measure measure_channel_id_set_bds_to_fetch_channels_index)
Proof
REWRITE_TAC [prim_recTheory.WF_measure]
QED

Theorem MEASURE_CHANNEL_ID_SET_BDS_TO_FETCH_CHANNELS_INDEX_EQ_LEMMA:
MEASURE_CHANNEL_ID_SET_BDS_TO_FETCH_CHANNELS_INDEX = measure measure_channel_id_set_bds_to_fetch_channels_index
Proof
REPEAT (fn (A, t) =>
 let val l = lhs t
     val r = rhs t in
 let val l_type = type_of l
     val r_type = type_of r
     val thm_type = ((type_of o #1 o dest_forall o concl) boolTheory.ETA_AX) in
 let val l_matching = match_type thm_type l_type
     val r_matching = match_type thm_type r_type in
 let val l_type_thm = INST_TYPE l_matching boolTheory.ETA_AX
     val r_type_thm = INST_TYPE r_matching boolTheory.ETA_AX in
 let val l_thm = SYM (SPEC l l_type_thm)
     val r_thm = SYM (SPEC r r_type_thm) in
   (ONCE_REWRITE_TAC [l_thm, r_thm] THEN ABS_TAC) (A, t)
 end end end end end) THEN
Cases_on ‘x’ THEN Cases_on ‘x'’ THEN Cases_on ‘r’ THEN Cases_on ‘r'’ THEN Cases_on ‘r’ THEN Cases_on ‘r''’ THEN Cases_on ‘r’ THEN Cases_on ‘r'’ THEN
ETAC prim_recTheory.measure_thm THEN
REWRITE_TAC [MEASURE_CHANNEL_ID_SET_BDS_TO_FETCH_CHANNELS_INDEX, measure_channel_id_set_bds_to_fetch_channels_index] THEN
ETAC prim_recTheory.measure_thm THEN
AP_THM_TAC THEN
AP_THM_TAC THEN
REWRITE_TAC [operationsTheory.MEASURE_CHANNEL_ID_EQ_MEASURE_CHANNEL_ID_LEMMA]
QED

val (set_bds_to_fetch_channels_index, set_bds_to_fetch_channels_index_ind) = Defn.tprove (
(*Defn.tgoal*) set_bds_to_fetch_channels_index_tgoal,
(fn (A, t) =>
  let val goal_type = (type_of o #1 o dest_exists) t in
  let val measure_type = type_of “MEASURE_CHANNEL_ID_SET_BDS_TO_FETCH_CHANNELS_INDEX” in
  let val type_matching = match_type measure_type goal_type in
  let val type_r_measure_channel_id = inst type_matching “MEASURE_CHANNEL_ID_SET_BDS_TO_FETCH_CHANNELS_INDEX”  in
    EXISTS_TAC type_r_measure_channel_id (A, t)
  end end end end) THEN
CONJ_TAC THENL
[
 REWRITE_TAC [MEASURE_CHANNEL_ID_SET_BDS_TO_FETCH_CHANNELS_INDEX_EQ_LEMMA] THEN
 REWRITE_TAC [WF_MEASURE_CHANNEL_ID_SET_BDS_TO_FETCH_CHANNELS_INDEX_LEMMA]
 ,
 CONJS_TAC THEN
  INTRO_TAC THEN
  REWRITE_TAC [MEASURE_CHANNEL_ID_SET_BDS_TO_FETCH_CHANNELS_INDEX] THEN
  (fn (A, t) => let val asm_to_disch = valOf (List.find (fn asm => if is_neg asm then (is_eq o dest_neg) asm else false) A) in UNDISCH_TAC asm_to_disch (A, t) end) THEN
  REWRITE_TAC [operationsTheory.INDEX_NEQ_ZERO_IMPLIES_MEASURE_CHANNEL_ID_LEMMA]
]
)

val set_bds_to_fetch_channels_index = save_thm ("set_bds_to_fetch_channels_index", set_bds_to_fetch_channels_index)
val set_bds_to_fetch_channels_index_ind = save_thm ("set_bds_to_fetch_channels_index_ind", set_bds_to_fetch_channels_index_ind)

Definition set_bds_to_fetch:
set_bds_to_fetch device_characteristics memory internal_state channels =
  set_bds_to_fetch_channels_index device_characteristics memory internal_state channels (-1w)
End

Definition device_set_abstract_bds_eq_concrete_bds:
device_set_abstract_bds_eq_concrete_bds device_characteristics memory device =
  device with dma_state :=
    device.dma_state with channels :=
      set_bds_to_fetch device_characteristics memory device.dma_state.internal_state device.dma_state.channels
End




Definition IS_SOME_CHANNELS:
IS_SOME_CHANNELS channels1 channels2 max_index =
  !index.
    index <=+ max_index
    ==>
    IS_SOME (channels1 index) = IS_SOME (channels2 index)
End

Definition CHANNEL_BDS_TO_FETCH_UPDATE:
CHANNEL_BDS_TO_FETCH_UPDATE channel1 channel2 bds_to_fetch = (
  channel2 = channel1 with queue := channel1.queue with bds_to_fetch := bds_to_fetch
)
End

Definition CHANNEL_BDS_TO_FETCH_OPTION_UPDATE:
(CHANNEL_BDS_TO_FETCH_OPTION_UPDATE NONE            NONE            bds_to_fetch = T) /\
(CHANNEL_BDS_TO_FETCH_OPTION_UPDATE NONE            (SOME channel2) bds_to_fetch = F) /\  
(CHANNEL_BDS_TO_FETCH_OPTION_UPDATE (SOME channel1) NONE            bds_to_fetch = F) /\
(CHANNEL_BDS_TO_FETCH_OPTION_UPDATE (SOME channel1) (SOME channel2) bds_to_fetch =
 CHANNEL_BDS_TO_FETCH_UPDATE channel1 channel2 bds_to_fetch)
End

Definition CHANNELS_BDS_TO_FETCH:
CHANNELS_BDS_TO_FETCH device_characteristics memory internal_state channels1 channels2 max_index =
!channel_id channel1 channel2 bds_to_fetch.
  channel_id <=+ max_index /\
  channel1 = channels1 channel_id /\
  channel2 = channels2 channel_id /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state
  ==>
  CHANNEL_BDS_TO_FETCH_OPTION_UPDATE channel1 channel2 bds_to_fetch
End

Definition SET_BDS_TO_FETCH_CHANNELS:
SET_BDS_TO_FETCH_CHANNELS device_characteristics memory internal_state channels1 channels2 max_index = (
  CHANNELS_BDS_TO_FETCH device_characteristics memory internal_state channels1 channels2 max_index /\
  IS_SOME_CHANNELS channels1 channels2 max_index /\
  PRESERVED_CHANNELS channels1 channels2 max_index
)
End

Definition SET_BDS_TO_FETCH:
SET_BDS_TO_FETCH
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
memory
internal_state
(channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
(channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
max_index = (
  channels2 = set_bds_to_fetch_channels_index device_characteristics memory internal_state channels1 max_index
  ==>
  SET_BDS_TO_FETCH_CHANNELS device_characteristics memory internal_state channels1 channels2 max_index
)
End

Definition CHANNELS_SET_BDS_TO_FETCH:
CHANNELS_SET_BDS_TO_FETCH device_characteristics memory internal_state channels1 channels2 =
!channel_id channel1 channel2 bds_to_fetch.
  channel1 = channels1 channel_id /\
  channel2 = channels2 channel_id /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state
  ==>
  CHANNEL_BDS_TO_FETCH_OPTION_UPDATE channel1 channel2 bds_to_fetch
End

Definition CHANNELS_IS_SOME:
CHANNELS_IS_SOME channels1 channels2 =
  !i. IS_SOME (channels2 i) = IS_SOME (channels1 i)
End

Definition CHANNELS_SET_BDS_TO_FETCH_IS_SOME:
CHANNELS_SET_BDS_TO_FETCH_IS_SOME device_characteristics memory internal_state channels1 channels2 = (
  CHANNELS_SET_BDS_TO_FETCH device_characteristics memory internal_state channels1 channels2 /\
  CHANNELS_IS_SOME channels1 channels2
)
End

Theorem SET_BDS_TO_FETCH_CHANNELS_IMPLIES_CHANNELS_BDS_TO_FETCH_BASE_LEMMA:
!device_characteristics memory internal_state channels1 channels2.
  channels2 = set_bds_to_fetch_channels device_characteristics memory internal_state channels1 0w
  ==>
  CHANNELS_BDS_TO_FETCH device_characteristics memory internal_state channels1 channels2 0w
Proof
INTRO_TAC THEN
PTAC CHANNELS_BDS_TO_FETCH THEN
INTRO_TAC THEN
PTAC set_bds_to_fetch_channels THEN
ETAC wordsTheory.WORD_LS_word_0 THEN
ALL_LRTAC THEN
PTAC set_bds_to_fetch_channel THEN
 LRTAC THEN
 REWRITE_TAC [combinTheory.UPDATE_def] THEN
 APP_SCALAR_TAC THEN
 REWRITE_TAC [CHANNEL_BDS_TO_FETCH_OPTION_UPDATE, CHANNEL_BDS_TO_FETCH_UPDATE]
QED

Theorem SET_BDS_TO_FETCH_CHANNELS_IMPLIES_IS_SOME_CHANNELS_BASE_LEMMA:
!device_characteristics memory internal_state channels1 channels2.
  channels2 = set_bds_to_fetch_channels device_characteristics memory internal_state channels1 0w
  ==>
  IS_SOME_CHANNELS channels1 channels2 0w
Proof
INTRO_TAC THEN
PTAC IS_SOME_CHANNELS THEN
INTRO_TAC THEN
PTAC set_bds_to_fetch_channels THEN
ETAC wordsTheory.WORD_LS_word_0 THEN
ALL_LRTAC THEN
PTAC set_bds_to_fetch_channel THEN
 LRTAC THEN
 REWRITE_TAC [combinTheory.UPDATE_def] THEN
 APP_SCALAR_TAC THEN
 REWRITE_TAC [optionTheory.IS_SOME_DEF]
QED

Theorem SET_BDS_TO_FETCH_CHANNELS_IMPLIES_PRESERVED_CHANNELS_BASE_LEMMA:
!device_characteristics memory internal_state channels1 channels2.
  channels2 = set_bds_to_fetch_channels device_characteristics memory internal_state channels1 0w
  ==>
  PRESERVED_CHANNELS channels1 channels2 0w
Proof
INTRO_TAC THEN
PTAC PRESERVED_CHANNELS THEN
INTRO_TAC THEN
PTAC set_bds_to_fetch_channels THEN
ETAC wordsTheory.WORD_HIGHER THEN
IRTAC wordsTheory.WORD_LOWER_NOT_EQ THEN
ALL_LRTAC THEN
PTAC set_bds_to_fetch_channel THEN
 REWRITE_TAC [combinTheory.UPDATE_def] THEN
 APP_SCALAR_TAC THEN
 ASM_REWRITE_TAC []
QED

Theorem SET_BDS_TO_FETCH_CHANNELS_BASE_LEMMA:
!device_characteristics memory internal_state channels1 channels2.
  channels2 = set_bds_to_fetch_channels device_characteristics memory internal_state channels1 0w
  ==>
  SET_BDS_TO_FETCH_CHANNELS device_characteristics memory internal_state channels1 channels2 0w
Proof
INTRO_TAC THEN
PTAC SET_BDS_TO_FETCH_CHANNELS THEN
CONJS_TAC THENL
[
 IRTAC SET_BDS_TO_FETCH_CHANNELS_IMPLIES_CHANNELS_BDS_TO_FETCH_BASE_LEMMA THEN STAC
 ,
 IRTAC SET_BDS_TO_FETCH_CHANNELS_IMPLIES_IS_SOME_CHANNELS_BASE_LEMMA THEN STAC
 ,
 IRTAC SET_BDS_TO_FETCH_CHANNELS_IMPLIES_PRESERVED_CHANNELS_BASE_LEMMA THEN STAC
]
QED



Theorem SET_BDS_TO_FETCH_CHANNELS_IMPLIES_CHANNELS_BDS_TO_FETCH_INDUCTION_LEMMA:
!device_characteristics memory internal_state channels1 channels channels2 i.
  i <> 0w /\
  channels = set_bds_to_fetch_channels device_characteristics memory internal_state channels1 i /\
  SET_BDS_TO_FETCH_CHANNELS device_characteristics memory internal_state channels channels2 (i − 1w)
  ==>
  CHANNELS_BDS_TO_FETCH device_characteristics memory internal_state channels1 channels2 i
Proof
INTRO_TAC THEN
PTAC set_bds_to_fetch_channels THEN
RLTAC THEN
ETAC SET_BDS_TO_FETCH_CHANNELS THEN
ETAC CHANNELS_BDS_TO_FETCH THEN
INTRO_TAC THEN
ETAC wordsTheory.WORD_LOWER_OR_EQ THEN
SPLIT_ASM_DISJS_TAC THENL
[
 ITAC wordsTheory.WORD_LOWER_NOT_EQ THEN
 IRTAC word_lemmasTheory.LE_IMPLIES_LEQ_PRED_LEMMA THEN
 AIRTAC THEN
 LRTAC THEN
 LRTAC THEN
 ETAC combinTheory.UPDATE_def THEN
 APP_SCALAR_TAC THEN
 IF_SPLIT_TAC THEN (TRY STAC) THEN
 REFL_ASM_EQ_TAC THEN
 CONTR_ASMS_TAC
 ,
 RLTAC THEN
 WEAKEN_TAC is_forall THEN
 RLTAC THEN
 LRTAC THEN
 PTAC set_bds_to_fetch_channel THEN
  ALL_LRTAC THEN
  PTAC PRESERVED_CHANNELS THEN
  IRTAC word_lemmasTheory.NEQ_ZERO_IMPLIES_GT_PRED_LEMMA THEN
  AIRTAC THEN
  LRTAC THEN
  ETAC combinTheory.UPDATE_def THEN
  APP_SCALAR_TAC THEN
  REWRITE_TAC [CHANNEL_BDS_TO_FETCH_OPTION_UPDATE, CHANNEL_BDS_TO_FETCH_UPDATE]
]
QED

Theorem SET_BDS_TO_FETCH_CHANNELS_IMPLIES_IS_SOME_CHANNELS_INDUCTION_LEMMA:
!device_characteristics memory internal_state channels1 channels channels2 i.
  i <> 0w /\
  channels = set_bds_to_fetch_channels device_characteristics memory internal_state channels1 i /\
  SET_BDS_TO_FETCH_CHANNELS device_characteristics memory internal_state channels channels2 (i − 1w)
  ==>
  IS_SOME_CHANNELS channels1 channels2 i
Proof
INTRO_TAC THEN
PTAC set_bds_to_fetch_channels THEN
RLTAC THEN
ETAC SET_BDS_TO_FETCH_CHANNELS THEN
ETAC IS_SOME_CHANNELS THEN
INTRO_TAC THEN
ETAC wordsTheory.WORD_LOWER_OR_EQ THEN
SPLIT_ASM_DISJS_TAC THENL
[
 ITAC wordsTheory.WORD_LOWER_NOT_EQ THEN
 IRTAC word_lemmasTheory.LE_IMPLIES_LEQ_PRED_LEMMA THEN
 AIRTAC THEN
 LRTAC THEN
 RLTAC THEN
 REWRITE_TAC [combinTheory.UPDATE_def] THEN
 APP_SCALAR_TAC THEN
 REPEAT (WEAKEN_TAC (not o is_neg)) THEN
 IF_SPLIT_TAC THEN (TRY STAC) THEN
 LRTAC THEN
 CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
 ,
 RLTAC THEN
 WEAKEN_TAC is_forall THEN
 PTAC set_bds_to_fetch_channel THEN
  ALL_LRTAC THEN
  PTAC PRESERVED_CHANNELS THEN
  IRTAC word_lemmasTheory.NEQ_ZERO_IMPLIES_GT_PRED_LEMMA THEN
  AIRTAC THEN
  LRTAC THEN
  ETAC combinTheory.UPDATE_def THEN
  APP_SCALAR_TAC THEN
  REWRITE_TAC [optionTheory.IS_SOME_DEF]
]
QED

Theorem SET_BDS_TO_FETCH_CHANNELS_IMPLIES_PRESERVED_CHANNELS_INDUCTION_LEMMA:
!device_characteristics memory internal_state channels1 channels channels2 i.
  i <> 0w /\
  channels = set_bds_to_fetch_channels device_characteristics memory internal_state channels1 i /\
  SET_BDS_TO_FETCH_CHANNELS device_characteristics memory internal_state channels channels2 (i − 1w)
  ==>
  PRESERVED_CHANNELS channels1 channels2 i
Proof
INTRO_TAC THEN
PTAC set_bds_to_fetch_channels THEN
RLTAC THEN
ETAC SET_BDS_TO_FETCH_CHANNELS THEN
ETAC PRESERVED_CHANNELS THEN
INTRO_TAC THEN
ALL_LRTAC THEN
ETAC wordsTheory.WORD_HIGHER THEN
ITAC wordsTheory.WORD_LOWER_NOT_EQ THEN
ETAC wordsTheory.WORD_HIGHER THEN
ITAC word_lemmasTheory.NEQ_ZERO_GT_IMPLIES_GT_PRED_LEMMA THEN
AIRTAC THEN
LRTAC THEN
REWRITE_TAC [combinTheory.UPDATE_def] THEN
APP_SCALAR_TAC THEN
STAC
QED

Theorem SET_BDS_TO_FETCH_CHANNELS_INDUCTION_LEMMA:
!device_characteristics memory internal_state channels1 channels channels2 i.
  i <> 0w /\
  channels = set_bds_to_fetch_channels device_characteristics memory internal_state channels1 i /\
  SET_BDS_TO_FETCH_CHANNELS device_characteristics memory internal_state channels channels2 (i − 1w)
  ==>
  SET_BDS_TO_FETCH_CHANNELS device_characteristics memory internal_state channels1 channels2 i
Proof
INTRO_TAC THEN
REWRITE_TAC [SET_BDS_TO_FETCH_CHANNELS] THEN
CONJS_TAC THENL
[
 IRTAC SET_BDS_TO_FETCH_CHANNELS_IMPLIES_CHANNELS_BDS_TO_FETCH_INDUCTION_LEMMA THEN STAC
 ,
 IRTAC SET_BDS_TO_FETCH_CHANNELS_IMPLIES_IS_SOME_CHANNELS_INDUCTION_LEMMA THEN STAC
 ,
 IRTAC SET_BDS_TO_FETCH_CHANNELS_IMPLIES_PRESERVED_CHANNELS_INDUCTION_LEMMA THEN STAC
]
QED

Theorem SET_BDS_TO_FETCH_CHANNELS_INDEX_IND_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 internal_state
 (channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 max_index.
 (\device_characteristics memory internal_state channels1 max_index.
 !(channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option).
   channels2 = set_bds_to_fetch_channels_index device_characteristics memory internal_state channels1 max_index
   ==>
   SET_BDS_TO_FETCH_CHANNELS device_characteristics memory internal_state channels1 channels2 max_index)
 device_characteristics memory internal_state channels1 max_index
Proof
MATCH_MP_TAC set_bds_to_fetch_channels_index_ind THEN
INTRO_TAC THEN
APP_SCALAR_TAC THEN
INTRO_TAC THEN
PTAC set_bds_to_fetch_channels_index THENL
[
 IRTAC SET_BDS_TO_FETCH_CHANNELS_BASE_LEMMA THEN STAC
 ,
 AITAC THEN
 AIRTAC THEN
 IRTAC SET_BDS_TO_FETCH_CHANNELS_INDUCTION_LEMMA THEN
 STAC
]
QED

Theorem SET_BDS_TO_FETCH_CHANNELS_INDEX_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 internal_state
 (channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 max_index.
 channels2 = set_bds_to_fetch_channels_index device_characteristics memory internal_state channels1 max_index
 ==>
 SET_BDS_TO_FETCH_CHANNELS device_characteristics memory internal_state channels1 channels2 max_index
Proof
REWRITE_TAC [BETA_RULE SET_BDS_TO_FETCH_CHANNELS_INDEX_IND_LEMMA]
QED

Theorem SET_BDS_TO_FETCH_ALL_CHANNELS_INDEX_IMPLIES_CHANNELS_SET_BDS_TO_FETCH_IS_SOME_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 internal_state
 (channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option).
  channels2 = set_bds_to_fetch_channels_index device_characteristics memory internal_state channels1 (-1w)
  ==>
  CHANNELS_SET_BDS_TO_FETCH_IS_SOME device_characteristics memory internal_state channels1 channels2
Proof
INTRO_TAC THEN
IRTAC SET_BDS_TO_FETCH_CHANNELS_INDEX_LEMMA THEN
PTAC SET_BDS_TO_FETCH_CHANNELS THEN
PTAC CHANNELS_SET_BDS_TO_FETCH_IS_SOME THEN
CONJ_TAC THENL
[
 PTAC CHANNELS_SET_BDS_TO_FETCH THEN
 INTRO_TAC THEN
 PTAC CHANNELS_BDS_TO_FETCH THEN
 INST_IMP_ASM_GOAL_TAC THEN
 ASM_REWRITE_TAC [wordsTheory.WORD_LS_word_T]
 ,
 PTAC IS_SOME_CHANNELS THEN
 PTAC CHANNELS_IS_SOME THEN
 GEN_TAC THEN
 ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
 INST_IMP_ASM_GOAL_TAC THEN
 REWRITE_TAC [wordsTheory.WORD_LS_word_T]
]
QED

Theorem SET_BDS_TO_FETCH_IMPLIES_CHANNELS_SET_BDS_TO_FETCH_IS_SOME_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 internal_state
 (channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option).
  channels2 = set_bds_to_fetch device_characteristics memory internal_state channels1
  ==>
  CHANNELS_SET_BDS_TO_FETCH_IS_SOME device_characteristics memory internal_state channels1 channels2
Proof
INTRO_TAC THEN
PTAC set_bds_to_fetch THEN
IRTAC SET_BDS_TO_FETCH_ALL_CHANNELS_INDEX_IMPLIES_CHANNELS_SET_BDS_TO_FETCH_IS_SOME_LEMMA THEN
STAC
QED

Theorem CHANNELS_SET_BDS_TO_FETCH_IS_SOME_IMPLIES_IS_SOME_EQ_LEMMA:
!device_characteristics channel_id memory internal_state channels1 channels2.
  CHANNELS_SET_BDS_TO_FETCH_IS_SOME device_characteristics memory internal_state channels1 channels2
  ==>
  IS_SOME (channels2 channel_id) = IS_SOME (channels1 channel_id)
Proof
INTRO_TAC THEN
PTAC CHANNELS_SET_BDS_TO_FETCH_IS_SOME THEN
PTAC CHANNELS_IS_SOME THEN
STAC
QED

Theorem SET_BDS_TO_FETCH_IMPLIES_IS_SOME_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 internal_state
 (channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 channel_id.
  channels2 = set_bds_to_fetch device_characteristics memory internal_state channels1
  ==>
  IS_SOME (channels2 channel_id) = IS_SOME (channels1 channel_id)
Proof
INTRO_TAC THEN
IRTAC SET_BDS_TO_FETCH_IMPLIES_CHANNELS_SET_BDS_TO_FETCH_IS_SOME_LEMMA THEN
IRTAC CHANNELS_SET_BDS_TO_FETCH_IS_SOME_IMPLIES_IS_SOME_EQ_LEMMA THEN
STAC
QED

Theorem SET_BDS_TO_FETCH_IMPLIES_CHANNEL_BDS_TO_FETCH_OPTION_UPDATE_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 internal_state
 (channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 channel_id channel1 channel2 bds_to_fetch.
  channels2 = set_bds_to_fetch device_characteristics memory internal_state channels1 /\
  channel1 = channels1 channel_id /\
  channel2 = channels2 channel_id /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state
  ==>
  CHANNEL_BDS_TO_FETCH_OPTION_UPDATE channel1 channel2 bds_to_fetch
Proof
INTRO_TAC THEN
IRTAC SET_BDS_TO_FETCH_IMPLIES_CHANNELS_SET_BDS_TO_FETCH_IS_SOME_LEMMA THEN
PTAC CHANNELS_SET_BDS_TO_FETCH_IS_SOME THEN
PTAC CHANNELS_SET_BDS_TO_FETCH THEN
AIRTAC THEN
STAC
QED




Theorem SET_BDS_TO_FETCH_IMPLIES_ABSTRACT_EQ_CONCRETE_BDS_TO_FETCH_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 internal_state
 (channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 channel_id channel1 channel2.
  channels2 = set_bds_to_fetch device_characteristics memory internal_state channels1 /\
  IS_SOME (channels2 channel_id) /\
  channel1 = THE (channels1 channel_id) /\
  channel2 = THE (channels2 channel_id)
  ==>
  channel2.queue.bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state
Proof
INTRO_TAC THEN
IRTAC SET_BDS_TO_FETCH_IMPLIES_CHANNEL_BDS_TO_FETCH_OPTION_UPDATE_LEMMA THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC “channel_id : 'channel_index_width channel_id_type ” thm)) THEN
Cases_on ‘channels1 channel_id’ THEN Cases_on ‘channels2 channel_id’ THEN ETAC CHANNEL_BDS_TO_FETCH_OPTION_UPDATE THENL
[
 ETAC optionTheory.IS_SOME_DEF THEN SOLVE_F_ASM_TAC
 ,
 SOLVE_F_ASM_TAC
 ,
 SOLVE_F_ASM_TAC
 ,
 ETAC optionTheory.THE_DEF THEN
 RLTAC THEN
 RLTAC THEN
 RLTAC THEN
 PTAC CHANNEL_BDS_TO_FETCH_UPDATE THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
]
QED

Theorem SET_BDS_TO_FETCH_IMPLIES_BDS_TO_UPDATE_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 internal_state
 (channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
channel_id channel1 channel2.
  channels2 = set_bds_to_fetch device_characteristics memory internal_state channels1 /\
  IS_SOME (channels2 channel_id) /\
  channel1 = THE (channels1 channel_id) /\
  channel2 = THE (channels2 channel_id)
  ==>
  channel2.queue.bds_to_update = channel1.queue.bds_to_update
Proof
INTRO_TAC THEN
IRTAC SET_BDS_TO_FETCH_IMPLIES_CHANNEL_BDS_TO_FETCH_OPTION_UPDATE_LEMMA THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC “channel_id : 'channel_index_width channel_id_type ” thm)) THEN
Cases_on ‘channels1 channel_id’ THEN Cases_on ‘channels2 channel_id’ THEN ETAC CHANNEL_BDS_TO_FETCH_OPTION_UPDATE THENL
[
 ETAC optionTheory.IS_SOME_DEF THEN SOLVE_F_ASM_TAC
 ,
 SOLVE_F_ASM_TAC
 ,
 SOLVE_F_ASM_TAC
 ,
 ETAC optionTheory.THE_DEF THEN
 RLTAC THEN
 RLTAC THEN
 RLTAC THEN
 PTAC CHANNEL_BDS_TO_FETCH_UPDATE THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
]
QED

Theorem SET_BDS_TO_FETCH_IMPLIES_BDS_TO_PROCESS_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 internal_state
 (channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
channel_id channel1 channel2.
  channels2 = set_bds_to_fetch device_characteristics memory internal_state channels1 /\
  IS_SOME (channels2 channel_id) /\
  channel1 = THE (channels1 channel_id) /\
  channel2 = THE (channels2 channel_id)
  ==>
  channel2.queue.bds_to_process = channel1.queue.bds_to_process
Proof
INTRO_TAC THEN
IRTAC SET_BDS_TO_FETCH_IMPLIES_CHANNEL_BDS_TO_FETCH_OPTION_UPDATE_LEMMA THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC “channel_id : 'channel_index_width channel_id_type ” thm)) THEN
Cases_on ‘channels1 channel_id’ THEN Cases_on ‘channels2 channel_id’ THEN ETAC CHANNEL_BDS_TO_FETCH_OPTION_UPDATE THENL
[
 ETAC optionTheory.IS_SOME_DEF THEN SOLVE_F_ASM_TAC
 ,
 SOLVE_F_ASM_TAC
 ,
 SOLVE_F_ASM_TAC
 ,
 ETAC optionTheory.THE_DEF THEN
 RLTAC THEN
 RLTAC THEN
 RLTAC THEN
 PTAC CHANNEL_BDS_TO_FETCH_UPDATE THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
]
QED

Theorem SET_BDS_TO_FETCH_IMPLIES_BDS_TO_WRITE_BACK_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 internal_state
 (channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
channel_id channel1 channel2.
  channels2 = set_bds_to_fetch device_characteristics memory internal_state channels1 /\
  IS_SOME (channels2 channel_id) /\
  channel1 = THE (channels1 channel_id) /\
  channel2 = THE (channels2 channel_id)
  ==>
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
IRTAC SET_BDS_TO_FETCH_IMPLIES_CHANNEL_BDS_TO_FETCH_OPTION_UPDATE_LEMMA THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC “channel_id : 'channel_index_width channel_id_type ” thm)) THEN
Cases_on ‘channels1 channel_id’ THEN Cases_on ‘channels2 channel_id’ THEN ETAC CHANNEL_BDS_TO_FETCH_OPTION_UPDATE THENL
[
 ETAC optionTheory.IS_SOME_DEF THEN SOLVE_F_ASM_TAC
 ,
 SOLVE_F_ASM_TAC
 ,
 SOLVE_F_ASM_TAC
 ,
 ETAC optionTheory.THE_DEF THEN
 RLTAC THEN
 RLTAC THEN
 RLTAC THEN
 PTAC CHANNEL_BDS_TO_FETCH_UPDATE THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
]
QED

Theorem SET_BDS_TO_FETCH_IMPLIES_PENDING_ACCESSES_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 internal_state
 (channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
channel_id channel1 channel2.
  channels2 = set_bds_to_fetch device_characteristics memory internal_state channels1 /\
  IS_SOME (channels2 channel_id) /\
  channel1 = THE (channels1 channel_id) /\
  channel2 = THE (channels2 channel_id)
  ==>
  channel2.pending_accesses = channel1.pending_accesses
Proof
INTRO_TAC THEN
IRTAC SET_BDS_TO_FETCH_IMPLIES_CHANNEL_BDS_TO_FETCH_OPTION_UPDATE_LEMMA THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC “channel_id : 'channel_index_width channel_id_type ” thm)) THEN
Cases_on ‘channels1 channel_id’ THEN Cases_on ‘channels2 channel_id’ THEN ETAC CHANNEL_BDS_TO_FETCH_OPTION_UPDATE THENL
[
 ETAC optionTheory.IS_SOME_DEF THEN SOLVE_F_ASM_TAC
 ,
 SOLVE_F_ASM_TAC
 ,
 SOLVE_F_ASM_TAC
 ,
 ETAC optionTheory.THE_DEF THEN
 RLTAC THEN
 RLTAC THEN
 RLTAC THEN
 PTAC CHANNEL_BDS_TO_FETCH_UPDATE THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
]
QED

Theorem DEVICE_SET_ABSTRACT_BDS_EQ_CONCRETE_BDS_IMPLIES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device3 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  DEFINED_CHANNELS device_characteristics device3 /\
  device2 = device_set_abstract_bds_eq_concrete_bds device_characteristics memory device3
  ==>
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device2 device3
Proof
INTRO_TAC THEN
PTAC ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
PTAC DEFINED_CHANNELS THEN
PTAC VALID_CHANNELS THEN
AIRTAC THEN
PTAC device_set_abstract_bds_eq_concrete_bds THEN
LRTAC THEN
REWRITE_TAC [stateTheory.schannel] THEN
RECORD_TAC THEN
ITAC SET_BDS_TO_FETCH_IMPLIES_ABSTRACT_EQ_CONCRETE_BDS_TO_FETCH_LEMMA THEN
IRTAC SET_BDS_TO_FETCH_IMPLIES_IS_SOME_EQ_LEMMA THEN
RLTAC THEN
AIRTAC THEN
STAC
QED

Theorem DEVICE_SET_ABSTRACT_BDS_EQ_CONCRETE_BDS_IMPLIES_BDS_TO_UPDATE_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device3 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  DEFINED_CHANNELS device_characteristics device3 /\
  device2 = device_set_abstract_bds_eq_concrete_bds device_characteristics memory device3
  ==>
  BDS_TO_UPDATE_EQ device_characteristics device2 device3
Proof
INTRO_TAC THEN
PTAC BDS_TO_UPDATE_EQ THEN
INTRO_TAC THEN
PTAC DEFINED_CHANNELS THEN
PTAC VALID_CHANNELS THEN
AIRTAC THEN
PTAC device_set_abstract_bds_eq_concrete_bds THEN
LRTAC THEN
REWRITE_TAC [stateTheory.schannel] THEN
RECORD_TAC THEN
ITAC SET_BDS_TO_FETCH_IMPLIES_BDS_TO_UPDATE_EQ_LEMMA THEN
IRTAC SET_BDS_TO_FETCH_IMPLIES_IS_SOME_EQ_LEMMA THEN
QRLTAC THEN
AIRTAC THEN
STAC
QED

Theorem DEVICE_SET_ABSTRACT_BDS_EQ_CONCRETE_BDS_IMPLIES_BDS_TO_PROCESS_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device3 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  DEFINED_CHANNELS device_characteristics device3 /\
  device2 = device_set_abstract_bds_eq_concrete_bds device_characteristics memory device3
  ==>
  BDS_TO_PROCESS_EQ device_characteristics device2 device3
Proof
INTRO_TAC THEN
PTAC BDS_TO_PROCESS_EQ THEN
INTRO_TAC THEN
PTAC DEFINED_CHANNELS THEN
PTAC VALID_CHANNELS THEN
AIRTAC THEN
PTAC device_set_abstract_bds_eq_concrete_bds THEN
LRTAC THEN
REWRITE_TAC [stateTheory.schannel] THEN
RECORD_TAC THEN
ITAC SET_BDS_TO_FETCH_IMPLIES_BDS_TO_PROCESS_EQ_LEMMA THEN
IRTAC SET_BDS_TO_FETCH_IMPLIES_IS_SOME_EQ_LEMMA THEN
RLTAC THEN
AIRTAC THEN
STAC
QED

Theorem DEVICE_SET_ABSTRACT_BDS_EQ_CONCRETE_BDS_IMPLIES_BDS_TO_WRITE_BACK_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device3 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  DEFINED_CHANNELS device_characteristics device3 /\
  device2 = device_set_abstract_bds_eq_concrete_bds device_characteristics memory device3
  ==>
  BDS_TO_WRITE_BACK_EQ device_characteristics device2 device3
Proof
INTRO_TAC THEN
PTAC BDS_TO_WRITE_BACK_EQ THEN
INTRO_TAC THEN
PTAC DEFINED_CHANNELS THEN
PTAC VALID_CHANNELS THEN
AIRTAC THEN
PTAC device_set_abstract_bds_eq_concrete_bds THEN
LRTAC THEN
REWRITE_TAC [stateTheory.schannel] THEN
RECORD_TAC THEN
ITAC SET_BDS_TO_FETCH_IMPLIES_BDS_TO_WRITE_BACK_EQ_LEMMA THEN
IRTAC SET_BDS_TO_FETCH_IMPLIES_IS_SOME_EQ_LEMMA THEN
RLTAC THEN
AIRTAC THEN
STAC
QED

Theorem DEVICE_SET_ABSTRACT_BDS_EQ_CONCRETE_BDS_IMPLIES_MEMORY_REQUESTS_REPLIES_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device3 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  DEFINED_CHANNELS device_characteristics device3 /\
  device2 = device_set_abstract_bds_eq_concrete_bds device_characteristics memory device3
  ==>
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device2 device3
Proof
INTRO_TAC THEN
PTAC MEMORY_REQUESTS_REPLIES_EQ THEN
PTAC device_set_abstract_bds_eq_concrete_bds THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [] THEN
INTRO_TAC THEN
PTAC DEFINED_CHANNELS THEN
PTAC VALID_CHANNELS THEN
AIRTAC THEN
REWRITE_TAC [stateTheory.schannel] THEN
RECORD_TAC THEN
ITAC SET_BDS_TO_FETCH_IMPLIES_PENDING_ACCESSES_EQ_LEMMA THEN
IRTAC SET_BDS_TO_FETCH_IMPLIES_IS_SOME_EQ_LEMMA THEN
RLTAC THEN
AIRTAC THEN
STAC
QED

Theorem DEVICE_SET_ABSTRACT_BDS_EQ_CONCRETE_BDS_IMPLIES_FUNCTION_STATES_EQ_LEMMA:
!device_characteristics memory device2 device3.
  device2 = device_set_abstract_bds_eq_concrete_bds device_characteristics memory device3
  ==>
  FUNCTION_STATES_EQ device2 device3
Proof
INTRO_TAC THEN
PTAC device_set_abstract_bds_eq_concrete_bds THEN
LRTAC THEN
PTAC FUNCTION_STATES_EQ THEN
RECORD_TAC THEN
STAC
QED

Theorem DEVICE_SET_ABSTRACT_BDS_EQ_CONCRETE_BDS_IMPLIES_INTERNAL_STATES_EQ_LEMMA:
!device_characteristics memory device2 device3.
  device2 = device_set_abstract_bds_eq_concrete_bds device_characteristics memory device3
  ==>
  INTERNAL_STATES_EQ device2 device3
Proof
INTRO_TAC THEN
PTAC device_set_abstract_bds_eq_concrete_bds THEN
LRTAC THEN
PTAC INTERNAL_STATES_EQ THEN
RECORD_TAC THEN
STAC
QED

Theorem DEVICE_SET_ABSTRACT_BDS_EQ_CONCRETE_BDS_IMPLIES_DEFINED_CHANNELS_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 memory
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device3 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  device2 = device_set_abstract_bds_eq_concrete_bds device_characteristics memory device3
  ==>
  DEFINED_CHANNELS_EQ device_characteristics device2 device3
Proof
INTRO_TAC THEN
PTAC device_set_abstract_bds_eq_concrete_bds THEN
LRTAC THEN
PTAC DEFINED_CHANNELS_EQ THEN
GEN_TAC THEN
RECORD_TAC THEN
ITAC SET_BDS_TO_FETCH_IMPLIES_IS_SOME_EQ_LEMMA THEN
STAC
QED

Theorem DEVICE_SET_ABSTRACT_BDS_EQ_CONRETE_BDS_IMPLIES_L23EQ_LEMMA:
!device_characteristics memory device2 device3.
  DEFINED_CHANNELS device_characteristics device3 /\
  device2 = device_set_abstract_bds_eq_concrete_bds device_characteristics memory device3
  ==>
  L23EQ device_characteristics memory device2 device3
Proof
INTRO_TAC THEN
ETAC L23EQ THEN
ITAC DEVICE_SET_ABSTRACT_BDS_EQ_CONCRETE_BDS_IMPLIES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA THEN
ITAC DEVICE_SET_ABSTRACT_BDS_EQ_CONCRETE_BDS_IMPLIES_BDS_TO_UPDATE_EQ_LEMMA THEN
ITAC DEVICE_SET_ABSTRACT_BDS_EQ_CONCRETE_BDS_IMPLIES_BDS_TO_PROCESS_EQ_LEMMA THEN
ITAC DEVICE_SET_ABSTRACT_BDS_EQ_CONCRETE_BDS_IMPLIES_BDS_TO_WRITE_BACK_EQ_LEMMA THEN
ITAC DEVICE_SET_ABSTRACT_BDS_EQ_CONCRETE_BDS_IMPLIES_MEMORY_REQUESTS_REPLIES_EQ_LEMMA THEN
ITAC DEVICE_SET_ABSTRACT_BDS_EQ_CONCRETE_BDS_IMPLIES_FUNCTION_STATES_EQ_LEMMA THEN
ITAC DEVICE_SET_ABSTRACT_BDS_EQ_CONCRETE_BDS_IMPLIES_INTERNAL_STATES_EQ_LEMMA THEN
ITAC DEVICE_SET_ABSTRACT_BDS_EQ_CONCRETE_BDS_IMPLIES_DEFINED_CHANNELS_EQ_LEMMA THEN
STAC
QED

Theorem EXISTS_L23EQ_LEMMA:
!device_characteristics memory1 device1.
  DEFINED_CHANNELS device_characteristics device1
  ==>
  ?device.
    L23EQ device_characteristics memory1 device device1
Proof
INTRO_TAC THEN
IRTAC DEVICE_SET_ABSTRACT_BDS_EQ_CONRETE_BDS_IMPLIES_L23EQ_LEMMA THEN
PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (SPEC “memory1 : 'e memory_type” thm)) THEN
PAXTAC THEN
STAC
QED

val _ = export_theory();
