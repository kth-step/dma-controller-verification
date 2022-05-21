open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory;

val _ = new_theory "state_lemmas";

Theorem UPDATING_INTERNAL_STATE_LEMMA:
!device1 device2 internal_state2.
  device2 = device1 with dma_state := device1.dma_state with internal_state := internal_state2
  ==>
  device2.dma_state.internal_state = internal_state2
Proof
INTRO_TAC THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC []
QED

Theorem UPDATING_INTERNAL_STATE_PRESERVES_CHANNEL_STATES_LEMMA:
!device1 device2 internal_state2.
  device2 = device1 with dma_state := device1.dma_state with internal_state := internal_state2
  ==>
  device2.dma_state.channels = device1.dma_state.channels
Proof
INTRO_TAC THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC []
QED

Theorem UPDATING_INTERNAL_STATE_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA:
!device1 device2 internal_state2.
  device2 = device1 with dma_state := device1.dma_state with internal_state := internal_state2
  ==>
  device2.dma_state.pending_register_related_memory_requests = device1.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC []
QED

Theorem UPDATING_INTERNAL_STATE_PRESERVES_CHANNEL_STATES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA:
!device1 device2 internal_state2.
  device2 = device1 with dma_state := device1.dma_state with internal_state := internal_state2
  ==>
  device2.dma_state.channels = device1.dma_state.channels /\
  device2.dma_state.pending_register_related_memory_requests = device1.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
ITAC UPDATING_INTERNAL_STATE_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA THEN
ITAC UPDATING_INTERNAL_STATE_PRESERVES_CHANNEL_STATES_LEMMA THEN
STAC
QED

Theorem EQUAL_PENDING_ACCESSES_IMPLY_EQUAL_REQUESTS_LEMMA:
!channel1 channel2.
  channel2.pending_accesses = channel1.pending_accesses
  ==>
  channel2.pending_accesses.requests = channel1.pending_accesses.requests
Proof
REPEAT GEN_TAC THEN
DISCH_TAC THEN
STAC
QED

Theorem EQ_PENDING_ACCESSES_IMP_EQ_PENDING_ACCESSES_REQUESTS_ALL_OPERATIONS_LEMMA:
!(channel1 : ('a, 'b, 'c) channel_state_type) (channel2 : ('a, 'b, 'c) channel_state_type).
  channel2.pending_accesses = channel1.pending_accesses
  ==>
  channel1.pending_accesses.requests.fetching_bd = channel2.pending_accesses.requests.fetching_bd /\
  channel1.pending_accesses.requests.updating_bd = channel2.pending_accesses.requests.updating_bd /\
  channel1.pending_accesses.requests.transferring_data = channel2.pending_accesses.requests.transferring_data /\
  channel1.pending_accesses.requests.writing_back_bd = channel2.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
STAC
QED

Theorem FUNCTION_STATE_UPDATE_PRESERVES_ALL_DMA_CHANNEL_PENDING_ACCESSES_LEMMA:
!device1 device2 function_state.
  device2 = device1 with function_state := function_state
  ==>
  !channel_id.
    (schannel device2 channel_id).pending_accesses = (schannel device1 channel_id).pending_accesses
Proof
INTRO_TAC THEN
GEN_TAC THEN
LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
STAC
QED

Theorem UPDATING_INTERNAL_STATE_PRESERVES_DEFINED_CHANNELS_LEMMA:
!device_characteristics device1 device2 internal_state2.
  device2 = device1 with dma_state := device1.dma_state with internal_state := internal_state2 /\
  DEFINED_CHANNELS device_characteristics device1
  ==>
  DEFINED_CHANNELS device_characteristics device2
Proof
INTRO_TAC THEN
ETAC DEFINED_CHANNELS THEN
ITAC UPDATING_INTERNAL_STATE_PRESERVES_CHANNEL_STATES_LEMMA THEN
STAC
QED

Theorem UPDATING_INTERNAL_STATE_EQ_SCHANNEL_LEMMA:
!device1 device2 internal_state2 channel_id.
  device2 = device1 with dma_state := device1.dma_state with internal_state := internal_state2
  ==>
  schannel device2 channel_id = schannel device1 channel_id
Proof
INTRO_TAC THEN
IRTAC UPDATING_INTERNAL_STATE_PRESERVES_CHANNEL_STATES_LEMMA THEN
ETAC schannel THEN
STAC
QED

Theorem DEVICE_CHANNELS_CHANNEL_ID_IMPLIES_SCHANNEL_LEMMA:
!device channels channel channel_id.
  channels = device.dma_state.channels /\
  channel = THE (channels channel_id)
  ==>
  channel = schannel device channel_id
Proof
INTRO_TAC THEN
ASM_REWRITE_TAC [stateTheory.schannel]
QED

Theorem BD_TRANSFER_RAS_WAS_EQ_RAS_WAS_LEMMA:
!device_characteristics channel_id internal_state1 bd.
  ?ras was.
    (ras, was) = (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state1 bd
Proof
REPEAT GEN_TAC THEN
(fn (A, t) =>
 let val r = (rhs o #2 o strip_exists) t in
 let val ty = type_of r in
 let val qv = (#1 o dest_forall o concl) boolTheory.EXISTS_REFL in
 let val qt = type_of qv in
 let val t_subst = [qt |-> ty] in
 let val v_subst = [inst t_subst qv |-> r] in
 let val instantiated_existential_thm = INST_TY_TERM (v_subst, t_subst) (SPEC_ALL boolTheory.EXISTS_REFL) in
   ASSUME_TAC instantiated_existential_thm (A, t)
 end end end end end end end) THEN
AXTAC THEN
(fn (A, t) =>
 let val l = (lhs o #2 o strip_exists o hd) A in
 let val tys = (#2 o dest_type o type_of) l in
 let val qv = (#1 o dest_forall o concl) pairTheory.pair_CASES in
 let val qts = (#2 o dest_type o type_of) qv in
 let val t_subst = map (fn (from, to) => from |-> to) (zip qts tys) in
 let val v_subst = [inst t_subst qv |-> l] in
 let val instantiated_existential_thm = INST_TY_TERM (v_subst, t_subst) (SPEC_ALL pairTheory.pair_CASES) in
   ASSUME_TAC instantiated_existential_thm (A, t)
 end end end end end end end) THEN
AXTAC THEN
LRTAC THEN
PAXTAC THEN
STAC
QED

Theorem ACCESSING_UPDATED_INTERNAL_STATE_LEMMA:
!device1 device2 internal_state2.
  device2 = device1 with dma_state := device1.dma_state with internal_state := internal_state2
  ==>
  device2.dma_state.internal_state = internal_state2
Proof
INTRO_TAC THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem DEFINED_VALID_CHANNEL_IS_SOME_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id.
  DEFINED_CHANNELS device_characteristics device /\
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  IS_SOME (device.dma_state.channels channel_id)
Proof
INTRO_TAC THEN
ETAC stateTheory.DEFINED_CHANNELS THEN
ETAC stateTheory.VALID_CHANNELS THEN
AIRTAC THEN
STAC
QED








Theorem NEQ_ZERO_INDEX_PRESERVES_VALID_CHANNEL_ID_LEMMA:
!device_characteristics i.
  VALID_CHANNEL_ID device_characteristics i /\
  i <> 0w
  ==>
  VALID_CHANNEL_ID device_characteristics (i - 1w)
Proof
INTRO_TAC THEN
ETAC stateTheory.VALID_CHANNEL_ID THEN
IRTAC word_lemmasTheory.NEQ_ZERO_IMPLIES_PRE_LT_LEMMA THEN
IRTAC wordsTheory.WORD_LOWER_LOWER_EQ_TRANS THEN
IRTAC wordsTheory.WORD_LOWER_IMP_LOWER_OR_EQ THEN
STAC
QED

Theorem LT_SOME_MAX_INDEX_IMP_VALID_CHANNEL_ID_LEMMA:
!device_characteristics index max_index.
  max_index = device_characteristics.dma_characteristics.max_index /\
  index <=+ max_index
  ==>
  VALID_CHANNEL_ID device_characteristics index
Proof
INTRO_TAC THEN
ETAC VALID_CHANNEL_ID THEN
STAC
QED

Theorem SOME_MAX_INDEX_IMP_VALID_CHANNEL_ID_LEMMA:
!device_characteristics max_index.
  max_index = device_characteristics.dma_characteristics.max_index
  ==>
  VALID_CHANNEL_ID device_characteristics max_index
Proof
INTRO_TAC THEN
ETAC VALID_CHANNEL_ID THEN
LRTAC THEN
REWRITE_TAC [wordsTheory.WORD_LOWER_EQ_REFL]
QED

Theorem VALID_CHANNEL_ID_IMPLIES_LEQ_MAX_LEMMA:
!device_characteristics max index.
  max = device_characteristics.dma_characteristics.max_index /\
  VALID_CHANNEL_ID device_characteristics index
  ==>
  index <=+ max
Proof
INTRO_TAC THEN
ETAC VALID_CHANNEL_ID THEN
RLTAC THEN
STAC
QED

Theorem NOT_VALID_CHANNEL_ID_IMPLIES_INDEX_GT_MAX_LEMMA:
!device_characteristics max index.
  ~VALID_CHANNEL_ID device_characteristics index /\
  max = device_characteristics.dma_characteristics.max_index
  ==>
  index >+ max
Proof
INTRO_TAC THEN
ETAC VALID_CHANNEL_ID THEN
RLTAC THEN
ETAC wordsTheory.WORD_NOT_LOWER_EQUAL THEN
ETAC wordsTheory.WORD_HIGHER THEN
STAC
QED

Theorem VALID_CHANNEL_ID_SUC_IMPLIES_VALID_CHANNEL_LEMMA:
!device_characteristics n.
  SUC n < dimword (: 'a) /\
  VALID_CHANNEL_ID device_characteristics (n2w (SUC n) : 'a word)
  ==>
  VALID_CHANNEL_ID device_characteristics (n2w n)
Proof
INTRO_TAC THEN
ETAC stateTheory.VALID_CHANNEL_ID THEN
IRTAC word_lemmasTheory.SUC_LEQ_IMPLIES_LEQ_LEMMA THEN
STAC
QED

Theorem VALID_CHANNEL_ID_NOT_ZERO_IMPLIES_VALID_CHANNEL_PRE_LEMMA:
!device_characteristics i.
  i <> 0w /\
  VALID_CHANNEL_ID device_characteristics i
  ==>
  VALID_CHANNEL_ID device_characteristics (i - 1w)
Proof
INTRO_TAC THEN
ETAC stateTheory.VALID_CHANNEL_ID THEN
IRTAC word_lemmasTheory.NEQ_ZERO_IMPLIES_PRE_LT_LEMMA THEN
IRTAC wordsTheory.WORD_LOWER_LOWER_EQ_TRANS THEN
IRTAC wordsTheory.WORD_LOWER_IMP_LOWER_OR_EQ THEN
STAC
QED

Theorem MAX_INDEX_VALID_CHANNEL_LEMMA:
!device_characteristics max_index.
  max_index = device_characteristics.dma_characteristics.max_index
  ==>
  VALID_CHANNEL_ID device_characteristics max_index
Proof
INTRO_TAC THEN
ETAC stateTheory.VALID_CHANNEL_ID THEN
LRTAC THEN
REWRITE_TAC [wordsTheory.WORD_LOWER_EQ_REFL]
QED






Theorem NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA:
!device_characteristics.
  ~INTERNAL_BDS device_characteristics
  ==>
  EXTERNAL_BDS device_characteristics
Proof
INTRO_TAC THEN
PTAC stateTheory.EXTERNAL_BDS THEN
PTAC stateTheory.INTERNAL_BDS THEN
CCONTR_TAC THEN
PAT_X_ASSUM “x” (fn thm => ASSUME_TAC thm THEN ASSUME_TAC (SPEC ((lhs o dest_neg o concl) thm) stateTheory.bd_location_type_nchotomy)) THEN
SPLIT_ASM_DISJS_TAC THENL
[
 LRTAC THEN
 CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
 ,
 LRTAC THEN
 CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
]
QED

Theorem NOT_EXTERNAL_BDS_IMPLIES_INTERNAL_BDS_LEMMA:
!device_characteristics.
  ~EXTERNAL_BDS device_characteristics
  ==>
  INTERNAL_BDS device_characteristics
Proof
INTRO_TAC THEN
ETAC stateTheory.EXTERNAL_BDS THEN
ETAC stateTheory.INTERNAL_BDS THEN
(fn (A, t) =>
 let val neg = hd A in
 let val location = (lhs o dest_neg) neg in
 let val thm = SPEC location stateTheory.bd_location_type_nchotomy in
   ASSUME_TAC thm (A, t)
 end end end) THEN
SPLIT_ASM_DISJS_TAC THENL
[
 STAC
 ,
 LRTAC THEN
 CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
]
QED

Theorem EXTERNAL_BDS_IMPLIES_NOT_INTERNAL_BDS_LEMMA:
!device_characteristics.
  EXTERNAL_BDS device_characteristics
  ==>
  ~INTERNAL_BDS device_characteristics
Proof
INTRO_TAC THEN
PTAC stateTheory.EXTERNAL_BDS THEN
PTAC stateTheory.INTERNAL_BDS THEN
LRTAC THEN
REWRITE_TAC [GSYM stateTheory.bd_location_type_distinct]
QED

Theorem INTERNAL_BDS_IMPLIES_NOT_EXTERNAL_BDS_LEMMA:
!device_characteristics.
  INTERNAL_BDS device_characteristics
  ==>
  ~EXTERNAL_BDS device_characteristics
Proof
INTRO_TAC THEN
PTAC stateTheory.EXTERNAL_BDS THEN
PTAC stateTheory.INTERNAL_BDS THEN
LRTAC THEN
REWRITE_TAC [stateTheory.bd_location_type_distinct]
QED


val _ = export_theory();

