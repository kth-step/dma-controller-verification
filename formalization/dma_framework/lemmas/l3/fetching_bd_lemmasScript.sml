open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory abstractTheory concreteTheory proof_obligationsTheory invariant_l3Theory l3Theory;

val _ = new_theory "fetching_bd_lemmas";

Definition FETCHING_BD_FETCH_BD_ABSTRACT_CONCRETE:
FETCHING_BD_FETCH_BD_ABSTRACT_CONCRETE device_characteristics channel_id
 verification operation
 concrete_bds1 concrete_bds2 internal_state1 internal_state22 internal_state32
 channel22 channel32 channel23 channel33 memory read_reply = (
  verification = cverification device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  concrete_bds1 = verification.bds_to_fetch memory internal_state1 /\
  concrete_bds2 = verification.bds_to_fetch memory internal_state32 /\
  (internal_state22, channel23) = fetching_bd_fetch_bd_abstract operation.fetch_bd internal_state1 channel22 (SOME read_reply) /\
  (internal_state32, channel33) = fetching_bd_fetch_bd_concrete operation.fetch_bd internal_state1 channel32 (SOME read_reply)
)
End

Definition EXTERNAL_FETCH_BD_REPLY:
EXTERNAL_FETCH_BD_REPLY operation memory internal_state (bytes, tag1) =
!tag2 addresses.
  operation.fetch_bd_addresses internal_state = (addresses, tag2)
  ==>
  tag1 = tag2 /\
  MAP memory addresses = bytes
End

Definition EXTERNAL_BDS_FETCH_REPLY:
EXTERNAL_BDS_FETCH_REPLY device_characteristics channel_id memory channel internal_state =
  !read_reply.
    EXTERNAL_BDS device_characteristics /\
    channel.pending_accesses.replies.fetching_bd = SOME read_reply
    ==>
    EXTERNAL_FETCH_BD_REPLY (coperation device_characteristics channel_id) memory internal_state read_reply
End

Theorem INVARIANT_EXTERNAL_FETCH_BD_REPLY_IMPLIES_EXTERNAL_BDS_FETCH_REPLY_LEMMA:
!device_characteristics memory device channel_id.
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device /\
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  EXTERNAL_BDS_FETCH_REPLY device_characteristics channel_id memory (schannel device channel_id) device.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC invariant_l3Theory.INVARIANT_EXTERNAL_FETCH_BD_REPLY THEN
PTAC EXTERNAL_BDS_FETCH_REPLY THEN
INTRO_TAC THEN
PTAC EXTERNAL_FETCH_BD_REPLY THEN
INTRO_TAC THEN
FAIRTAC THEN
STAC
QED

Theorem ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_PENDING_ACCESSES_LEMMA:
!concrete_bds channel2 channel3.
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds channel2 channel3
  ==>
  channel2.pending_accesses = channel3.pending_accesses
Proof
INTRO_TAC THEN
PTAC stateTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
STAC
QED

Theorem ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_ABSTRACT_EQ_CONCRETE_BDS_LEMMA:
!concrete_bds1 channel22 channel32.
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel22 channel32
  ==>
  channel22.queue.bds_to_fetch = concrete_bds1
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
STAC
QED

Theorem FETCH_BD_EMPTY_QUEUE_IMPLIES_F_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width,
                            'internal_state_type, 'tag_width) device_characteristics_type)
 channel_id verification operation internal_state1
 internal_state2 read_reply bd_ras_was_update memory.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  verification = cverification device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  (internal_state2, SOME bd_ras_was_update) = operation.fetch_bd internal_state1 (SOME read_reply) /\
  verification.bds_to_fetch memory internal_state1 = []
  ==>
  F
Proof
INTRO_TAC THEN
ETAC proof_obligationsTheory.PROOF_OBLIGATION_NO_BDS_TO_FETCH THEN
AIRTAC THEN
QLRTAC THEN
QLRTAC THEN
EQ_PAIR_ASM_TAC THEN
HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
QED

Theorem UPDATE_BD_TO_FETCH_NOT_UPDATE_BD_FETCHED_IMPLIES_F_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width,
                            'internal_state_type, 'tag_width) device_characteristics_type)
 channel_id verification operation bd_ras_was_to_fetch
 bd_ras_was_fetched read_reply bds_to_fetch memory internal_state1 internal_state2.
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  EXTERNAL_FETCH_BD_REPLY operation memory internal_state1 read_reply /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  EXTERNAL_BDS device_characteristics /\
  verification = cverification device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  (bd_ras_was_to_fetch, update)::bds_to_fetch = verification.bds_to_fetch memory internal_state1 /\
  (internal_state2, SOME (bd_ras_was_fetched, no_update)) = operation.fetch_bd internal_state1 (SOME read_reply)
  ==>
  F
Proof
INTRO_TAC THEN
ETAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL THEN
AITAC THEN
EXPAND_TERM_TAC "read_reply" THEN
AITAC THEN
(fn (A, t) =>
 let val qimp = valOf (List.find is_forall A) in
 let val imp = (#2 o strip_forall) qimp in
 let val ant = (#1 o dest_imp) imp in
 let val conjs = strip_conj ant in
 let val eqs = filter is_eq conjs in
 let val field_name = "channel_operations_type_fetch_bd_addresses" in
 let val fetch_bd_addresses_eq = valOf ((List.find (fn term => (term_to_string o #1 o strip_comb o lhs) term = field_name) eqs)) in
 let val fetch_bd_addresses = lhs fetch_bd_addresses_eq in
 let val thm_type = INST_TYPE [alpha |-> type_of fetch_bd_addresses] boolTheory.EXISTS_REFL in
 let val thm = GSYM (SPEC fetch_bd_addresses thm_type) in
   (ASSUME_TAC thm THEN AXTAC) (A, t)
 end end end end end end end end end end) THEN
AITAC THEN
PTAC EXTERNAL_FETCH_BD_REPLY THEN
FAIRTAC THEN
RLTAC THEN
LRTAC THEN
RLTAC THEN
AIRTAC THEN
HYP_CONTR_NEQ_LEMMA_TAC stateTheory.bd_update_type_distinct
QED

Theorem NOT_UPDATE_BD_TO_FETCH_UPDATE_BD_FETCHED_IMPLIES_F_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width,
                            'internal_state_type, 'tag_width) device_characteristics_type)
 channel_id verification operation bd_ras_was_to_fetch
 bd_ras_was_fetched bytes tag bds_to_fetch memory internal_state1 internal_state2.
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  EXTERNAL_FETCH_BD_REPLY operation memory internal_state1 (bytes, tag) /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  EXTERNAL_BDS device_characteristics /\
  verification = cverification device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  (bd_ras_was_to_fetch, no_update)::bds_to_fetch = verification.bds_to_fetch memory internal_state1 /\
  (internal_state2, SOME (bd_ras_was_fetched, update)) = operation.fetch_bd internal_state1 (SOME (bytes, tag))
  ==>
  F
Proof
INTRO_TAC THEN
ETAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL THEN
AITAC THEN
AITAC THEN
(fn (A, t) =>
 let val qimp = valOf (List.find is_forall A) in
 let val imp = (#2 o strip_forall) qimp in
 let val ant = (#1 o dest_imp) imp in
 let val conjs = strip_conj ant in
 let val eqs = filter is_eq conjs in
 let val field_name = "channel_operations_type_fetch_bd_addresses" in
 let val fetch_bd_addresses_eq = valOf ((List.find (fn term => (term_to_string o #1 o strip_comb o lhs) term = field_name) eqs)) in
 let val fetch_bd_addresses = lhs fetch_bd_addresses_eq in
 let val thm_type = INST_TYPE [alpha |-> type_of fetch_bd_addresses] boolTheory.EXISTS_REFL in
 let val thm = GSYM (SPEC fetch_bd_addresses thm_type) in
   (ASSUME_TAC thm THEN AXTAC) (A, t)
 end end end end end end end end end end) THEN
AITAC THEN
ETAC EXTERNAL_FETCH_BD_REPLY THEN
FAIRTAC THEN
RLTAC THEN
LRTAC THEN
RLTAC THEN
AIRTAC THEN
HYP_CONTR_NEQ_LEMMA_TAC stateTheory.bd_update_type_distinct
QED

Theorem SAME_QUEUE_IMPLIES_SAME_FIRST_BD_UPDATE_LEMMA:
!device_characteristics channel_id operation verification channel22 bd_ras_was2
 bd_ras_was3 bd_ras_was_update_cyclics memory internal_state1 internal_state2
 reply update_bd2 update_bd3.
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  EXTERNAL_FETCH_BD_REPLY operation memory internal_state1 reply /\
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  verification = cverification device_characteristics channel_id /\
  channel22.queue.bds_to_fetch = verification.bds_to_fetch memory internal_state1 /\
  channel22.queue.bds_to_fetch = (bd_ras_was2, update_bd2)::bd_ras_was_update_cyclics /\
  (internal_state2, SOME (bd_ras_was3, update_bd3)) = operation.fetch_bd internal_state1 (SOME reply)
  ==>
  bd_ras_was3 = bd_ras_was2 /\
  update_bd2 = update_bd3
Proof
INTRO_TAC THEN
EXPAND_TERM_TAC "update_bd2" THEN EXPAND_TERM_TAC "update_bd3" THENL
[
 PTAC EXTERNAL_FETCH_BD_REPLY THEN
 (fn (A, t) =>
  let val qimp = valOf (List.find is_forall A) in
  let val imp = (#2 o strip_forall) qimp in
  let val ant = (#1 o dest_imp) imp in
  let val conjs = strip_conj ant in
  let val eqs = filter is_eq conjs in
  let val field_name = "channel_operations_type_fetch_bd_addresses" in
  let val fetch_bd_addresses_eq = valOf ((List.find (fn term => (term_to_string o #1 o strip_comb o lhs) term = field_name) eqs)) in
  let val fetch_bd_addresses = lhs fetch_bd_addresses_eq in
  let val thm_type = INST_TYPE [alpha |-> type_of fetch_bd_addresses] boolTheory.EXISTS_REFL in
  let val thm = GSYM (SPEC fetch_bd_addresses thm_type) in
    (ASSUME_TAC thm THEN AXTAC) (A, t)
  end end end end end end end end end end) THEN
 AITAC THEN
 RLTAC THEN
 ETAC PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL THEN
 FAITAC THEN
 FAITAC THEN
 STAC
 ,
 IRTAC UPDATE_BD_TO_FETCH_NOT_UPDATE_BD_FETCHED_IMPLIES_F_LEMMA THEN SOLVE_F_ASM_TAC
 ,
 IRTAC NOT_UPDATE_BD_TO_FETCH_UPDATE_BD_FETCHED_IMPLIES_F_LEMMA THEN SOLVE_F_ASM_TAC
 ,
 PTAC EXTERNAL_FETCH_BD_REPLY THEN
 (fn (A, t) =>
  let val qimp = valOf (List.find is_forall A) in
  let val imp = (#2 o strip_forall) qimp in
  let val ant = (#1 o dest_imp) imp in
  let val conjs = strip_conj ant in
  let val eqs = filter is_eq conjs in
  let val field_name = "channel_operations_type_fetch_bd_addresses" in
  let val fetch_bd_addresses_eq = valOf ((List.find (fn term => (term_to_string o #1 o strip_comb o lhs) term = field_name) eqs)) in
  let val fetch_bd_addresses = lhs fetch_bd_addresses_eq in
  let val thm_type = INST_TYPE [alpha |-> type_of fetch_bd_addresses] boolTheory.EXISTS_REFL in
  let val thm = GSYM (SPEC fetch_bd_addresses thm_type) in
    (ASSUME_TAC thm THEN AXTAC) (A, t)
  end end end end end end end end end end) THEN
 AITAC THEN
 RLTAC THEN
 ETAC PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL THEN
 FAITAC THEN
 FAITAC THEN
 STAC
]
QED

Theorem UPDATE_CHANNEL_QS_BDS_TO_FETCH_UPDATE_LEMMA:
!channel22 channel23 bd_ras_was_update_cyclics q.
  channel23 = update_channel_qs channel22 [fetch_queue bd_ras_was_update_cyclics; update_queue q]
  ==>
  channel23.queue.bds_to_fetch = bd_ras_was_update_cyclics
Proof
INTRO_TAC THEN
PTAC operationsTheory.update_channel_qs THEN
PTAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
PTAC operationsTheory.update_q THEN
PTAC operationsTheory.update_q THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem UPDATE_CHANNEL_QS_BDS_TO_FETCH_PROCESS_LEMMA:
!channel22 channel23 bd_ras_was_update_cyclics q.
  channel23 = update_channel_qs channel22 [fetch_queue bd_ras_was_update_cyclics; process_queue q]
  ==>
  channel23.queue.bds_to_fetch = bd_ras_was_update_cyclics
Proof
INTRO_TAC THEN
ETAC operationsTheory.update_channel_qs THEN
ETAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem FETCHED_BD_PRESERVES_BDS_TO_FETCH_EQ_ACYCLIC_LEMMA:
!device_characteristics channel_id operation verification channel22
 channel23 bd_ras_was2 bd_ras_was3 bd_ras_was_update_cyclics memory
 internal_state1 internal_state2 reply q.
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  EXTERNAL_FETCH_BD_REPLY operation memory internal_state1 reply /\
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  verification = cverification device_characteristics channel_id /\
  channel22.queue.bds_to_fetch = verification.bds_to_fetch memory internal_state1 /\
  BDS_TO_FETCH_DISJOINT channel22.queue.bds_to_fetch /\
  channel22.queue.bds_to_fetch = (bd_ras_was2, no_update)::bd_ras_was_update_cyclics /\
  channel23 = update_channel_qs channel22 [fetch_queue bd_ras_was_update_cyclics; process_queue q] /\
  (internal_state2, SOME (bd_ras_was3, no_update)) = operation.fetch_bd internal_state1 (SOME reply)
  ==>
  channel23.queue.bds_to_fetch = verification.bds_to_fetch memory internal_state2
Proof
INTRO_TAC THEN
ITAC SAME_QUEUE_IMPLIES_SAME_FIRST_BD_UPDATE_LEMMA THEN
LRTAC THEN
ETAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT THEN
AITAC THEN
PTAC EXTERNAL_FETCH_BD_REPLY THEN
(fn (A, t) =>
 let val qimp = valOf (List.find is_forall A) in
 let val imp = (#2 o strip_forall) qimp in
 let val ant = (#1 o dest_imp) imp in
 let val conjs = strip_conj ant in
 let val eqs = filter is_eq conjs in
 let val field_name = "channel_operations_type_fetch_bd_addresses" in
 let val fetch_bd_addresses_eq = valOf ((List.find (fn term => (term_to_string o #1 o strip_comb o lhs) term = field_name) eqs)) in
 let val fetch_bd_addresses = lhs fetch_bd_addresses_eq in
 let val thm_type = INST_TYPE [alpha |-> type_of fetch_bd_addresses] boolTheory.EXISTS_REFL in
 let val thm = GSYM (SPEC fetch_bd_addresses thm_type) in
   (ASSUME_TAC thm THEN AXTAC) (A, t)
 end end end end end end end end end end) THEN
FAITAC THEN
RLTAC THEN
RLTAC THEN
LRTAC THEN
AITAC THEN
IRTAC UPDATE_CHANNEL_QS_BDS_TO_FETCH_PROCESS_LEMMA THEN
STAC
QED

Theorem FETCHED_ACYCLIC_BD_PRESERVES_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics channel_id operation verification channel22
 channel23 bd_ras_was2 bd_ras_was3 bd_ras_was_update_cyclics memory
 internal_state1 internal_state2 reply q.
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  EXTERNAL_FETCH_BD_REPLY operation memory internal_state1 reply /\
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  verification = cverification device_characteristics channel_id /\
  channel22.queue.bds_to_fetch = verification.bds_to_fetch memory internal_state1 /\
  BDS_TO_FETCH_DISJOINT channel22.queue.bds_to_fetch /\
  channel22.queue.bds_to_fetch = (bd_ras_was2, update)::bd_ras_was_update_cyclics /\
  channel23 = update_channel_qs channel22 [fetch_queue bd_ras_was_update_cyclics; update_queue q] /\
  (internal_state2, SOME (bd_ras_was3, update)) = operation.fetch_bd internal_state1 (SOME reply)
  ==>
  channel23.queue.bds_to_fetch = verification.bds_to_fetch memory internal_state2
Proof
INTRO_TAC THEN
ITAC SAME_QUEUE_IMPLIES_SAME_FIRST_BD_UPDATE_LEMMA THEN
LRTAC THEN
ETAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT THEN
AITAC THEN
PTAC EXTERNAL_FETCH_BD_REPLY THEN
LRTAC THEN
(fn (A, t) =>
 let val qimp = valOf (List.find is_forall A) in
 let val imp = (#2 o strip_forall) qimp in
 let val ant = (#1 o dest_imp) imp in
 let val conjs = strip_conj ant in
 let val eqs = filter is_eq conjs in
 let val field_name = "channel_operations_type_fetch_bd_addresses" in
 let val fetch_bd_addresses_eq = valOf ((List.find (fn term => (term_to_string o #1 o strip_comb o lhs) term = field_name) eqs)) in
 let val fetch_bd_addresses = lhs fetch_bd_addresses_eq in
 let val thm_type = INST_TYPE [alpha |-> type_of fetch_bd_addresses] boolTheory.EXISTS_REFL in
 let val thm = GSYM (SPEC fetch_bd_addresses thm_type) in
   (ASSUME_TAC thm THEN AXTAC) (A, t)
 end end end end end end end end end end) THEN
FAITAC THEN
RLTAC THEN
RLTAC THEN
AITAC THEN
IRTAC UPDATE_CHANNEL_QS_BDS_TO_FETCH_UPDATE_LEMMA THEN
STAC
QED

(*
Theorem UPDATE_CHANNEL_QS_FETCH_PROCESS_CYCLIC_LEMMA:
!channel22 channel23 bd_ras_was_update_cyclics bd_ras_was q update_bd cyclic_bd.
  channel23 = update_channel_qs channel22 [fetch_queue (bd_ras_was_update_cyclics ++ [(bd_ras_was, update_bd, cyclic_bd)]);
                                           process_queue q]
  ==>
  channel23.queue.bds_to_fetch = bd_ras_was_update_cyclics ++ [(bd_ras_was, update_bd, cyclic_bd)]
Proof
INTRO_TAC THEN
ETAC operationsTheory.update_channel_qs THEN
ETAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem UPDATE_CHANNEL_QS_FETCH_UPDATE_CYCLIC_LEMMA:
!channel22 channel23 bd_ras_was_update_cyclics bd_ras_was q update_bd cyclic_bd.
  channel23 = update_channel_qs channel22 [fetch_queue (bd_ras_was_update_cyclics ++ [(bd_ras_was, update_bd, cyclic_bd)]);
                                           update_queue q]
  ==>
  channel23.queue.bds_to_fetch = bd_ras_was_update_cyclics ++ [(bd_ras_was, update_bd, cyclic_bd)]
Proof
INTRO_TAC THEN
ETAC operationsTheory.update_channel_qs THEN
ETAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem FETCHED_BD_PRESERVES_BDS_TO_FETCH_EQ_CYCLIC_LEMMA:
!device_characteristics channel_id operation verification channel22
 channel23 bd_ras_was2 bd_ras_was3 bd_ras_was_update_cyclics memory
 internal_state1 internal_state2 reply q.
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  EXTERNAL_FETCH_BD_REPLY operation memory internal_state1 reply /\
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  verification = cverification device_characteristics channel_id /\
  channel22.queue.bds_to_fetch = verification.bds_to_fetch memory internal_state1 /\
  channel22.queue.bds_to_fetch = (bd_ras_was2, no_update, cyclic)::bd_ras_was_update_cyclics /\
  channel23 = update_channel_qs channel22 [fetch_queue (bd_ras_was_update_cyclics ++ [(bd_ras_was2, no_update, cyclic)]);
                                           process_queue q] /\
  (internal_state2, SOME (bd_ras_was3, no_update)) = operation.fetch_bd internal_state1 (SOME reply)
  ==>
  channel23.queue.bds_to_fetch = verification.bds_to_fetch memory internal_state2
Proof
INTRO_TAC THEN
ITAC SAME_QUEUE_IMPLIES_SAME_FIRST_BD_UPDATE_LEMMA THEN
LRTAC THEN
ETAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT THEN
AITAC THEN
PTAC EXTERNAL_FETCH_BD_REPLY THEN
LRTAC THEN
(fn (A, t) =>
 let val qimp = valOf (List.find is_forall A) in
 let val imp = (#2 o strip_forall) qimp in
 let val ant = (#1 o dest_imp) imp in
 let val conjs = strip_conj ant in
 let val eqs = filter is_eq conjs in
 let val field_name = "channel_operations_type_fetch_bd_addresses" in
 let val fetch_bd_addresses_eq = valOf ((List.find (fn term => (term_to_string o #1 o strip_comb o lhs) term = field_name) eqs)) in
 let val fetch_bd_addresses = lhs fetch_bd_addresses_eq in
 let val thm_type = INST_TYPE [alpha |-> type_of fetch_bd_addresses] boolTheory.EXISTS_REFL in
 let val thm = GSYM (SPEC fetch_bd_addresses thm_type) in
   (ASSUME_TAC thm THEN AXTAC) (A, t)
 end end end end end end end end end end) THEN
FAITAC THEN
RLTAC THEN
RLTAC THEN
AITAC THEN
WEAKEN_TAC is_imp THEN
FIRTAC UPDATE_CHANNEL_QS_FETCH_PROCESS_CYCLIC_LEMMA THEN
ALL_LRTAC THEN
STAC
QED

Theorem FETCHED_CYCLIC_BD_PRESERVES_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics channel_id operation verification channel22
 channel23 bd_ras_was2 bd_ras_was3 bd_ras_was_update_cyclics memory
 internal_state1 internal_state2 reply q update_bd2 update_bd3.
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  EXTERNAL_FETCH_BD_REPLY operation memory internal_state1 reply /\
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  verification = cverification device_characteristics channel_id /\
  channel22.queue.bds_to_fetch = verification.bds_to_fetch memory internal_state1 /\
  channel22.queue.bds_to_fetch = (bd_ras_was2, update_bd2, cyclic)::bd_ras_was_update_cyclics /\
  channel23 = update_channel_qs channel22 [fetch_queue (bd_ras_was_update_cyclics ++ [(bd_ras_was2, update_bd2, cyclic)]);
                                           update_queue q] /\
  (internal_state2, SOME (bd_ras_was3, update_bd3)) = operation.fetch_bd internal_state1 (SOME reply)
  ==>
  channel23.queue.bds_to_fetch = verification.bds_to_fetch memory internal_state2
Proof
INTRO_TAC THEN
ITAC SAME_QUEUE_IMPLIES_SAME_FIRST_BD_UPDATE_LEMMA THEN
LRTAC THEN
ETAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT THEN
AITAC THEN
PTAC EXTERNAL_FETCH_BD_REPLY THEN
LRTAC THEN
(fn (A, t) =>
 let val qimp = valOf (List.find is_forall A) in
 let val imp = (#2 o strip_forall) qimp in
 let val ant = (#1 o dest_imp) imp in
 let val conjs = strip_conj ant in
 let val eqs = filter is_eq conjs in
 let val field_name = "channel_operations_type_fetch_bd_addresses" in
 let val fetch_bd_addresses_eq = valOf ((List.find (fn term => (term_to_string o #1 o strip_comb o lhs) term = field_name) eqs)) in
 let val fetch_bd_addresses = lhs fetch_bd_addresses_eq in
 let val thm_type = INST_TYPE [alpha |-> type_of fetch_bd_addresses] boolTheory.EXISTS_REFL in
 let val thm = GSYM (SPEC fetch_bd_addresses thm_type) in
   (ASSUME_TAC thm THEN AXTAC) (A, t)
 end end end end end end end end end end) THEN
FAITAC THEN
RLTAC THEN
RLTAC THEN
AITAC THEN
WEAKEN_TAC is_imp THEN
IRTAC UPDATE_CHANNEL_QS_FETCH_UPDATE_CYCLIC_LEMMA THEN
STAC
QED
*)

Theorem COLLECT_BD_RAS_WAS_UPDATE_CYCLIC_LEMMA:
!h q r q' update_bd.
  h = (q, r) /\
  r = q' /\
  q' = update_bd
  ==>
  h = (q, update_bd)
Proof
INTRO_TAC THEN
ALL_LRTAC THEN
STAC
QED

Theorem UPDATE_CHANNEL_QS_FETCH_UPDATE_APPEND_BDS_TO_UPDATE_PRESERVES_BDS_TO_UPDATE_EQ_LEMMA:
!channel22 channel32 channel23 channel33 q bd_ras_was.
  channel23 = update_channel_qs channel22 [fetch_queue q; update_queue (channel22.queue.bds_to_update ++ [bd_ras_was])] /\
  channel33 = append_bds_to_update channel32 bd_ras_was /\
  channel22.queue.bds_to_update = channel32.queue.bds_to_update
  ==>
  channel23.queue.bds_to_update = channel33.queue.bds_to_update
Proof
INTRO_TAC THEN
PTAC operationsTheory.append_bds_to_update THEN
PTAC operationsTheory.update_channel_qs THEN
PTAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem UPDATE_CHANNEL_QS_FETCH_PROCESS_APPEND_BDS_TO_PROCESS_PRESERVES_BDS_TO_UPDATE_EQ_LEMMA:
!channel22 channel32 channel23 channel33 t q bd_ras_was.
  channel23 = update_channel_qs channel22 [fetch_queue t; process_queue (channel22.queue.bds_to_process ++ [q])] /\
  channel33 = append_bds_to_process channel32 bd_ras_was /\
  channel22.queue.bds_to_update = channel32.queue.bds_to_update
  ==>
  channel23.queue.bds_to_update = channel33.queue.bds_to_update
Proof
INTRO_TAC THEN
PTAC operationsTheory.append_bds_to_process THEN
PTAC operationsTheory.update_channel_qs THEN
PTAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem UPDATE_CHANNEL_QS_FETCH_PROCESS_APPEND_BDS_TO_PROCESS_PRESERVES_BDS_TO_PROCESS_WRITE_BACK_PENDING_ACCESSES_EQ_LEMMA:
!device_characteristics channel_id operation verification memory reply channel22
 channel32 channel23 channel33 bd_ras_was_update_cyclics bd_ras_was2 bd_ras_was3
 update_bd2 update_bd3 internal_state1 internal_state2.
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  EXTERNAL_FETCH_BD_REPLY operation memory internal_state1 reply /\
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  verification = cverification device_characteristics channel_id /\
  channel22.queue.bds_to_fetch = verification.bds_to_fetch memory internal_state1 /\
  channel22.queue.bds_to_fetch = (bd_ras_was2, update_bd2)::bd_ras_was_update_cyclics /\
  (internal_state2, SOME (bd_ras_was3, update_bd3)) = operation.fetch_bd internal_state1 (SOME reply) /\
  channel23 = update_channel_qs channel22 [fetch_queue bd_ras_was_update_cyclics;
                                           process_queue (channel22.queue.bds_to_process ++ [bd_ras_was2])] /\
  channel33 = append_bds_to_process channel32 bd_ras_was3 /\
  channel22.queue.bds_to_process = channel32.queue.bds_to_process /\
  channel22.queue.bds_to_write_back = channel32.queue.bds_to_write_back /\
  channel22.pending_accesses = channel32.pending_accesses
  ==>
  channel23.queue.bds_to_process = channel33.queue.bds_to_process /\
  channel23.queue.bds_to_write_back = channel33.queue.bds_to_write_back /\
  channel23.pending_accesses = channel33.pending_accesses
Proof
INTRO_TAC THEN
IRTAC SAME_QUEUE_IMPLIES_SAME_FIRST_BD_UPDATE_LEMMA THEN
LRTAC THEN
ETAC operationsTheory.append_bds_to_process THEN
ETAC operationsTheory.update_channel_qs THEN
ETAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem FETCHED_BD_NO_UPDATE_ACYCLIC_BSIMS_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width,
                            'internal_state_type, 'tag_width) device_characteristics_type)
 memory internal_state1 internal_state2 verification
 operation channel_id concrete_bds1 concrete_bds2 channel22 channel32 channel23
 channel33 reply bd_ras_was2 bd_ras_was3 bdrwaus.
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  verification = cverification device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  concrete_bds1 = verification.bds_to_fetch memory internal_state1 /\
  concrete_bds2 = verification.bds_to_fetch memory internal_state2 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel22 channel32 /\
  BDS_TO_FETCH_DISJOINT channel22.queue.bds_to_fetch /\
  EXTERNAL_FETCH_BD_REPLY operation memory internal_state1 reply /\
  (internal_state2, SOME (bd_ras_was3, no_update)) = operation.fetch_bd internal_state1 (SOME reply) /\
  channel23 = update_channel_qs channel22 [fetch_queue bdrwaus; process_queue (channel22.queue.bds_to_process ++ [bd_ras_was2])] /\
  channel33 = append_bds_to_process channel32 bd_ras_was3 /\
  channel22.queue.bds_to_fetch = (bd_ras_was2, no_update)::bdrwaus
  ==>
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel23 channel33
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
REPEAT CONJ_TAC THENL
[
 ITAC FETCHED_BD_PRESERVES_BDS_TO_FETCH_EQ_ACYCLIC_LEMMA THEN
 STAC
 ,
 IRTAC UPDATE_CHANNEL_QS_FETCH_PROCESS_APPEND_BDS_TO_PROCESS_PRESERVES_BDS_TO_UPDATE_EQ_LEMMA THEN
 STAC
 ,
 IRTAC UPDATE_CHANNEL_QS_FETCH_PROCESS_APPEND_BDS_TO_PROCESS_PRESERVES_BDS_TO_PROCESS_WRITE_BACK_PENDING_ACCESSES_EQ_LEMMA THEN
 STAC
 ,
 FIRTAC UPDATE_CHANNEL_QS_FETCH_PROCESS_APPEND_BDS_TO_PROCESS_PRESERVES_BDS_TO_PROCESS_WRITE_BACK_PENDING_ACCESSES_EQ_LEMMA THEN
 STAC
 ,
 FIRTAC UPDATE_CHANNEL_QS_FETCH_PROCESS_APPEND_BDS_TO_PROCESS_PRESERVES_BDS_TO_PROCESS_WRITE_BACK_PENDING_ACCESSES_EQ_LEMMA THEN
 STAC
]
QED

Theorem UPDATE_CHANNEL_QS_FETCH_UPDATE_APPEND_BDS_TO_UPDATE_PRESERVES_BDS_TO_PROCESS_WRITE_BACK_PENDING_ACCESSES_EQ_LEMMA:
!channel22 channel32 channel23 channel33 q1 q2 bd_ras_was.
  channel23 = update_channel_qs channel22 [fetch_queue q1; update_queue q2] /\
  channel33 = append_bds_to_update channel32 bd_ras_was /\
  channel22.queue.bds_to_process = channel32.queue.bds_to_process /\
  channel22.queue.bds_to_write_back = channel32.queue.bds_to_write_back /\
  channel22.pending_accesses = channel32.pending_accesses
  ==>
  channel23.queue.bds_to_process = channel33.queue.bds_to_process /\
  channel23.queue.bds_to_write_back = channel33.queue.bds_to_write_back /\
  channel23.pending_accesses = channel33.pending_accesses
Proof
INTRO_TAC THEN
ETAC operationsTheory.append_bds_to_update THEN
ETAC operationsTheory.update_channel_qs THEN
ETAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem FETCHED_BD_UPDATE_ACYCLIC_BSIMS_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width,
                            'internal_state_type, 'tag_width) device_characteristics_type)
 memory internal_state1 internal_state2 verification
 operation channel_id concrete_bds1 concrete_bds2 channel22 channel32 channel23
 channel33 reply bd_ras_was2 bd_ras_was3 bdrwaus.
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  verification = cverification device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  concrete_bds1 = verification.bds_to_fetch memory internal_state1 /\
  concrete_bds2 = verification.bds_to_fetch memory internal_state2 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel22 channel32 /\
  BDS_TO_FETCH_DISJOINT channel22.queue.bds_to_fetch /\
  EXTERNAL_FETCH_BD_REPLY operation memory internal_state1 reply /\
  (internal_state2, SOME (bd_ras_was3, update)) = operation.fetch_bd internal_state1 (SOME reply) /\
  channel23 = update_channel_qs channel22 [fetch_queue bdrwaus; update_queue (channel22.queue.bds_to_update ++ [bd_ras_was2])] /\
  channel33 = append_bds_to_update channel32 bd_ras_was3 /\
  channel22.queue.bds_to_fetch = (bd_ras_was2, update)::bdrwaus
  ==>
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel23 channel33
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
REPEAT CONJ_TAC THENL
[
 ITAC FETCHED_ACYCLIC_BD_PRESERVES_BDS_TO_FETCH_EQ_LEMMA THEN STAC
 ,
 ITAC SAME_QUEUE_IMPLIES_SAME_FIRST_BD_UPDATE_LEMMA THEN
 LRTAC THEN
 ITAC UPDATE_CHANNEL_QS_FETCH_UPDATE_APPEND_BDS_TO_UPDATE_PRESERVES_BDS_TO_UPDATE_EQ_LEMMA THEN
 STAC
 ,
 IRTAC UPDATE_CHANNEL_QS_FETCH_UPDATE_APPEND_BDS_TO_UPDATE_PRESERVES_BDS_TO_PROCESS_WRITE_BACK_PENDING_ACCESSES_EQ_LEMMA THEN STAC
 ,
 IRTAC UPDATE_CHANNEL_QS_FETCH_UPDATE_APPEND_BDS_TO_UPDATE_PRESERVES_BDS_TO_PROCESS_WRITE_BACK_PENDING_ACCESSES_EQ_LEMMA THEN STAC
 ,
 IRTAC UPDATE_CHANNEL_QS_FETCH_UPDATE_APPEND_BDS_TO_UPDATE_PRESERVES_BDS_TO_PROCESS_WRITE_BACK_PENDING_ACCESSES_EQ_LEMMA THEN STAC
]
QED

(*
Theorem FETCHED_BD_UPDATE_CYCLIC_BSIMS_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA:
!device_characteristics memory internal_state1 internal_state2 verification
 operation channel_id concrete_bds1 concrete_bds2 channel22 channel32 channel23
 channel33 reply bd_ras_was2 bd_ras_was3 bdrwaucs.
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  verification = cverification device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  concrete_bds1 = verification.bds_to_fetch memory internal_state1 /\
  concrete_bds2 = verification.bds_to_fetch memory internal_state2 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel22 channel32 /\
  EXTERNAL_FETCH_BD_REPLY operation memory internal_state1 reply /\
  (internal_state2, SOME (bd_ras_was3, update)) = operation.fetch_bd internal_state1 (SOME reply) /\
  channel23 = update_channel_qs channel22 [fetch_queue (bdrwaucs ++ [(bd_ras_was2, update, cyclic)]);
                                           update_queue (channel22.queue.bds_to_update ++ [bd_ras_was2])] /\
  channel33 = append_bds_to_update channel32 bd_ras_was3 /\
  channel22.queue.bds_to_fetch = (bd_ras_was2, update, cyclic)::bdrwaucs
  ==>
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel23 channel33
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
REPEAT CONJ_TAC THENL
[
 IRTAC FETCHED_CYCLIC_BD_PRESERVES_BDS_TO_FETCH_EQ_LEMMA THEN STAC
 ,
 IRTAC SAME_QUEUE_IMPLIES_SAME_FIRST_BD_UPDATE_LEMMA THEN
 LRTAC THEN
 ITAC UPDATE_CHANNEL_QS_FETCH_UPDATE_APPEND_BDS_TO_UPDATE_PRESERVES_BDS_TO_UPDATE_EQ_LEMMA THEN
 STAC
 ,
 ITAC UPDATE_CHANNEL_QS_FETCH_UPDATE_APPEND_BDS_TO_UPDATE_PRESERVES_BDS_TO_PROCESS_WRITE_BACK_PENDING_ACCESSES_EQ_LEMMA THEN STAC
 ,
 ITAC UPDATE_CHANNEL_QS_FETCH_UPDATE_APPEND_BDS_TO_UPDATE_PRESERVES_BDS_TO_PROCESS_WRITE_BACK_PENDING_ACCESSES_EQ_LEMMA THEN STAC
 ,
 ITAC UPDATE_CHANNEL_QS_FETCH_UPDATE_APPEND_BDS_TO_UPDATE_PRESERVES_BDS_TO_PROCESS_WRITE_BACK_PENDING_ACCESSES_EQ_LEMMA THEN STAC
]
QED
*)

Theorem UPDATE_CHANNEL_QS_FETCH_PROCESS_PRESERVES_BDS_TO_UPDATE_WRITE_BACK_PENDING_ACCESSES_EQ_LEMMA:
!channel22 channel32 channel23 channel33 q1 q2 bd_ras_was.
  channel23 = update_channel_qs channel22 [fetch_queue q1; process_queue q2] /\
  channel33 = append_bds_to_process channel32 bd_ras_was /\
  channel22.queue.bds_to_update = channel32.queue.bds_to_update /\
  channel22.queue.bds_to_write_back = channel32.queue.bds_to_write_back /\
  channel22.pending_accesses = channel32.pending_accesses
  ==>
  channel23.queue.bds_to_update = channel33.queue.bds_to_update /\
  channel23.queue.bds_to_write_back = channel33.queue.bds_to_write_back /\
  channel23.pending_accesses = channel33.pending_accesses
Proof
INTRO_TAC THEN
ETAC operationsTheory.append_bds_to_process THEN
ETAC operationsTheory.update_channel_qs THEN
ETAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem UPDATE_CHANNEL_QS_FETCH_PROCESS_APPEND_BDS_TO_PROCESS_PRESERVES_BDS_TO_PROCESS_EQ_LEMMA:
!channel22 channel32 channel23 channel33 bd_ras_was q.
  channel23 = update_channel_qs channel22 [fetch_queue q; process_queue (channel22.queue.bds_to_process ++ [bd_ras_was])] /\
  channel33 = append_bds_to_process channel32 bd_ras_was /\
  channel22.queue.bds_to_process = channel32.queue.bds_to_process
  ==>
  channel23.queue.bds_to_process = channel33.queue.bds_to_process
Proof
INTRO_TAC THEN
ETAC operationsTheory.append_bds_to_process THEN
ETAC operationsTheory.update_channel_qs THEN
ETAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

(*
Theorem FETCHED_BD_NO_UPDATE_CYCLIC_BSIMS_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA:
!device_characteristics memory internal_state1 internal_state2 verification
 operation channel_id concrete_bds1 concrete_bds2 channel22 channel32 channel23
 channel33 reply bd_ras_was2 bd_ras_was3 bdrwaucs.
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  verification = cverification device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  concrete_bds1 = verification.bds_to_fetch memory internal_state1 /\
  concrete_bds2 = verification.bds_to_fetch memory internal_state2 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel22 channel32 /\
  EXTERNAL_FETCH_BD_REPLY operation memory internal_state1 reply /\
  (internal_state2, SOME (bd_ras_was3, no_update)) = operation.fetch_bd internal_state1 (SOME reply) /\
  channel23 = update_channel_qs channel22 [fetch_queue (bdrwaucs ++ [(bd_ras_was2, no_update, cyclic)]);
                                           process_queue (channel22.queue.bds_to_process ++ [bd_ras_was2])] /\
  channel33 = append_bds_to_process channel32 bd_ras_was3 /\
  channel22.queue.bds_to_fetch = (bd_ras_was2, no_update, cyclic)::bdrwaucs
  ==>
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel23 channel33
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
REPEAT CONJ_TAC THENL
[
 ITAC FETCHED_BD_PRESERVES_BDS_TO_FETCH_EQ_CYCLIC_LEMMA THEN STAC
 ,
 IRTAC UPDATE_CHANNEL_QS_FETCH_PROCESS_PRESERVES_BDS_TO_UPDATE_WRITE_BACK_PENDING_ACCESSES_EQ_LEMMA THEN STAC
 ,
 ITAC SAME_QUEUE_IMPLIES_SAME_FIRST_BD_UPDATE_LEMMA THEN
 LRTAC THEN
 IRTAC UPDATE_CHANNEL_QS_FETCH_PROCESS_APPEND_BDS_TO_PROCESS_PRESERVES_BDS_TO_PROCESS_EQ_LEMMA THEN
 STAC
 ,
 IRTAC UPDATE_CHANNEL_QS_FETCH_PROCESS_PRESERVES_BDS_TO_UPDATE_WRITE_BACK_PENDING_ACCESSES_EQ_LEMMA THEN STAC
 ,
 IRTAC UPDATE_CHANNEL_QS_FETCH_PROCESS_PRESERVES_BDS_TO_UPDATE_WRITE_BACK_PENDING_ACCESSES_EQ_LEMMA THEN STAC
]
QED
*)

(*
Theorem OPERATION_FETCH_BD_UPDATE_LEMMA:
!internal_state1 internal_state2 reply bd_ras_was_update bd_ras_was operation.
  (internal_state2, SOME bd_ras_was_update) = operation.fetch_bd internal_state1 (SOME reply) /\
  bd_ras_was_update = (bd_ras_was, no_update)
  ==>
  (internal_state2, SOME (bd_ras_was, no_update)) = operation.fetch_bd internal_state1 (SOME reply)
Proof
INTRO_TAC THEN
STAC
QED
*)

Theorem FETCHING_BD_UPDATE_QS_APPEND_BDS_TO_PROCESS_PRESERVE_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width,
                            'internal_state_type, 'tag_width) device_characteristics_type)
 bd_ras_was_update bd_ras_was concrete_bds1 concrete_bds2 channel_id memory internal_state1
 internal_state2 operation bd_reply channel22 channel32 channel23 channel33 verification.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  bd_ras_was_update = (bd_ras_was, no_update) /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  EXTERNAL_BDS device_characteristics /\
  verification = cverification device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  concrete_bds1 = verification.bds_to_fetch memory internal_state1 /\
  concrete_bds2 = verification.bds_to_fetch memory internal_state2 /\
  EXTERNAL_FETCH_BD_REPLY operation memory internal_state1 bd_reply /\
  BDS_TO_FETCH_DISJOINT channel22.queue.bds_to_fetch /\
  (internal_state2, SOME bd_ras_was_update) = operation.fetch_bd internal_state1 (SOME bd_reply) /\
  channel23 = fetching_bd_update_qs_abstract channel22 channel22.queue.bds_to_fetch /\
  channel33 = append_bds_to_process channel32 bd_ras_was /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel22 channel32
  ==>
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel23 channel33
Proof
INTRO_TAC THEN
PTAC abstractTheory.fetching_bd_update_qs_abstract THENL
[
 MATCH_MP_TAC boolTheory.FALSITY THEN
 MATCH_MP_TAC FETCH_BD_EMPTY_QUEUE_IMPLIES_F_LEMMA THEN
 Q.EXISTS_TAC ‘device_characteristics’ THEN
 Q.EXISTS_TAC ‘channel_id’ THEN
 Q.EXISTS_TAC ‘verification’ THEN
 Q.EXISTS_TAC ‘operation’ THEN
 Q.EXISTS_TAC ‘internal_state1’ THEN
 Q.EXISTS_TAC ‘internal_state2’ THEN
 Q.EXISTS_TAC ‘bd_reply’ THEN
 Q.EXISTS_TAC ‘bd_ras_was_update’ THEN
 Q.EXISTS_TAC ‘memory’ THEN
 IRTAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_ABSTRACT_EQ_CONCRETE_BDS_LEMMA THEN
 STAC
 ,
 MATCH_MP_TAC boolTheory.FALSITY THEN
 MATCH_MP_TAC UPDATE_BD_TO_FETCH_NOT_UPDATE_BD_FETCHED_IMPLIES_F_LEMMA THEN
 Q.EXISTS_TAC ‘device_characteristics’ THEN
 Q.EXISTS_TAC ‘channel_id’ THEN
 Q.EXISTS_TAC ‘verification’ THEN
 Q.EXISTS_TAC ‘operation’ THEN
 Q.EXISTS_TAC ‘q’ THEN
 Q.EXISTS_TAC ‘bd_ras_was’ THEN
 Q.EXISTS_TAC ‘bd_reply’ THEN
 PAXTAC THEN
 Q.EXISTS_TAC ‘t’ THEN
 CONJS_TAC THEN TRY STAC THEN
 WEAKEN_TAC (fn _ => true) THEN
 LRTAC THEN LRTAC THEN
 IRTAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_ABSTRACT_EQ_CONCRETE_BDS_LEMMA THEN
 STAC
 ,
 MATCH_MP_TAC FETCHED_BD_NO_UPDATE_ACYCLIC_BSIMS_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA THEN
 Q.EXISTS_TAC ‘device_characteristics’ THEN
 Q.EXISTS_TAC ‘memory’ THEN
 Q.EXISTS_TAC ‘internal_state1’ THEN
 Q.EXISTS_TAC ‘internal_state2’ THEN
 Q.EXISTS_TAC ‘verification’ THEN
 Q.EXISTS_TAC ‘operation’ THEN
 Q.EXISTS_TAC ‘channel_id’ THEN
 Q.EXISTS_TAC ‘concrete_bds1’ THEN
 Q.EXISTS_TAC ‘channel22’ THEN
 Q.EXISTS_TAC ‘channel32’ THEN
 Q.EXISTS_TAC ‘bd_reply’ THEN
 PAXTAC THEN
 CONJS_TAC THEN
  STAC
]
QED

Theorem EXTERNAL_FETCHING_BD_UPDATE_QS_ABSTRACT_APPEND_BDS_TO_UPDATE_PRESERVE_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width,
                            'internal_state_type, 'tag_width) device_characteristics_type)
 bd_ras_was_update bd_ras_was concrete_bds1 concrete_bds2 channel_id memory internal_state1
 internal_state2 operation read_reply channel22 channel32 channel23 channel33 verification.
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  EXTERNAL_FETCH_BD_REPLY operation memory internal_state1 read_reply /\
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  verification = cverification device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  bd_ras_was_update = (bd_ras_was, update) /\
  concrete_bds1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  concrete_bds2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2 /\
  (internal_state2, SOME bd_ras_was_update) = operation.fetch_bd internal_state1 (SOME read_reply) /\
  channel23 = fetching_bd_update_qs_abstract channel22 channel22.queue.bds_to_fetch /\
  channel33 = append_bds_to_update channel32 bd_ras_was /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel22 channel32 /\
  BDS_TO_FETCH_DISJOINT channel22.queue.bds_to_fetch
  ==>
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel23 channel33
Proof
INTRO_TAC THEN
PTAC abstractTheory.fetching_bd_update_qs_abstract THENL
[
 MATCH_MP_TAC boolTheory.FALSITY THEN
 MATCH_MP_TAC FETCH_BD_EMPTY_QUEUE_IMPLIES_F_LEMMA THEN
 Q.EXISTS_TAC ‘device_characteristics’ THEN
 Q.EXISTS_TAC ‘channel_id’ THEN
 Q.EXISTS_TAC ‘verification’ THEN
 Q.EXISTS_TAC ‘operation’ THEN
 Q.EXISTS_TAC ‘internal_state1’ THEN
 Q.EXISTS_TAC ‘internal_state2’ THEN
 Q.EXISTS_TAC ‘read_reply’ THEN
 Q.EXISTS_TAC ‘bd_ras_was_update’ THEN
 Q.EXISTS_TAC ‘memory’ THEN
 CONJS_TAC THEN TRY STAC THEN
 IRTAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_ABSTRACT_EQ_CONCRETE_BDS_LEMMA THEN
 STAC
 ,
 MATCH_MP_TAC FETCHED_BD_UPDATE_ACYCLIC_BSIMS_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA THEN
 Q.EXISTS_TAC ‘device_characteristics’ THEN
 Q.EXISTS_TAC ‘memory’ THEN
 Q.EXISTS_TAC ‘internal_state1’ THEN
 Q.EXISTS_TAC ‘internal_state2’ THEN
 Q.EXISTS_TAC ‘verification’ THEN
 Q.EXISTS_TAC ‘operation’ THEN
 Q.EXISTS_TAC ‘channel_id’ THEN
 Q.EXISTS_TAC ‘concrete_bds1’ THEN
 Q.EXISTS_TAC ‘channel22’ THEN
 Q.EXISTS_TAC ‘channel32’ THEN
 Q.EXISTS_TAC ‘read_reply’ THEN
 Q.EXISTS_TAC ‘q’ THEN
 Q.EXISTS_TAC ‘bd_ras_was’ THEN
 Q.EXISTS_TAC ‘t’ THEN
 CONJS_TAC THEN STAC
 ,
 MATCH_MP_TAC boolTheory.FALSITY THEN
 MATCH_MP_TAC NOT_UPDATE_BD_TO_FETCH_UPDATE_BD_FETCHED_IMPLIES_F_LEMMA THEN
 Q.EXISTS_TAC ‘device_characteristics’ THEN
 Q.EXISTS_TAC ‘channel_id’ THEN
 Q.EXISTS_TAC ‘verification’ THEN
 Q.EXISTS_TAC ‘operation’ THEN
 Q.EXISTS_TAC ‘q’ THEN
 Q.EXISTS_TAC ‘bd_ras_was’ THEN
 EXPAND_TERM_TAC "read_reply" THEN
 Q.EXISTS_TAC ‘q'’ THEN
 Q.EXISTS_TAC ‘r'’ THEN
 Q.EXISTS_TAC ‘t’ THEN
 Q.EXISTS_TAC ‘memory’ THEN
 Q.EXISTS_TAC ‘internal_state1’ THEN
 Q.EXISTS_TAC ‘internal_state2’ THEN
 IRTAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_ABSTRACT_EQ_CONCRETE_BDS_LEMMA THEN
 CONJS_TAC THEN STAC
]
QED

Theorem FETCHING_BD_FETCH_BD_ABSTRACT_CONCRETE_PRESERVES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width,
                            'internal_state_type, 'tag_width) device_characteristics_type)
 channel_id memory internal_state1 internal_state32 internal_state22 concrete_bds1
 concrete_bds2 channel22 channel32 channel23 channel33 verification operation read_reply.
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  EXTERNAL_BDS device_characteristics /\
  EXTERNAL_FETCH_BD_REPLY operation memory internal_state1 read_reply /\
  FETCHING_BD_FETCH_BD_ABSTRACT_CONCRETE
    device_characteristics channel_id verification operation 
    concrete_bds1 concrete_bds2 internal_state1 internal_state22 internal_state32
    channel22 channel32 channel23 channel33 memory read_reply /\
  BDS_TO_FETCH_DISJOINT channel22.queue.bds_to_fetch /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel22 channel32
  ==>
  internal_state32 = internal_state22 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel23 channel33
Proof
INTRO_TAC THEN
ETAC FETCHING_BD_FETCH_BD_ABSTRACT_CONCRETE THEN
PTAC abstractTheory.fetching_bd_fetch_bd_abstract THEN PTAC concreteTheory.fetching_bd_fetch_bd_concrete THENL
[
 EQ_PAIR_ASM_TAC THEN
 FITAC FETCHING_BD_UPDATE_QS_APPEND_BDS_TO_PROCESS_PRESERVE_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 FITAC EXTERNAL_FETCHING_BD_UPDATE_QS_ABSTRACT_APPEND_BDS_TO_UPDATE_PRESERVE_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ETAC proof_obligationsTheory.PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT THEN
 AIRTAC THEN
 ALL_LRTAC THEN
 QLRTAC THEN
 STAC
]
QED

Theorem ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_SOME_NONE_PENDING_FETCH_BD_REPLIES_IMPLIES_F_LEMMA:
!concrete_bds1 channel21 channel31 read_reply.
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel21 channel31 /\
  SOME read_reply = channel21.pending_accesses.replies.fetching_bd /\
  NONE = channel31.pending_accesses.replies.fetching_bd
  ==>
  F
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
ALL_LRTAC THEN
RLTAC THEN
HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
QED

Theorem ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_NONE_SOME_PENDING_FETCH_BD_REPLIES_IMPLIES_F_LEMMA:
!concrete_bds1 channel21 channel31 read_reply.
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel21 channel31 /\
  NONE = channel21.pending_accesses.replies.fetching_bd /\
  SOME read_reply = channel31.pending_accesses.replies.fetching_bd
  ==>
  F
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
ALL_LRTAC THEN
RLTAC THEN
HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
QED

Theorem FETCH_BD_ADDRESSES_EQ_HEAD_BD_RAS_LEMMA:
!device_characteristics verification operation channel memory
 internal_state fetch_bd_read_addresses fetch_bd_addresses tag channel_id.
  PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS device_characteristics /\
  PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  verification = (cverification device_characteristics channel_id) /\
  operation = (coperation device_characteristics channel_id) /\
  channel.queue.bds_to_fetch = verification.bds_to_fetch memory internal_state /\
  operation.fetch_bd_addresses internal_state = (fetch_bd_addresses, tag) /\
  fetch_bd_read_addresses = bd_read_addresses channel.queue.bds_to_fetch fetch_bd_addresses
  ==>
  fetch_bd_read_addresses = fetch_bd_addresses
Proof
INTRO_TAC THEN
PTAC bd_queuesTheory.bd_read_addresses THENL
[
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ THEN
 AIRTAC THEN
 STAC
 ,
 RLTAC THEN
 LRTAC THEN
 LRTAC THEN
 LRTAC THEN
 LRTAC THEN
 LRTAC THEN
 LRTAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS THEN
 AIRTAC THEN
 PTAC listsTheory.LIST1_IN_LIST2 THEN
 REWRITE_TAC [listTheory.FILTER_EQ_ID] THEN
 STAC
]
QED

Theorem FETCHING_BD_SET_REQUEST_PRESERVES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA:
!concrete_bds channel21 channel31 channel22 channel32 fetch_bd_addresses tag.
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds channel21 channel31 /\
  channel22 = fetching_bd_set_request channel21 fetch_bd_addresses tag /\
  channel32 = fetching_bd_set_request channel31 fetch_bd_addresses tag
  ==>
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds channel22 channel32
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
REPEAT (PTAC operationsTheory.fetching_bd_set_request) THEN
LRTAC THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem ISSUING_BD_READ_MEMORY_REQUEST_PRESERVES_INTERNAL_STATE_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA:
!device_characteristics channel_id verification operation concrete_bds1 concrete_bds2 channel21 channel31 channel22
 channel32 memory internal_state1 internal_state22 internal_state32
 fetch_bd_read_addresses fetch_bd_addresses tag.
  PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS device_characteristics /\
  PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  verification = (cverification device_characteristics channel_id) /\
  operation = (coperation device_characteristics channel_id) /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel21 channel31 /\
  concrete_bds1 = verification.bds_to_fetch memory internal_state1 /\
  concrete_bds2 = verification.bds_to_fetch memory internal_state32 /\
  fetch_bd_read_addresses = bd_read_addresses channel21.queue.bds_to_fetch fetch_bd_addresses /\
  operation.fetch_bd_addresses internal_state1 = (fetch_bd_addresses,tag) /\
  (internal_state22, channel22) = (internal_state1, fetching_bd_set_request channel21 fetch_bd_read_addresses tag) /\
  (internal_state32, channel32) = (internal_state1, fetching_bd_set_request channel31 fetch_bd_addresses tag)
  ==>
  internal_state32 = internal_state22 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel22 channel32
Proof
INTRO_TAC THEN
EQ_PAIR_ASM_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
FITAC FETCH_BD_ADDRESSES_EQ_HEAD_BD_RAS_LEMMA THEN
LRTAC THEN
IRTAC (REWRITE_RULE [stateTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ] 
 FETCHING_BD_SET_REQUEST_PRESERVES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA
) THEN
STAC
QED

Theorem NO_BDS_TO_FETCH_FETCH_BD_IMPLIES_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id internal_state1 internal_state2 bd memory
 operation verification u.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  verification = cverification device_characteristics channel_id /\
  operation.fetch_bd internal_state1 NONE = (internal_state2, SOME (bd, u))
  ==>
  ?bd bds. bd::bds = verification.bds_to_fetch memory internal_state1
Proof
INTRO_TAC THEN
CCONTR_TAC THEN
IRTAC lists_lemmasTheory.NO_HD_TL_IMPLIES_EMPTY_LEMMA THEN
PTAC PROOF_OBLIGATION_NO_BDS_TO_FETCH THEN
AIRTAC THEN
RLTAC THEN
QLRTAC THEN
EQ_PAIR_ASM_TAC THEN
HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_NONE_SOME
QED

Theorem FETCHED_BD_IMPLIES_BDS_TO_FETCH_NOT_EMPTY_LEMMA:
!device_characteristics channel_id internal_state1 internal_state2 bd memory
 operation verification.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  verification = cverification device_characteristics channel_id /\
  operation.fetch_bd internal_state1 NONE = (internal_state2, SOME bd)
  ==>
  verification.bds_to_fetch memory internal_state1 <> []
Proof
INTRO_TAC THEN
CCONTR_TAC THEN
ETAC boolTheory.NOT_CLAUSES THEN
IRTAC NO_BDS_TO_FETCH_FETCH_BD_IMPLIES_BDS_TO_FETCH_LEMMA THEN
PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (SPEC “memory : 'e memory_type” thm)) THEN
LRTAC THEN
AXTAC THEN
HYP_CONTR_NEQ_LEMMA_TAC listTheory.NOT_CONS_NIL
QED

Theorem FETCHED_BD_IS_FIRST_INTERNAL_LEMMA:
!device_characteristics operation verification bd u internal_state1
 internal_state2 (memory : 'e memory_type) channel_id.
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  INTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  verification = cverification device_characteristics channel_id /\
  operation.fetch_bd internal_state1 NONE = (internal_state2, SOME (bd, u))
  ==>
  ?bds. (bd, u)::bds = verification.bds_to_fetch memory internal_state1
Proof
INTRO_TAC THEN
ITAC NO_BDS_TO_FETCH_FETCH_BD_IMPLIES_BDS_TO_FETCH_LEMMA THEN
PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (SPEC “memory : 'e memory_type” thm)) THEN
PTAC PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL THEN
AXTAC THEN
AIRTAC THEN
FAITAC THEN
LRTAC THEN
LRTAC THEN
RLTAC THEN
EXISTS_EQ_TAC
QED

(*
Theorem FETCHING_CONCRETE_CYCLIC_BD_LEMMA:
!device_characteristics operation verification bd u internal_state1 internal_state2 memory channel_id bds.
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  INTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  verification = cverification device_characteristics channel_id /\
  operation.fetch_bd internal_state1 NONE = (internal_state2, SOME (bd, u)) /\
  (bd, u, cyclic)::bds = verification.bds_to_fetch memory internal_state1
  ==>
  verification.bds_to_fetch memory internal_state2 = bds ++ [(bd, u, cyclic)]
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT THEN
AIRTAC THEN
AIRTAC THEN
STAC
QED
*)

Theorem FETCHING_CONCRETE_ACYCLIC_BD_LEMMA:
!device_characteristics operation verification bd u internal_state1
 internal_state2 memory channel_id bds.
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  INTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  verification = cverification device_characteristics channel_id /\
  operation.fetch_bd internal_state1 NONE = (internal_state2, SOME (bd, u)) /\
  (bd, u)::bds = verification.bds_to_fetch memory internal_state1 /\
  BDS_TO_FETCH_DISJOINT ((bd, u)::bds)
  ==>
  verification.bds_to_fetch memory internal_state2 = bds
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT THEN
AIRTAC THEN
AIRTAC THEN
STAC
QED

Theorem FETCHING_BD_UPDATE_QS_ABSTRACT_NO_UPDATE_ACYCLIC_QUEUES_EQ_LEMMA:
!channel1 channel2 bd bds.
  channel2 = fetching_bd_update_qs_abstract channel1 ((bd, no_update)::bds)
  ==>
  channel2.queue.bds_to_fetch = bds /\
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process ++ [bd] /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back /\
  channel2.pending_accesses = channel1.pending_accesses
Proof
INTRO_TAC THEN
PTAC abstractTheory.fetching_bd_update_qs_abstract THEN
PTAC operationsTheory.update_channel_qs THEN
PTAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
PTAC operationsTheory.update_q THEN
PTAC operationsTheory.update_q THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem FETCHING_BD_UPDATE_QS_ABSTRACT_UPDATE_ACYCLIC_QUEUES_EQ_LEMMA:
!channel1 channel2 bd bds.
  channel2 = fetching_bd_update_qs_abstract channel1 ((bd, update)::bds)
  ==>
  channel2.queue.bds_to_fetch = bds /\
  channel2.queue.bds_to_update = channel1.queue.bds_to_update ++ [bd] /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back /\
  channel2.pending_accesses = channel1.pending_accesses
Proof
INTRO_TAC THEN
PTAC abstractTheory.fetching_bd_update_qs_abstract THEN
PTAC operationsTheory.update_channel_qs THEN
PTAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
PTAC operationsTheory.update_q THEN
PTAC operationsTheory.update_q THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

(*
Theorem FETCHING_BD_UPDATE_QS_ABSTRACT_NO_UPDATE_CYCLIC_QUEUES_EQ_LEMMA:
!channel1 channel2 bd bds.
  channel2 = fetching_bd_update_qs_abstract channel1 ((bd, no_update, cyclic)::bds)
  ==>
  channel2.queue.bds_to_fetch = bds ++ [(bd, no_update, cyclic)] /\
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process ++ [bd] /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back /\
  channel2.pending_accesses = channel1.pending_accesses
Proof
INTRO_TAC THEN
PTAC abstractTheory.fetching_bd_update_qs_abstract THEN
PTAC operationsTheory.update_channel_qs THEN
PTAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
PTAC operationsTheory.update_q THEN
PTAC operationsTheory.update_q THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem FETCHING_BD_UPDATE_QS_ABSTRACT_UPDATE_CYCLIC_QUEUES_EQ_LEMMA:
!channel1 channel2 bd bds.
  channel2 = fetching_bd_update_qs_abstract channel1 ((bd, update, cyclic)::bds)
  ==>
  channel2.queue.bds_to_fetch = bds ++ [(bd, update, cyclic)] /\
  channel2.queue.bds_to_update = channel1.queue.bds_to_update ++ [bd] /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back /\
  channel2.pending_accesses = channel1.pending_accesses
Proof
INTRO_TAC THEN
PTAC abstractTheory.fetching_bd_update_qs_abstract THEN
PTAC operationsTheory.update_channel_qs THEN
PTAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
PTAC operationsTheory.update_q THEN
PTAC operationsTheory.update_q THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED
*)

Theorem APPEND_BDS_TO_UPDATE_APPENDS_BDS_TO_UPDATE_LEMMA:
!channel1 channel2 bd.
  channel2 = append_bds_to_update channel1 bd
  ==>
  channel2.queue.bds_to_update = channel1.queue.bds_to_update ++ [bd] /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back /\
  channel2.pending_accesses = channel1.pending_accesses
Proof
INTRO_TAC THEN
PTAC operationsTheory.append_bds_to_update THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem APPEND_BDS_TO_PROCESS_OPERATION_LEMMA:
!channel1 channel2 bd.
  channel2 = append_bds_to_process channel1 bd
  ==>
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process ++ [bd] /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back /\
  channel2.pending_accesses = channel1.pending_accesses
Proof
INTRO_TAC THEN
PTAC operationsTheory.append_bds_to_process THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem UPDATE_CHANNEL_QS_FETCH_PROCESS_OPERATION_LEMMA:
!channel1 channel2 t q.
  channel2 = update_channel_qs channel1 [fetch_queue t; process_queue (channel1.queue.bds_to_process ++ [q])]
  ==>
  channel2.queue.bds_to_fetch = t /\
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process ++ [q] /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back /\
  channel2.pending_accesses = channel1.pending_accesses
Proof
INTRO_TAC THEN
PTAC operationsTheory.update_channel_qs THEN
PTAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem UPDATE_CHANNEL_QS_FETCH_APPEND_BDS_TO_PROCESS_PRESERVES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA:
!channel21 channel31 channel22 channel32 concrete_bds bd bds.
  channel22 = update_channel_qs channel21 [fetch_queue bds; process_queue (channel21.queue.bds_to_process ++ [bd])] /\
  channel32 = append_bds_to_process channel31 bd /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds channel21 channel31
  ==>
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ bds channel22 channel32
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
IRTAC APPEND_BDS_TO_PROCESS_OPERATION_LEMMA THEN
IRTAC UPDATE_CHANNEL_QS_FETCH_PROCESS_OPERATION_LEMMA THEN
STAC
QED

Theorem APPEND_BDS_TO_UPDATE_OPERATION_LEMMA:
!channel1 channel2 bd.
  channel2 = append_bds_to_update channel1 bd
  ==>
  channel2.queue.bds_to_update = channel1.queue.bds_to_update ++ [bd] /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back /\
  channel2.pending_accesses = channel1.pending_accesses
Proof
INTRO_TAC THEN
PTAC operationsTheory.append_bds_to_update THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem UPDATE_CHANNEL_QS_FETCH_UPDATE_OPERATION_LEMMA:
!channel1 channel2 t q.
  channel2 = update_channel_qs channel1 [fetch_queue t; update_queue (channel1.queue.bds_to_update ++ [q])]
  ==>
  channel2.queue.bds_to_fetch = t /\
  channel2.queue.bds_to_update = channel1.queue.bds_to_update ++ [q] /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back /\
  channel2.pending_accesses = channel1.pending_accesses
Proof
INTRO_TAC THEN
PTAC operationsTheory.update_channel_qs THEN
PTAC operationsTheory.update_qs THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.update_q THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem UPDATE_CHANNEL_QS_FETCH_APPEND_BDS_TO_UPDATE_PRESERVES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA:
!channel21 channel31 channel22 channel32 concrete_bds bd bds.
  channel22 = update_channel_qs channel21 [fetch_queue bds; update_queue (channel21.queue.bds_to_update ++ [bd])] /\
  channel32 = append_bds_to_update channel31 bd /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds channel21 channel31
  ==>
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ bds channel22 channel32
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
IRTAC APPEND_BDS_TO_UPDATE_OPERATION_LEMMA THEN
IRTAC UPDATE_CHANNEL_QS_FETCH_UPDATE_OPERATION_LEMMA THEN
STAC
QED

Theorem FETCHING_BD_UPDATE_QS_ABSTRACT_APPEND_BDS_TO_PROCESS_PRESERVE_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA:
!device_characteristics operation channel_id (memory : 'e memory_type) internal_state1 internal_state2 concrete_bds1 concrete_bds2 q channel21 channel31 channel22 channel32.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INTERNAL_BDS device_characteristics /\
  operation = coperation device_characteristics channel_id /\
  concrete_bds1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  concrete_bds2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2 /\
  (internal_state2, SOME (q, no_update)) = operation.fetch_bd internal_state1 NONE /\
  channel22 = fetching_bd_update_qs_abstract channel21 channel21.queue.bds_to_fetch /\
  channel32 = append_bds_to_process channel31 q /\
  BDS_TO_FETCH_DISJOINT channel21.queue.bds_to_fetch /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel21 channel31
  ==>
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel22 channel32
Proof
INTRO_TAC THEN
PTAC abstractTheory.fetching_bd_update_qs_abstract THENL
[
 IRTAC FETCHED_BD_IMPLIES_BDS_TO_FETCH_NOT_EMPTY_LEMMA THEN
 PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (SPEC “memory : 'e memory_type” thm)) THEN
 IRTAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_ABSTRACT_EQ_CONCRETE_BDS_LEMMA THEN
 LRTAC THEN LRTAC THEN RLTAC THEN
 CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
 ,
 PAT_X_ASSUM “r = update” (fn thm => ASSUME_TAC thm THEN LRTAC THEN LRTAC) THEN
 IRTAC FETCHED_BD_IS_FIRST_INTERNAL_LEMMA THEN
 PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (SPEC “memory : 'e memory_type” thm)) THEN
 AXTAC THEN
 IRTAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_ABSTRACT_EQ_CONCRETE_BDS_LEMMA THEN
 RLTAC THEN
 LRTAC THEN
 LRTAC THEN
 ETAC listTheory.CONS_11 THEN
 EQ_PAIR_ASM_TAC THEN
 HYP_CONTR_NEQ_LEMMA_TAC stateTheory.bd_update_type_distinct
 ,
 PAT_X_ASSUM “r = no_update” (fn thm => ASSUME_TAC thm THEN LRTAC THEN LRTAC) THEN
 ITAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_ABSTRACT_EQ_CONCRETE_BDS_LEMMA THEN
 RLTAC THEN
 PTAC PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT THEN
 AITAC THEN
 AITAC THEN
 LRTAC THEN
 MATCH_MP_TAC UPDATE_CHANNEL_QS_FETCH_APPEND_BDS_TO_PROCESS_PRESERVES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA THEN
 LRTAC THEN
 PAXTAC THEN
 CONJS_TAC THEN TRY STAC THEN
 IRTAC FETCHED_BD_IS_FIRST_INTERNAL_LEMMA THEN
 PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (SPEC “memory : 'e memory_type” thm)) THEN
 AXTAC THEN
 RLTAC THEN
 LRTAC THEN
 ETAC listTheory.CONS_11 THEN
 EQ_PAIR_ASM_TAC THEN
 STAC
(*
 IRTAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_ABSTRACT_EQ_CONCRETE_BDS_LEMMA THEN
 FAITAC THEN
 IRTAC FETCHED_BD_IS_FIRST_INTERNAL_LEMMA THEN
 PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (SPEC “memory : 'e memory_type” thm)) THEN
 AXTAC THEN
 RLTAC THEN
 ETAC listTheory.CONS_11 THEN
 LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 RLTAC THEN
 FIRTAC UPDATE_CHANNEL_QS_FETCH_APPEND_BDS_TO_PROCESS_PRESERVES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA THEN
 STAC
*)
]
QED

Theorem INTERNAL_FETCHING_BD_UPDATE_QS_ABSTRACT_APPEND_BDS_TO_UPDATE_PRESERVE_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA:
!device_characteristics operation verification channel_id (memory : 'e memory_type) internal_state1 internal_state2 concrete_bds1 concrete_bds2 q channel21 channel31 channel22 channel32.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INTERNAL_BDS device_characteristics /\
  operation = coperation device_characteristics channel_id /\
  verification = cverification device_characteristics channel_id /\
  concrete_bds1 = verification.bds_to_fetch memory internal_state1 /\
  concrete_bds2 = verification.bds_to_fetch memory internal_state2 /\
  (internal_state2, SOME (q, update)) = operation.fetch_bd internal_state1 NONE /\
  channel22 = fetching_bd_update_qs_abstract channel21 channel21.queue.bds_to_fetch /\
  channel32 = append_bds_to_update channel31 q /\
  BDS_TO_FETCH_DISJOINT channel21.queue.bds_to_fetch /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel21 channel31
  ==>
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel22 channel32
Proof
INTRO_TAC THEN
PTAC abstractTheory.fetching_bd_update_qs_abstract THENL
[
 IRTAC FETCHED_BD_IMPLIES_BDS_TO_FETCH_NOT_EMPTY_LEMMA THEN
 PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (SPEC “memory : 'e memory_type” thm)) THEN
 IRTAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_ABSTRACT_EQ_CONCRETE_BDS_LEMMA THEN
 LRTAC THEN LRTAC THEN RLTAC THEN
 CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
 ,
 MATCH_MP_TAC UPDATE_CHANNEL_QS_FETCH_APPEND_BDS_TO_UPDATE_PRESERVES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA THEN
 PAT_X_ASSUM “r = update” (fn thm => ASSUME_TAC thm THEN LRTAC THEN LRTAC) THEN
 PAXTAC THEN
 CONJS_TAC THEN TRY STAC THENL
 [
  ITAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_ABSTRACT_EQ_CONCRETE_BDS_LEMMA THEN
  RLTAC THEN
  PTAC PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT THEN
  LRTAC THEN
  AITAC THEN
  AITAC THEN
  PAT_X_ASSUM “verification = cverification device_characteristics channel_id” (fn thm => ASSUME_TAC thm THEN RLTAC) THEN
  LRTAC THEN
  LRTAC THEN
  STAC
  ,
  ITAC FETCHED_BD_IS_FIRST_INTERNAL_LEMMA THEN
  PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (SPEC “memory : 'e memory_type” thm) THEN AXTAC) THEN
  ITAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_ABSTRACT_EQ_CONCRETE_BDS_LEMMA THEN
  RLTAC THEN
  RLTAC THEN
  RLTAC THEN
  ETAC listTheory.CONS_11 THEN
  EQ_PAIR_ASM_TAC THEN
  STAC
 ]
(*
 LRTAC THEN LRTAC THEN LRTAC THEN
 ITAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_ABSTRACT_EQ_CONCRETE_BDS_LEMMA THEN
 PTAC PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT THEN
 AITAC THEN
 LRTAC THEN
 FAITAC THEN
 ITAC FETCHED_BD_IS_FIRST_INTERNAL_LEMMA THEN
 PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (SPEC “memory : 'e memory_type” thm)) THEN
 AXTAC THEN
 RLTAC THEN LRTAC THEN
 ETAC listTheory.CONS_11 THEN
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN RLTAC THEN
 RLTAC THEN FIRTAC UPDATE_CHANNEL_QS_FETCH_APPEND_BDS_TO_UPDATE_PRESERVES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA THEN
 STAC
*)
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN
 IRTAC FETCHED_BD_IS_FIRST_INTERNAL_LEMMA THEN
 PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (SPEC “memory : 'e memory_type” thm)) THEN
 AXTAC THEN
 IRTAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_ABSTRACT_EQ_CONCRETE_BDS_LEMMA THEN
 RLTAC THEN RLTAC THEN RLTAC THEN
 ETAC listTheory.CONS_11 THEN
 EQ_PAIR_ASM_TAC THEN
 HYP_CONTR_NEQ_LEMMA_TAC stateTheory.bd_update_type_distinct
]
QED

Theorem FETCHING_BD_ABSTRACT_CONCRETE_BSIMS_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA:
!device_characteristics channel_id memory concrete_bds1 concrete_bds2
 internal_state1 internal_state22 internal_state32
 channel21 channel31 channel22 channel32 operation.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INTERNAL_BDS device_characteristics /\
  operation = coperation device_characteristics channel_id /\
  concrete_bds1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  concrete_bds2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state32 /\
  (internal_state22, channel22) = fetching_bd_fetch_bd_abstract operation.fetch_bd internal_state1 channel21 NONE /\
  (internal_state32, channel32) = fetching_bd_fetch_bd_concrete operation.fetch_bd internal_state1 channel31 NONE /\
  BDS_TO_FETCH_DISJOINT channel21.queue.bds_to_fetch /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel21 channel31
  ==>
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel22 channel32
Proof
INTRO_TAC THEN
PTAC abstractTheory.fetching_bd_fetch_bd_abstract THEN PTAC concreteTheory.fetching_bd_fetch_bd_concrete THENL
[
 EQ_PAIR_ASM_TAC THEN
 ALL_LRTAC THEN
 IRTAC FETCHING_BD_UPDATE_QS_ABSTRACT_APPEND_BDS_TO_PROCESS_PRESERVE_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ALL_LRTAC THEN
 IRTAC INTERNAL_FETCHING_BD_UPDATE_QS_ABSTRACT_APPEND_BDS_TO_UPDATE_PRESERVE_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 LRTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN
 PTAC PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT THEN
 AIRTAC THEN
 ALL_LRTAC THEN
 QLRTAC THEN
 STAC
]
QED

Theorem ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_BD_READ_ADDRESSES_EQ_LEMMA:
!fetch_bd_read_addresses2 channel21 fetch_bd_addresses fetch_bd_read_addresses3 concrete_bds2 channel31.
  fetch_bd_read_addresses2 = bd_read_addresses channel21.queue.bds_to_fetch fetch_bd_addresses /\
  fetch_bd_read_addresses3 = bd_read_addresses concrete_bds2 fetch_bd_addresses /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel21 channel31
  ==>
  fetch_bd_read_addresses2 = fetch_bd_read_addresses3
Proof
INTRO_TAC THEN
IRTAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_ABSTRACT_EQ_CONCRETE_BDS_LEMMA THEN
LRTAC THEN
STAC
QED

Theorem NONE_NOT_NONE_FETCHING_BD_REPLIES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_F_LEMMA:
!channel2 channel3 concrete_bds.
  IS_NONE channel2.pending_accesses.replies.fetching_bd /\
  ~IS_NONE channel3.pending_accesses.replies.fetching_bd /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds channel2 channel3
  ==>
  F
Proof
INTRO_TAC THEN
IRTAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_PENDING_ACCESSES_LEMMA THEN
RLTAC THEN
PTAC optionTheory.IS_NONE_DEF THEN PTAC optionTheory.IS_NONE_DEF THENL
[
 ETAC boolTheory.NOT_CLAUSES THEN STAC
 ,
 STAC
]
QED

Theorem NOT_NONE_NONE_FETCHING_BD_REPLIES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_F_LEMMA:
!channel2 channel3 concrete_bds.
  ~IS_NONE channel2.pending_accesses.replies.fetching_bd /\
  IS_NONE channel3.pending_accesses.replies.fetching_bd /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds channel2 channel3
  ==>
  F
Proof
INTRO_TAC THEN
IRTAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_PENDING_ACCESSES_LEMMA THEN
RLTAC THEN
PTAC optionTheory.IS_NONE_DEF THEN PTAC optionTheory.IS_NONE_DEF THENL
[
 ETAC boolTheory.NOT_CLAUSES THEN STAC
 ,
 SOLVE_F_ASM_TAC
]
QED

Theorem NOT_IS_NONE_IMPLIES_EXISTS_SOME_LEMMA:
!channel.
  ~IS_NONE channel.pending_accesses.replies.fetching_bd
  ==>
  ?read_reply.
    channel.pending_accesses.replies.fetching_bd = SOME read_reply
Proof
INTRO_TAC THEN
PTAC optionTheory.IS_NONE_DEF THENL
[
 ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC
 ,
 LRTAC THEN EXISTS_EQ_TAC
]
QED

Theorem FETCHING_BD_CLEAR_REPLY_PRESERVES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA:
!channel21 channel31 channel22 channel32 concrete_bds.
  channel22 = fetching_bd_clear_reply channel21 /\
  channel32 = fetching_bd_clear_reply channel31 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds channel21 channel31
  ==>
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds channel22 channel32
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
ETAC operationsTheory.fetching_bd_clear_reply THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_SAME_READ_REPLY_LEMMA:
!channel2 channel3 read_reply2 read_reply3 concrete_bds channel2 channel3.
  channel2.pending_accesses.replies.fetching_bd = SOME read_reply2 /\
  channel3.pending_accesses.replies.fetching_bd = SOME read_reply3 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds channel2 channel3
  ==>
  read_reply2 = read_reply3
Proof
INTRO_TAC THEN
IRTAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_PENDING_ACCESSES_LEMMA THEN
RLTAC THEN
LRTAC THEN
ETAC optionTheory.SOME_11 THEN
STAC
QED

Theorem NOT_NONE_FETCHING_BD_REPLY_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_SAME_REPLY_LEMMA:
!channel2 channel3 concrete_bds.
  ~IS_NONE channel2.pending_accesses.replies.fetching_bd /\
  ~IS_NONE channel3.pending_accesses.replies.fetching_bd /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds channel2 channel3
  ==>
  ?reply.
    channel2.pending_accesses.replies.fetching_bd = SOME reply /\
    channel3.pending_accesses.replies.fetching_bd = SOME reply
Proof
INTRO_TAC THEN
PTAC optionTheory.IS_NONE_DEF THEN PTAC optionTheory.IS_NONE_DEF THENL
[
 ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC
 ,
 ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC
 ,
 ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC
 ,
 IRTAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_PENDING_ACCESSES_LEMMA THEN
 RLTAC THEN
 LRTAC THEN
 EXISTS_EQ_TAC
]
QED

Theorem FETCHING_BD_CLEAR_REPLY_PRESERVES_BD_QUEUES_LEMMA:
!channel1 channel2.
  channel2 = fetching_bd_clear_reply channel1
  ==>
  channel2.queue.bds_to_fetch = channel1.queue.bds_to_fetch /\
  channel2.queue.bds_to_update = channel1.queue.bds_to_update /\
  channel2.queue.bds_to_process = channel1.queue.bds_to_process /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
LRTAC THEN
ETAC operationsTheory.fetching_bd_clear_reply THEN
RECORD_TAC THEN
STAC
QED

Theorem FETCHING_BD_L2_L3_BSIMS_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA:
!device_characteristics channel_id memory verification operation concrete_bds1 concrete_bds2 
 internal_state1 internal_state22 internal_state32 channel21 channel31 channel22 channel32.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  EXTERNAL_BDS_FETCH_REPLY device_characteristics channel_id memory channel31 internal_state1 /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  verification = cverification device_characteristics channel_id /\
  operation = coperation device_characteristics channel_id /\
  concrete_bds1 = verification.bds_to_fetch memory internal_state1 /\
  concrete_bds2 = verification.bds_to_fetch memory internal_state32 /\
  (internal_state22, channel22) = fetching_bd_l2 device_characteristics channel_id        internal_state1 channel21 /\
  (internal_state32, channel32) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel31 /\
  BDS_TO_FETCH_DISJOINT channel21.queue.bds_to_fetch /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel21 channel31
  ==>
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel22 channel32
Proof
INTRO_TAC THEN
PTAC l2Theory.fetching_bd_l2 THEN PTAC l3Theory.fetching_bd_l3 THENL
[
 MATCH_MP_TAC FETCHING_BD_ABSTRACT_CONCRETE_BSIMS_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA THEN
 PAXTAC THEN
 Q.EXISTS_TAC ‘memory’ THEN
 CONJS_TAC THEN TRY STAC
 ,
 ASM_RL_RW_OTHERS_KEEP_TAC THEN
 ASM_RL_RW_OTHERS_KEEP_TAC THEN
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN RLTAC THEN RLTAC THEN
 FITAC ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_BD_READ_ADDRESSES_EQ_LEMMA THEN
 RLTAC THEN
 IRTAC FETCHING_BD_SET_REQUEST_PRESERVES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA THEN
 STAC
 ,
 IRTAC NONE_NOT_NONE_FETCHING_BD_REPLIES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_F_LEMMA THEN SOLVE_F_ASM_TAC
 ,
 IRTAC NOT_NONE_NONE_FETCHING_BD_REPLIES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_F_LEMMA THEN SOLVE_F_ASM_TAC
 ,
 IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
 FITAC NOT_NONE_FETCHING_BD_REPLY_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_SAME_REPLY_LEMMA THEN
 AXTAC THEN
 WEAKEN_TAC is_neg THEN
 WEAKEN_TAC is_neg THEN
 PTAC EXTERNAL_BDS_FETCH_REPLY THEN
 AITAC THEN
 LRTAC THEN LRTAC THEN LRTAC THEN LRTAC THEN
 PAT_X_ASSUM “channel = fetching_bd_clear_reply channel21” (fn thm => ASSUME_TAC thm) THEN
 ITAC FETCHING_BD_CLEAR_REPLY_PRESERVES_BD_QUEUES_LEMMA THEN
 FIRTAC FETCHING_BD_CLEAR_REPLY_PRESERVES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA THEN
 FITAC ((GEN_ALL o #2 o EQ_IMP_RULE o SPEC_ALL) FETCHING_BD_FETCH_BD_ABSTRACT_CONCRETE) THEN
 ITAC FETCHING_BD_FETCH_BD_ABSTRACT_CONCRETE_PRESERVES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA THEN
 STAC
]
QED

Theorem FETCHING_BD_L2_L3_BSIMS_INTERNAL_STATE_LEMMA:
!device_characteristics channel_id memory internal_state1 channel21 channel31
 channel22 channel32 internal_state22 internal_state32
 verification concrete_bds1.
  verification = cverification device_characteristics channel_id /\
  concrete_bds1 = verification.bds_to_fetch memory internal_state1 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel21 channel31 /\
  (internal_state22, channel22) = fetching_bd_l2 device_characteristics channel_id        internal_state1 channel21 /\
  (internal_state32, channel32) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel31
  ==>
  internal_state22 = internal_state32
Proof
INTRO_TAC THEN
PTAC l2Theory.fetching_bd_l2 THEN PTAC l3Theory.fetching_bd_l3 THENL
[
 PTAC abstractTheory.fetching_bd_fetch_bd_abstract THEN PTAC concreteTheory.fetching_bd_fetch_bd_concrete THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 IRTAC NONE_NOT_NONE_FETCHING_BD_REPLIES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_F_LEMMA THEN SOLVE_F_ASM_TAC
 ,
 IRTAC NOT_NONE_NONE_FETCHING_BD_REPLIES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_F_LEMMA THEN SOLVE_F_ASM_TAC
 ,
 FITAC NOT_NONE_FETCHING_BD_REPLY_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_SAME_REPLY_LEMMA THEN
 AXTAC THEN
 LRTAC THEN
 LRTAC THEN
 LRTAC THEN
 LRTAC THEN
 REPEAT (WEAKEN_TAC is_neg) THEN
 PTAC abstractTheory.fetching_bd_fetch_bd_abstract THEN PTAC concreteTheory.fetching_bd_fetch_bd_concrete THEN EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem FETCH_BD_NOT_AFFECTING_OTHER_BDS_TO_FETCH_LEMMA:
!device_characteristics internal_state1 internal_state2 fetch_result reply channel_id memory.
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, fetch_result) = (coperation device_characteristics channel_id).fetch_bd internal_state1 reply
  ==>
  OTHER_BDS_TO_FETCH_EQ device_characteristics channel_id memory internal_state1 internal_state2
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE THEN
PTAC stateTheory.OTHER_BDS_TO_FETCH_EQ THEN
AIRTAC THEN
STAC
(*
STAC
PAT_X_ASSUM “!x.P” (fn thm => MATCH_MP_TAC thm) THEN
INST_EXISTS_NAMES_TAC ["channel_id"] THEN
PAXTAC THEN
ASM_REWRITE_TAC [] THEN
CCONTR_TAC THEN
ETAC boolTheory.NOT_CLAUSES THEN
LRTAC THEN
CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
*)
QED

Theorem OTHER_BDS_TO_FETCH_EQ_IDENTITY_LEMMA:
!device_characteristics channel_id memory internal_state internal_state.
  OTHER_BDS_TO_FETCH_EQ device_characteristics channel_id memory internal_state internal_state
Proof
REWRITE_TAC [stateTheory.OTHER_BDS_TO_FETCH_EQ]
QED

Theorem FETCHING_BD_L3_PRESERVES_OTHER_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1
  ==>
  OTHER_BDS_TO_FETCH_EQ device_characteristics channel_id memory internal_state1 internal_state2
Proof
INTRO_TAC THEN
PTAC l3Theory.fetching_bd_l3 THENL
[
 PTAC concreteTheory.fetching_bd_fetch_bd_concrete THEN
 EQ_PAIR_ASM_TAC THEN RLTAC THEN IRTAC FETCH_BD_NOT_AFFECTING_OTHER_BDS_TO_FETCH_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 REWRITE_TAC [OTHER_BDS_TO_FETCH_EQ_IDENTITY_LEMMA]
 ,
 PTAC concreteTheory.fetching_bd_fetch_bd_concrete THEN
 EQ_PAIR_ASM_TAC THEN RLTAC THEN IRTAC FETCH_BD_NOT_AFFECTING_OTHER_BDS_TO_FETCH_LEMMA THEN STAC
]
QED

Theorem FETCHING_BD_L2_L3_BSIMS_INTERNAL_STATE_CHANNEL_OTHER_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id memory concrete_bds1 concrete_bds2
 channel21 channel31 channel22 channel32
 internal_state1 internal_state22 internal_state32.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics /\
  EXTERNAL_BDS_FETCH_REPLY device_characteristics channel_id memory channel31 internal_state1 /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel21 channel31 /\
  BDS_TO_FETCH_DISJOINT channel21.queue.bds_to_fetch /\
  concrete_bds1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  (internal_state22, channel22) = fetching_bd_l2 device_characteristics channel_id        internal_state1 channel21 /\
  (internal_state32, channel32) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel31 /\
  concrete_bds2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state32
  ==>
  internal_state32 = internal_state22 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel22 channel32 /\
  OTHER_BDS_TO_FETCH_EQ device_characteristics channel_id memory internal_state1 internal_state32
Proof
INTRO_TAC THEN
REPEAT CONJ_TAC THENL
[
 FIRTAC FETCHING_BD_L2_L3_BSIMS_INTERNAL_STATE_LEMMA THEN STAC
 ,
 FIRTAC FETCHING_BD_L2_L3_BSIMS_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA THEN STAC
 ,
 FIRTAC FETCHING_BD_L3_PRESERVES_OTHER_BDS_TO_FETCH_LEMMA THEN STAC
]
QED

Theorem FETCHING_BD_IMPLIES_NON_EMPTY_BDS_TO_FETCH_LEMMA:
!device_characteristics internal_state1 internal_state2 some_reply fetch_result channel_id memory.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, SOME fetch_result) = (coperation device_characteristics channel_id).fetch_bd internal_state1 some_reply
  ==>
  ?bd bds.
    (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 = bd::bds
Proof
INTRO_TAC THEN
CCONTR_TAC THEN
IRTAC (ONCE_REWRITE_RULE [boolTheory.EQ_SYM_EQ] lists_lemmasTheory.NO_HD_TL_IMPLIES_EMPTY_LEMMA) THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_NO_BDS_TO_FETCH THEN
AIRTAC THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC (mk_var ("some_reply", (type_of o #1 o dest_forall o concl) thm)) thm)) THEN
LRTAC THEN
EQ_PAIR_ASM_TAC THEN
HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
QED

(*
Theorem BD_NOT_ACYCLIC_IMPLIES_CYCLIC_LEMMA:
!bd_cyclic.
  bd_cyclic <> acyclic
  ==>
  bd_cyclic = cyclic
Proof
INTRO_TAC THEN
CCONTR_TAC THEN
ASSUME_TAC (SPEC “bd_cyclic : bd_closing_cycle_type” stateTheory.bd_closing_cycle_type_nchotomy) THEN
SPLIT_ASM_DISJS_TAC THEN
 CONTR_ASMS_TAC
QED

Theorem BD_NOT_CYCLIC_IMPLIES_ACYCLIC_LEMMA:
!bd_cyclic.
  bd_cyclic <> cyclic
  ==>
  bd_cyclic = acyclic
Proof
INTRO_TAC THEN
CCONTR_TAC THEN
ASSUME_TAC (SPEC “bd_cyclic : bd_closing_cycle_type” stateTheory.bd_closing_cycle_type_nchotomy) THEN
SPLIT_ASM_DISJS_TAC THEN
 CONTR_ASMS_TAC
QED
*)

Theorem FETCH_BD_ADDRESSES_EQ_ADDRESSES_TAG_LEMMA:
!device_characteristics channel_id internal_state1.
 ?addresses tag.
   (addresses, tag) = (coperation device_characteristics channel_id).fetch_bd_addresses internal_state1
Proof
REPEAT GEN_TAC THEN
REWRITE_TAC [GSYM pairTheory.pair_CASES]
QED

Theorem FETCH_BD_IMPLIES_BDS_TO_FETCH_NOT_NULL_LEMMA:
!device_characteristics channel_id internal_state1 internal_state2 fetch_result bds_to_fetch1 memory reply_option.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, SOME fetch_result) = (coperation device_characteristics channel_id).fetch_bd internal_state1 reply_option /\
  bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1
  ==>
  ~NULL bds_to_fetch1
Proof
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_NO_BDS_TO_FETCH THEN
CCONTR_TAC THEN
ETAC boolTheory.NOT_CLAUSES THEN
ETAC listTheory.NULL_EQ THEN
AIRTAC THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC (mk_var ("reply_option", (type_of o #1 o dest_forall o concl) thm)) thm)) THEN
LRTAC THEN
EQ_PAIR_ASM_TAC THEN
IRTAC optionTheory.NOT_SOME_NONE THEN
SOLVE_F_ASM_TAC
QED

Theorem FETCH_BD_IMPLIES_BDS_TO_FETCH_CONS_LEMMA:
!device_characteristics channel_id internal_state1 internal_state2 fetch_result memory reply_option.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, SOME fetch_result) = (coperation device_characteristics channel_id).fetch_bd internal_state1 reply_option
  ==>
  ?bd update_flag bds.
    (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 = (bd, update_flag)::bds
Proof
INTRO_TAC THEN
IRTAC FETCH_BD_IMPLIES_BDS_TO_FETCH_NOT_NULL_LEMMA THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC (mk_var ("memory", (type_of o #1 o dest_forall o concl) thm)) thm)) THEN
IRTAC lists_lemmasTheory.NOT_NULL_IMPLIES_EXISTING_HD_TL_LEMMA THEN
AXTAC THEN
LRTAC THEN
EXPAND_TERM_TAC "x" THEN
EXPAND_TERM_TAC "r" THEN
EXISTS_EQ_TAC
QED

Theorem FETCH_BD_IMPLIES_BDS_TO_FETCH_EQ_FIRST_BD_TL_LEMMA:
!device_characteristics channel_id internal_state1 internal_state2 memory bd channel.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INTERNAL_BD_FETCH device_characteristics channel_id internal_state1 internal_state2 bd /\
  EXTERNAL_BD_FETCH device_characteristics memory channel_id internal_state1 channel internal_state2 bd
  ==>
  ?update_flag bds.
    (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 = (bd, update_flag)::bds
Proof
INTRO_TAC THEN
Cases_on ‘INTERNAL_BDS device_characteristics’ THENL
[
 ETAC INTERNAL_BD_FETCH THEN
 AITAC THEN
 AXTAC THEN
 ITAC FETCH_BD_IMPLIES_BDS_TO_FETCH_CONS_LEMMA THEN
 PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC (mk_var ("memory", (type_of o #1 o dest_forall o concl) thm)) thm)) THEN
 AXTAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL THEN
 AIRTAC THEN
 AITAC THEN
 NLRTAC 2 THEN
 LRTAC THEN
 EXISTS_EQ_TAC
 ,
 IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
 ETAC EXTERNAL_BD_FETCH THEN
 AITAC THEN
 AXTAC THEN
 ITAC FETCH_BD_IMPLIES_BDS_TO_FETCH_CONS_LEMMA THEN
 PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC (mk_var ("memory", (type_of o #1 o dest_forall o concl) thm)) thm)) THEN
 AXTAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL THEN
 AIRTAC THEN
 AITAC THEN
 NLRTAC 2 THEN
 LRTAC THEN
 EXISTS_EQ_TAC
]
QED

Theorem FETCHING_BD_FETCH_BD_CONCRETE_INTERNAL_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 bds_to_fetch1 bds_to_fetch2 bd.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  INTERNAL_BDS device_characteristics /\
  INTERNAL_BD_FETCH device_characteristics channel_id internal_state1 internal_state2 bd /\
  EXTERNAL_BD_FETCH device_characteristics memory channel_id internal_state1 channel1 internal_state2 bd /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = fetching_bd_fetch_bd_concrete (coperation device_characteristics channel_id).fetch_bd internal_state1 channel1 NONE /\
  BDS_TO_FETCH_DISJOINT bds_to_fetch1 /\
  bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  bds_to_fetch2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2
  ==>
  ~NULL bds_to_fetch1 /\
  (bds_to_fetch2 = TL bds_to_fetch1) /\
  (channel2.queue.bds_to_update = channel1.queue.bds_to_update ++ [FST (HD bds_to_fetch1)] \/
   channel2.queue.bds_to_update = channel1.queue.bds_to_update) /\
  (channel2.queue.bds_to_process = channel1.queue.bds_to_process ++ [FST (HD bds_to_fetch1)] \/
   channel2.queue.bds_to_process = channel1.queue.bds_to_process) /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
ITAC FETCH_BD_IMPLIES_BDS_TO_FETCH_EQ_FIRST_BD_TL_LEMMA THEN
AXTAC THEN
ETAC INTERNAL_BD_FETCH THEN
AITAC THEN
AXTAC THEN
PTAC concreteTheory.fetching_bd_fetch_bd_concrete THENL
[
 EQ_PAIR_ASM_TAC THEN
 RM_ASM_IDS_TAC THEN
 IRTAC APPEND_BDS_TO_PROCESS_OPERATION_LEMMA THEN
 CONJS_TAC THEN TRY STAC THENL
 [
  ALL_LRTAC THEN REWRITE_TAC [listTheory.NULL]
  ,
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL THEN
  AITAC THEN
  AITAC THEN
  RLTAC THEN
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT THEN
  AIRTAC THEN
  AITAC THEN
  ALL_LRTAC THEN
  REWRITE_TAC [listTheory.HD, listTheory.TL] THEN
  AIRTAC THEN
  STAC
  ,
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL THEN
  AITAC THEN
  AITAC THEN
  RLTAC THEN
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT THEN
  AIRTAC THEN
  AITAC THEN
  ALL_LRTAC THEN
  REWRITE_TAC [listTheory.HD, listTheory.TL]
 ]
 ,
 EQ_PAIR_ASM_TAC THEN
 RM_ASM_IDS_TAC THEN
 IRTAC APPEND_BDS_TO_UPDATE_OPERATION_LEMMA THEN
 CONJS_TAC THEN TRY STAC THENL
 [
  ALL_LRTAC THEN REWRITE_TAC [listTheory.NULL]
  ,
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL THEN
  AITAC THEN
  AITAC THEN
  RLTAC THEN
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT THEN
  AIRTAC THEN
  AITAC THEN
  ALL_LRTAC THEN
  REWRITE_TAC [listTheory.TL, listTheory.HD] THEN
  AIRTAC THEN
  STAC
  ,
  ALL_LRTAC THEN REWRITE_TAC [listTheory.HD]
 ]
]
QED

Theorem FETCHING_BD_FETCH_BD_CONCRETE_EXTERNAL_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel channel2 bds_to_fetch1 bds_to_fetch2 bd.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  EXTERNAL_BDS device_characteristics /\
  INTERNAL_BD_FETCH device_characteristics channel_id internal_state1 internal_state2 bd /\
  EXTERNAL_BD_FETCH device_characteristics memory channel_id internal_state1 channel1 internal_state2 bd /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channel = fetching_bd_clear_reply channel1 /\
  (internal_state2, channel2) = fetching_bd_fetch_bd_concrete (coperation device_characteristics channel_id).fetch_bd internal_state1 channel channel1.pending_accesses.replies.fetching_bd /\
  BDS_TO_FETCH_DISJOINT bds_to_fetch1 /\
  bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  bds_to_fetch2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2
  ==>
  ~NULL bds_to_fetch1 /\
  (bds_to_fetch2 = TL bds_to_fetch1) /\
  (channel2.queue.bds_to_update = channel1.queue.bds_to_update ++ [FST (HD bds_to_fetch1)] \/
   channel2.queue.bds_to_update = channel1.queue.bds_to_update) /\
  (channel2.queue.bds_to_process = channel1.queue.bds_to_process ++ [FST (HD bds_to_fetch1)] \/
   channel2.queue.bds_to_process = channel1.queue.bds_to_process) /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
ITAC FETCH_BD_IMPLIES_BDS_TO_FETCH_EQ_FIRST_BD_TL_LEMMA THEN
AXTAC THEN
ETAC EXTERNAL_BD_FETCH THEN
AITAC THEN
AXTAC THEN
IRTAC FETCHING_BD_CLEAR_REPLY_PRESERVES_BD_QUEUES_LEMMA THEN
PTAC concreteTheory.fetching_bd_fetch_bd_concrete THENL
[
 EQ_PAIR_ASM_TAC THEN
 RM_ASM_IDS_TAC THEN
 IRTAC APPEND_BDS_TO_PROCESS_OPERATION_LEMMA THEN
 CONJS_TAC THEN TRY STAC THENL
 [
  ALL_LRTAC THEN REWRITE_TAC [listTheory.NULL]
  ,
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL THEN
  AITAC THEN
  AITAC THEN
  RLTAC THEN
  LRTAC THEN
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT THEN
  AIRTAC THEN
  AITAC THEN
  ALL_LRTAC THEN
  REWRITE_TAC [listTheory.TL, listTheory.HD] THEN
  AIRTAC THEN
  STAC
  ,
  ALL_LRTAC THEN REWRITE_TAC [listTheory.HD]
 ]
 ,
 EQ_PAIR_ASM_TAC THEN
 RM_ASM_IDS_TAC THEN
 IRTAC APPEND_BDS_TO_UPDATE_OPERATION_LEMMA THEN
 CONJS_TAC THEN TRY STAC THENL
 [
  ALL_LRTAC THEN REWRITE_TAC [listTheory.NULL]
  ,
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL THEN
  AITAC THEN
  AITAC THEN
  RLTAC THEN
  PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT THEN
  AIRTAC THEN
  AITAC THEN
  ALL_LRTAC THEN
  REWRITE_TAC [listTheory.TL, listTheory.HD] THEN
  AIRTAC THEN
  STAC
  ,
  ALL_LRTAC THEN REWRITE_TAC [listTheory.HD]
 ]
]
QED

Theorem FETCHING_BD_L3_BD_SHIFTS_BD_QUEUES_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 bds_to_fetch1 bds_to_fetch2 bd.
  PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics /\
  PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INTERNAL_BD_FETCH device_characteristics channel_id internal_state1 internal_state2 bd /\
  EXTERNAL_BD_FETCH device_characteristics memory channel_id internal_state1 channel1 internal_state2 bd /\
  (internal_state2, channel2) = fetching_bd_l3 device_characteristics channel_id memory internal_state1 channel1 /\
  BDS_TO_FETCH_DISJOINT bds_to_fetch1 /\
  bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  bds_to_fetch2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2
  ==>
  ~NULL bds_to_fetch1 /\
  (bds_to_fetch2 = TL bds_to_fetch1) /\
  (channel2.queue.bds_to_update = channel1.queue.bds_to_update ++ [FST (HD bds_to_fetch1)] \/
   channel2.queue.bds_to_update = channel1.queue.bds_to_update) /\
  (channel2.queue.bds_to_process = channel1.queue.bds_to_process ++ [FST (HD bds_to_fetch1)] \/
   channel2.queue.bds_to_process = channel1.queue.bds_to_process) /\
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC l3Theory.fetching_bd_l3 THENL
[
 IRTAC FETCHING_BD_FETCH_BD_CONCRETE_INTERNAL_LEMMA THEN STAC
 ,
 IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
 ETAC EXTERNAL_BD_FETCH THEN
 AIRTAC THEN
 AXTAC THEN
 ALL_LRTAC THEN
 RLTAC THEN
 ETAC optionTheory.IS_NONE_DEF THEN
 SOLVE_F_ASM_TAC
 ,
 IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
 IRTAC FETCHING_BD_FETCH_BD_CONCRETE_EXTERNAL_LEMMA THEN
 STAC
]
QED

Theorem OTHER_BDS_TO_FETCH_EQ_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics memory channel_id channel_id' internal_state1 internal_state2.
  VALID_CHANNEL_ID device_characteristics channel_id' /\
  OTHER_BDS_TO_FETCH_EQ device_characteristics channel_id memory internal_state1 internal_state2 /\
  channel_id' <> channel_id
  ==>
  (cverification device_characteristics channel_id').bds_to_fetch memory internal_state2 =
  (cverification device_characteristics channel_id').bds_to_fetch memory internal_state1
Proof
INTRO_TAC THEN
ETAC stateTheory.OTHER_BDS_TO_FETCH_EQ THEN
AIRTAC THEN
STAC
QED

Theorem NOT_EMPTY_FETCH_BD_ADDRESSES_IMPLIES_BDS_LEMMA:
!device_characteristics channel_id memory internal_state addresses tag.
  PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (coperation device_characteristics channel_id).fetch_bd_addresses internal_state = (addresses, tag) /\
  addresses <> []
  ==>
  ?bd bds.
    (cverification device_characteristics channel_id).bds_to_fetch memory internal_state = bd::bds
Proof
INTRO_TAC THEN
CCONTR_TAC THEN
IRTAC (GSYM lists_lemmasTheory.NO_HD_TL_IMPLIES_EMPTY_LEMMA) THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ THEN
AIRTAC THEN
LRTAC THEN
CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
QED

Theorem NOT_EMPTY_FETCH_BD_ADDRESSES_FIRST_BD_RAS_LEMMA:
!device_characteristics channel_id memory internal_state addresses tag.
  PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ device_characteristics /\
  PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (coperation device_characteristics channel_id).fetch_bd_addresses internal_state = (addresses, tag) /\
  addresses <> []
  ==>
  ?bd bd_ras bd_was uf bds.
    (cverification device_characteristics channel_id).bds_to_fetch memory internal_state = ((bd, bd_ras, bd_was), uf)::bds /\
    LIST1_IN_LIST2 addresses bd_ras
Proof
INTRO_TAC THEN
ITAC NOT_EMPTY_FETCH_BD_ADDRESSES_IMPLIES_BDS_LEMMA THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC (mk_var ("memory", (type_of o #1 o dest_forall o concl) thm)) thm)) THEN
AXTAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS THEN
AITAC THEN
PAXTAC THEN
STAC
QED

val _ = export_theory();
