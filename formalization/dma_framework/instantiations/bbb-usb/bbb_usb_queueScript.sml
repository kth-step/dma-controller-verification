open HolKernel Parse boolLib bossLib helper_tactics;
open bbb_usb_functionsTheory wordsTheory listsTheory;

val _ = new_theory "bbb_usb_queue";

Definition ALL_BD_LOCATIONS:
ALL_BD_LOCATIONS = generate_consecutive_addresses (0w : 32 word) (dimword (: 32))
End

Theorem MEM_GENERATE_CONSECUTIVE_ADDRESSES_REC_EQ_OR_SUC_LEMMA:
!n x y.
  MEM x (generate_consecutive_addresses_rec y n)
  ==>
  x = y \/ MEM x (generate_consecutive_addresses_rec (y + 1w) n)
Proof
Induct THENL
[
 INTRO_TAC THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
 PTAC generate_consecutive_addresses_rec THENL
 [
  ETAC listTheory.MEM THEN REMOVE_F_DISJUNCTS_TAC THEN STAC
  ,
  CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
 ]
 ,
 INTRO_TAC THEN
 RW_HYP_LEMMA_TAC generate_consecutive_addresses_rec THEN
 IF_SPLIT_TAC THEN TRY (HYP_CONTR_NEQ_LEMMA_TAC numTheory.NOT_SUC) THEN
 ETAC listTheory.MEM THEN
 SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
 ETAC arithmeticTheory.SUC_SUB1 THEN
 AIRTAC THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  RLTAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  PTAC generate_consecutive_addresses_rec THEN
  ETAC listTheory.MEM THEN
  REWRITE_TAC []
  ,
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  ONCE_REWRITE_TAC [generate_consecutive_addresses_rec] THEN
  REWRITE_TAC [numTheory.NOT_SUC] THEN
  ETAC arithmeticTheory.SUC_SUB1 THEN
  ASM_REWRITE_TAC [listTheory.MEM]
 ]
]
QED

Theorem ADD_SUC_EQ_SUC_ADD_LEMMA:
!x y.
  x + SUC y = SUC x + y
Proof
REWRITE_TAC [arithmeticTheory.ADD_CLAUSES]
QED

Theorem MEM_SUM_GENERATE_CONSECUTIVE_ADDRESSES_REC_LEMMA:
!y x i.
  i = x + y
  ==>
  MEM (n2w i) (generate_consecutive_addresses_rec (n2w x) y)
Proof
Induct THENL
[
 REWRITE_TAC [arithmeticTheory.ADD_0] THEN
 INTRO_TAC THEN
 RLTAC THEN
 PTAC generate_consecutive_addresses_rec THEN TRY (CONTR_NEG_ASM_TAC boolTheory.EQ_REFL) THEN
 REWRITE_TAC [listTheory.MEM]
 ,
 INTRO_TAC THEN
 PTAC generate_consecutive_addresses_rec THEN TRY (HYP_CONTR_NEQ_LEMMA_TAC numTheory.NOT_SUC) THEN
 ETAC arithmeticTheory.SUC_SUB1 THEN
 ETAC ADD_SUC_EQ_SUC_ADD_LEMMA THEN
 AIRTAC THEN
 ETAC wordsTheory.n2w_SUC THEN
 ASM_REWRITE_TAC [listTheory.MEM]
]
QED

Theorem ALL_LEQ_MEM_GENERATE_CONSECUTIVE_ADDRESSES_REC_LEMMA:
!n i.
  i <= n
  ==>
  MEM (n2w i) (generate_consecutive_addresses_rec 0w n)
Proof
Induct THENL
[
 INTRO_TAC THEN
 ETAC arithmeticTheory.LESS_EQ_0 THEN
 LRTAC THEN
 PTAC generate_consecutive_addresses_rec THEN TRY (REWRITE_TAC [listTheory.MEM]) THEN CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
 ,
 INTRO_TAC THEN
 ETAC arithmeticTheory.LESS_OR_EQ THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  ETAC arithmeticTheory.LESS_EQ_IFF_LESS_SUC THEN
  AIRTAC THEN
  PTAC generate_consecutive_addresses_rec THEN TRY (HYP_CONTR_NEQ_LEMMA_TAC numTheory.NOT_SUC) THEN
  ETAC arithmeticTheory.SUC_SUB1 THEN
  IRTAC MEM_GENERATE_CONSECUTIVE_ADDRESSES_REC_EQ_OR_SUC_LEMMA THEN
  ASM_REWRITE_TAC [listTheory.MEM]
  ,
  RLTAC THEN
  MATCH_MP_TAC MEM_SUM_GENERATE_CONSECUTIVE_ADDRESSES_REC_LEMMA THEN
  REWRITE_TAC [arithmeticTheory.ADD]
 ]
]
QED

Theorem ALL_LT_MEM_GENERATE_CONSECUTIVE_ADDRESSES_LEMMA:
!n i.
  i < n
  ==>
  MEM (n2w i) (generate_consecutive_addresses 0w n)
Proof
INTRO_TAC THEN
PTAC generate_consecutive_addresses THEN
MATCH_MP_TAC ALL_LEQ_MEM_GENERATE_CONSECUTIVE_ADDRESSES_REC_LEMMA THEN
IRTAC arithmeticTheory.SUB_LESS_OR THEN
STAC
QED

Theorem BD_LOCATION_IN_ALL_BD_LOCATIONS_LEMMA:
!bd_address.
  MEM bd_address ALL_BD_LOCATIONS
Proof
REWRITE_TAC [ALL_BD_LOCATIONS] THEN
GEN_TAC THEN
ASSUME_TAC (SPEC “bd_address : 32 word” (INST_TYPE [alpha |-> “: 32”] wordsTheory.ranged_word_nchotomy)) THEN
AXTAC THEN
LRTAC THEN
MATCH_MP_TAC (INST_TYPE [alpha |-> “: 32”] ALL_LT_MEM_GENERATE_CONSECUTIVE_ADDRESSES_LEMMA) THEN
STAC
QED

Definition BD_LOCATIONS:
BD_LOCATIONS = set ALL_BD_LOCATIONS
End

Theorem BD_LOCATIONS_FINITE:
FINITE BD_LOCATIONS
Proof
REWRITE_TAC [BD_LOCATIONS, listTheory.FINITE_LIST_TO_SET]
QED

Theorem BD_LOCATIONS_INTERSECT_FINITE_LEMMA:
!S.
  FINITE (pred_set$INTER S BD_LOCATIONS)
Proof
GEN_TAC THEN
MATCH_MP_TAC pred_setTheory.FINITE_INTER THEN
REWRITE_TAC [BD_LOCATIONS_FINITE]
QED

Theorem ALL_IN_BD_LOCATIONS_LEMMA:
!bd_address. bool$IN bd_address BD_LOCATIONS
Proof
GEN_TAC THEN
ETAC BD_LOCATIONS THEN
REWRITE_TAC [BD_LOCATION_IN_ALL_BD_LOCATIONS_LEMMA]
QED

Definition MEASURE_BDS_TO_FETCH:
MEASURE_BDS_TO_FETCH visited_bds1 visited_bds2 =
  let unvisited_bds1 = pred_set$INTER {x | ~MEM x visited_bds1} BD_LOCATIONS in
  let unvisited_bds2 = pred_set$INTER {x | ~MEM x visited_bds2} BD_LOCATIONS in
    pred_set$CARD unvisited_bds1 < pred_set$CARD unvisited_bds2
End

Definition measure_bds_to_fetch:
measure_bds_to_fetch visited_bds =
  let unvisited_bds = pred_set$INTER {x | ~MEM x visited_bds} BD_LOCATIONS in
    CARD unvisited_bds
End

Theorem MEASURE_BDS_TO_FETCH_EQ_MEASURE_BDS_TO_FETCH_LEMMA:
MEASURE_BDS_TO_FETCH = measure measure_bds_to_fetch
Proof
REWRITE_TAC [boolTheory.FUN_EQ_THM] THEN
REPEAT GEN_TAC THEN
ETAC prim_recTheory.measure_thm THEN
Cases_on ‘x’ THEN Cases_on ‘x'’ THEN
REWRITE_TAC [MEASURE_BDS_TO_FETCH, measure_bds_to_fetch] THEN
LETS_TAC THEN
STAC
QED

Definition MEASURE_BDS_TO_FETCH_REC:
(MEASURE_BDS_TO_FETCH_REC (memory1, registers1, visited_bds1, bd_address1) (memory2, registers2, visited_bds2, bd_address2) =
 MEASURE_BDS_TO_FETCH visited_bds1 visited_bds2)
End

Definition measure_bds_to_fetch_rec:
(measure_bds_to_fetch_rec (memory, registers, visited_bds, bd_address) = measure_bds_to_fetch visited_bds)
End

Theorem MEASURE_BDS_TO_FETCH_REC_EQ_LEMMA:
MEASURE_BDS_TO_FETCH_REC = measure measure_bds_to_fetch_rec
Proof
REWRITE_TAC [boolTheory.FUN_EQ_THM] THEN
REPEAT GEN_TAC THEN
PTAC MEASURE_BDS_TO_FETCH_REC THEN
ALL_LRTAC THEN
ETAC MEASURE_BDS_TO_FETCH_EQ_MEASURE_BDS_TO_FETCH_LEMMA THEN
ETAC prim_recTheory.measure_thm THEN
ETAC measure_bds_to_fetch_rec THEN
STAC
QED

Theorem WF_MEASURE_BDS_TO_FETCH_REC:
WF (measure measure_bds_to_fetch_rec)
Proof
REWRITE_TAC [prim_recTheory.WF_measure]
QED

Theorem NOT_MEM_SET_EQ_ABS_NOT_MEM_SET_LEMMA:
!e s.
  {e | ~MEM e s} = {e | (\e. ~MEM e s) e}
Proof
BETA_TAC THEN STAC
QED

Theorem NOT_MEM_NEQ_SET_EQ_ABS_NOT_MEM_NEQ_SET_LEMMA:
!e1 e2 s.
  {e1 | ~MEM e1 s /\ e1 <> e2} = {e1 | (\e1. ~MEM e1 s /\ e1 <> e2) e1}
Proof
BETA_TAC THEN STAC
QED

Theorem NOT_MEM_NEQ_SET_EQ_ABS_NOT_MEM_AND_NEQ_SET_LEMMA:
!e1 e2 s.
  {e1 | ~MEM e1 s /\ e1 <> e2} = {e1 | (\e1. ~MEM e1 s) e1 /\ (\e1. e1 <> e2) e1}
Proof
BETA_TAC THEN STAC
QED

Theorem VISITED_BD_IMPLIES_MEASURE_LEMMA:
!visited_bds1 visited_bds2 bd_address.
  visited_bds2 = visited_bds1 ++ [bd_address] /\
  ~MEM bd_address visited_bds1
  ==>
  measure_bds_to_fetch visited_bds2 < measure_bds_to_fetch visited_bds1
Proof
INTRO_TAC THEN
ETAC measure_bds_to_fetch THEN
LETS_TAC THEN
PAT_X_ASSUM “l = l1 ++ l2” (fn thm => ASSUME_TAC thm) THEN
LRTAC THEN
RW_HYPS_TAC listTheory.MEM_APPEND THEN
RW_HYPS_TAC boolTheory.DE_MORGAN_THM THEN
RW_HYPS_TAC listTheory.MEM THEN
ASSUME_TAC (SPEC “{(x : 32 word) | ~MEM x visited_bds1}” BD_LOCATIONS_INTERSECT_FINITE_LEMMA) THEN
ASM_RL_RW_OTHERS_KEEP_TAC THEN
IRTAC pred_setTheory.CARD_PSUBSET THEN
INST_IMP_ASM_GOAL_TAC THEN
ALL_LRTAC THEN
ETAC pred_setTheory.PSUBSET_MEMBER THEN
CONJS_TAC THENL
[
 ETAC pred_setTheory.SUBSET_applied THEN
 INTRO_TAC THEN
 ETAC pred_setTheory.INTER_applied THEN
 ETAC NOT_MEM_NEQ_SET_EQ_ABS_NOT_MEM_AND_NEQ_SET_LEMMA THEN
 ETAC pred_setTheory.GSPEC_AND THEN
 ETAC pred_setTheory.IN_INTER THEN
 APP_SCALAR_TAC THEN
 STAC
 ,
 EXISTS_TAC “bd_address : 32 word” THEN
 ETAC pred_setTheory.IN_INTER THEN
 REWRITE_TAC [ALL_IN_BD_LOCATIONS_LEMMA] THEN
 ETAC NOT_MEM_SET_EQ_ABS_NOT_MEM_SET_LEMMA THEN
 ETAC NOT_MEM_NEQ_SET_EQ_ABS_NOT_MEM_NEQ_SET_LEMMA THEN
 ETAC pred_setTheory.IN_GSPEC_IFF THEN
 APP_SCALAR_TAC THEN
 ETAC boolTheory.DE_MORGAN_THM THEN
 ETAC boolTheory.NOT_CLAUSES THEN
 STAC
]
QED

Theorem NOT_VISTED_BD_IN_LIST_IMPLIES_MEASURE_BDS_TO_FETCH_LEMMA:
!visited_bds visited_bds' sop_bd_address.
  ~MEM sop_bd_address visited_bds /\
  LIST1_IN_LIST2 (visited_bds ++ [sop_bd_address]) visited_bds'
  ==>
  measure_bds_to_fetch visited_bds' < measure_bds_to_fetch visited_bds
Proof
INTRO_TAC THEN
ETAC measure_bds_to_fetch THEN
LETS_TAC THEN
ETAC listsTheory.LIST1_IN_LIST2 THEN
ETAC listTheory.EVERY_MEM THEN
APP_SCALAR_TAC THEN
ASSUME_TAC (SPEC “{(x : 32 word) | ~MEM x visited_bds}” BD_LOCATIONS_INTERSECT_FINITE_LEMMA) THEN
ASM_RL_RW_OTHERS_KEEP_TAC THEN
IRTAC pred_setTheory.CARD_PSUBSET THEN
INST_IMP_ASM_GOAL_TAC THEN
ALL_LRTAC THEN
ETAC pred_setTheory.PSUBSET_MEMBER THEN
CONJS_TAC THENL
[
 ETAC pred_setTheory.SUBSET_applied THEN
 INTRO_TAC THEN
 ETAC pred_setTheory.INTER_applied THEN
 ETAC NOT_MEM_SET_EQ_ABS_NOT_MEM_SET_LEMMA THEN
 ETAC pred_setTheory.IN_GSPEC_IFF THEN
 APP_SCALAR_TAC THEN
 PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (Q.SPEC ‘x’ thm)) THEN
 RW_HYP_LEMMA_TAC (GEN_ALL boolTheory.MONO_NOT_EQ) THEN
 AIRTAC THEN
 ETAC listTheory.MEM_APPEND THEN
 ETAC boolTheory.DE_MORGAN_THM THEN
 STAC
 ,
 EXISTS_TAC “sop_bd_address : 32 word” THEN
 ETAC pred_setTheory.IN_INTER THEN
 REWRITE_TAC [ALL_IN_BD_LOCATIONS_LEMMA] THEN
 ETAC NOT_MEM_SET_EQ_ABS_NOT_MEM_SET_LEMMA THEN
 ETAC pred_setTheory.IN_GSPEC_IFF THEN
 APP_SCALAR_TAC THEN
 ETAC boolTheory.NOT_CLAUSES THEN
 CONJS_TAC THEN TRY STAC THEN
 WEAKEN_TAC is_neg THEN
 PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (REWRITE_RULE [listTheory.MEM_APPEND, listTheory.MEM] (Q.SPEC ‘sop_bd_address’ thm))) THEN
 STAC 
]
QED


















Theorem BD_ADDRESS_IN_BD_ALIGNED_READ_ADDRESSES_LEMMA:
!bd_address bd_ras.
  bd_ras = bd_aligned_read_addresses bd_address
  ==>
  MEM bd_address bd_ras
Proof
INTRO_TAC THEN
PTAC bd_aligned_read_addresses THEN
RLTAC THEN
LRTAC THEN
LRTAC THEN
PTAC generate_consecutive_addresses THEN
REWRITE_TAC [EVAL “generate_consecutive_addresses_rec (bd_address && 0xFFFFFFE0w) (32 − 1)”] THEN
RW_TAC (std_ss++wordsLib.WORD_ARITH_ss) [listTheory.MEM] THEN
blastLib.BBLAST_TAC
QED

Theorem BD_ADDRESS_IN_GET_BD_RAS_LEMMA:
!bd_ras registers bd_address.
  bd_ras = get_bd_ras registers bd_address
  ==>
  MEM bd_address bd_ras
Proof
INTRO_TAC THEN
PTAC get_bd_ras THEN
LRTAC THEN
ETAC listTheory.MEM_APPEND THEN
IRTAC BD_ADDRESS_IN_BD_ALIGNED_READ_ADDRESSES_LEMMA THEN
STAC
QED















Definition NOT_BD_RA:
NOT_BD_RA visited_bds bds_to_fetch =
!bd_address bd bd_ras bd_was bd_update.
  MEM bd_address visited_bds /\
  MEM ((bd, bd_ras, bd_was), bd_update) bds_to_fetch
  ==>
  ~MEM bd_address bd_ras
End

Theorem NOT_BD_RA_HD_TL_LEMMA:
!visited_bds bd bds.
  NOT_BD_RA visited_bds (bd::bds)
  ==>
  NOT_BD_RA visited_bds [bd] /\
  NOT_BD_RA visited_bds bds
Proof
INTRO_TAC THEN
ETAC NOT_BD_RA THEN
CONJS_TAC THENL
[
 INTRO_TAC THEN INST_IMP_ASM_GOAL_TAC THEN ETAC listTheory.MEM THEN REMOVE_F_DISJUNCTS_TAC THEN STAC
 ,
 INTRO_TAC THEN INST_IMP_ASM_GOAL_TAC THEN ETAC listTheory.MEM THEN STAC
]
QED

Theorem NOT_BD_RA_APPEND_LEMMA:
!visited_bd visited_bds bds_to_fetch.
  NOT_BD_RA [visited_bd] bds_to_fetch /\
  NOT_BD_RA visited_bds bds_to_fetch
  ==>
  NOT_BD_RA (visited_bds ++ [visited_bd]) bds_to_fetch
Proof
INTRO_TAC THEN
ETAC NOT_BD_RA THEN
INTRO_TAC THEN
ETAC listTheory.MEM_APPEND THEN
SPLIT_ASM_DISJS_TAC THEN TRY (AIRTAC THEN STAC) THEN
FAIRTAC THEN
STAC
QED

Theorem MEM_APPEND_IMPLIES_MEM_CONS_APPEND_LEMMA:
!l1 l2 e.
  MEM e (l1 ++ l2)
  ==>
  !e2.
    MEM e (e2::l1 ++ l2)
Proof
INTRO_TAC THEN
GEN_TAC THEN
ETAC listTheory.MEM_APPEND THEN
ETAC listTheory.MEM THEN
SPLIT_ASM_DISJS_TAC THEN STAC
QED

Theorem APPEND_APPEND_IMPLIES_CONS_APPEND_APPEND_LEMMA:
!l l1 l2 l3.
  l1 ++ l2 ++ l3 = l
  ==>
  !e.
    (e::l1) ++ l2 ++ l3 = e::l
Proof
INTRO_TAC THEN
GEN_TAC THEN
ETAC listTheory.APPEND THEN
ETAC listTheory.CONS_11 THEN
STAC
QED

Theorem BDS_TO_FETCH_DISJOINT_TAIL_LEMMA:
!bds bd.
  BDS_TO_FETCH_DISJOINT (bd::bds)
  ==>
  BDS_TO_FETCH_DISJOINT bds
Proof
REWRITE_TAC [bd_queuesTheory.BDS_TO_FETCH_DISJOINT] THEN
INTRO_TAC THEN
INTRO_TAC THEN
IRTAC MEM_APPEND_IMPLIES_MEM_CONS_APPEND_LEMMA THEN
IRTAC APPEND_APPEND_IMPLIES_CONS_APPEND_APPEND_LEMMA THEN
AIRTAC THEN
STAC
QED

Theorem MEM_IMPLIES_MEM_NIL_APPEND_LEMMA:
!e l.
  MEM e l
  ==>
  MEM e ([] ++ l)
Proof
REWRITE_TAC [listTheory.APPEND]
QED

Theorem MEM_IMPLIES_MEM_CONS_LEMMA:
!l e.
  MEM e l
  ==>
  !e2.
    MEM e (e2::l)
Proof
INTRO_TAC THEN
GEN_TAC THEN
ETAC listTheory.MEM THEN
STAC
QED

Theorem DISJOINT_VISITED_BDS_EXTENDS_NOT_BD_RA_LEMMA:
!start_bd_address bd_ras bd_was bd bd_update bds_to_fetch visited_bds1 visited_bds2.
  MEM start_bd_address bd_ras /\
  visited_bds2 = visited_bds1 ++ [start_bd_address] /\
  BDS_TO_FETCH_DISJOINT (((bd, bd_ras, bd_was), bd_update)::bds_to_fetch) /\
  NOT_BD_RA visited_bds1 (((bd, bd_ras, bd_was), bd_update)::bds_to_fetch)
  ==>
  NOT_BD_RA visited_bds2 bds_to_fetch
Proof
INTRO_TAC THEN
LRTAC THEN
ETAC NOT_BD_RA THEN
INTRO_TAC THEN
ETAC listTheory.MEM_APPEND THEN
ETAC listTheory.MEM THEN
REMOVE_F_DISJUNCTS_TAC THEN
SPLIT_ASM_DISJS_TAC THENL
[
 PAT_X_ASSUM “MEM (bd, bdu) l” (fn thm => ASSUME_TAC thm) THEN IRTAC MEM_IMPLIES_MEM_CONS_LEMMA THEN AIRTAC THEN STAC
 ,
 ETAC bd_queuesTheory.BDS_TO_FETCH_DISJOINT THEN
 RLTAC THEN
 IRTAC MEM_IMPLIES_MEM_NIL_APPEND_LEMMA THEN
 PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (REWRITE_RULE [listTheory.APPEND] (Q.SPECL [‘bd’, ‘bd_ras’, ‘bd_was’, ‘bd_update’, ‘bd'’, ‘bd_ras'’, ‘bd_was'’, ‘bd_update'’, ‘[]’, ‘bds_to_fetch’] thm))) THEN
 WEAKEN_TAC is_forall THEN
 AIRTAC THEN
 ETAC listTheory.APPEND THEN
 ETAC listsTheory.DISJOINT_LISTS THEN
 ETAC listTheory.EVERY_MEM THEN
 AIRTAC THEN
 APP_SCALAR_TAC THEN
 STAC
]
QED

Theorem NOT_BD_RA_EMPTY_LEMMA:
!bds : ((num -> 32 word) # 32 word, 32) bds_to_fetch_entry_type list.
  NOT_BD_RA [] bds
Proof
GEN_TAC THEN
ETAC NOT_BD_RA THEN
REWRITE_TAC [listTheory.MEM]
QED

Theorem NOT_BD_RA_VISITED_FIRST_BD_IMPLIES_F_LEMMA:
!visited_bds bd bd_ras bds_to_fetch start_bd_address.
  NOT_BD_RA visited_bds (((bd, bd_ras, bd_ras), no_update)::bds_to_fetch) /\
  MEM start_bd_address visited_bds /\
  MEM start_bd_address bd_ras
  ==>
  F
Proof
INTRO_TAC THEN
IRTAC NOT_BD_RA_HD_TL_LEMMA THEN
ETAC NOT_BD_RA THEN
RW_HYPS_TAC listTheory.MEM THEN
RW_HYPS_TAC pairTheory.PAIR_EQ THEN
AIRTAC THEN
CONTR_ASMS_TAC
QED









Theorem BDS_TO_FETCH_DISJOINT_MEM_NOT_BD_RA_LEMMA:
!bd bd_ras bd_was bd_update bds following_bds address.
  ((bd, bd_ras, bd_was), bd_update)::following_bds = bds /\
  BDS_TO_FETCH_DISJOINT bds /\
  MEM address bd_ras
  ==>
  NOT_BD_RA [address] following_bds
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.BDS_TO_FETCH_DISJOINT THEN
ETAC NOT_BD_RA THEN
INTRO_TAC THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (Q.SPECL [‘bd’, ‘bd_ras’, ‘bd_was’, ‘bd_update’] thm)) THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (Q.SPECL [‘bd'’, ‘bd_ras'’, ‘bd_was'’, ‘bd_update'’] thm)) THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (Q.SPECL [‘[]’, ‘following_bds’] thm)) THEN
ETAC listTheory.APPEND THEN
RLTAC THEN
PAT_X_ASSUM “P ==> Q” (fn thm => ASSUME_TAC (REWRITE_RULE [] thm)) THEN
AIRTAC THEN
ETAC DISJOINT_LISTS THEN
ETAC listTheory.EVERY_MEM THEN
AIRTAC THEN
APP_SCALAR_TAC THEN
ETAC listTheory.MEM THEN
REMOVE_F_DISJUNCTS_TAC THEN
STAC
QED








Theorem BDS_TO_FETCH_DISJOINT_APPEND_LEMMA:
!bds1 bds2.
  BDS_TO_FETCH_DISJOINT (bds1 ++ bds2)
  ==>
  BDS_TO_FETCH_DISJOINT bds1
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.BDS_TO_FETCH_DISJOINT THEN
INTRO_TAC THEN
PAT_X_ASSUM “!x.P” (fn thm => MATCH_MP_TAC thm) THEN
INST_EXISTS_NAMES_TAC ["bd1", "bd_was1", "uf1", "bd2", "bd_was2", "uf2", "preceding_bds"] THEN
Q.EXISTS_TAC ‘following_bds ++ bds2’ THEN
REWRITE_TAC [listTheory.APPEND_ASSOC] THEN
RLTAC THEN
ETAC listTheory.MEM_APPEND THEN
STAC
QED

Theorem NOT_BD_RA_TAIL_LEMMA:
!bd bds visited_bds.
  NOT_BD_RA visited_bds (bd::bds)
  ==>
  NOT_BD_RA visited_bds bds
Proof
INTRO_TAC THEN
ETAC NOT_BD_RA THEN
INTRO_TAC THEN
PAT_X_ASSUM “!x.P” (fn thm => MATCH_MP_TAC thm) THEN
PAXTAC THEN
ETAC listTheory.MEM THEN
STAC
QED

Theorem NOT_BD_RA_APPEND_LEMMA:
!bds1 bds2 visited_bds.
  NOT_BD_RA visited_bds (bds1 ++ bds2)
  ==>
  NOT_BD_RA visited_bds bds1
Proof
INTRO_TAC THEN
ETAC NOT_BD_RA THEN
INTRO_TAC THEN
PAT_X_ASSUM “!x.P” (fn thm => MATCH_MP_TAC thm) THEN
PAXTAC THEN
ETAC listTheory.MEM_APPEND THEN
STAC
QED

val _ = export_theory();

