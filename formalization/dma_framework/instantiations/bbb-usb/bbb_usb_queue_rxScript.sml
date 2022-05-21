open HolKernel Parse boolLib bossLib helper_tactics
open bbb_usb_queueTheory;

val _ = new_theory "bbb_usb_queue_rx";

val rx_bds_to_fetch_rec_tgoal = Hol_defn "rx_bds_to_fetch_rec" ‘
rx_bds_to_fetch_rec memory registers visited_bds bd_address =
  if bd_address = 0w then (* The end is reached. *)
    []
  else if MEM bd_address visited_bds then (* Let visited BD be last to terminate and indicate cyclicity (same BD occurs twice). *)
    let bd_ras = get_bd_ras registers bd_address in
    let bd_was = bd_ras in
    let bd_bytes = MAP memory bd_ras in
    let (bd, li) = form_bd_li bd_bytes in
      [(((bd, li), bd_ras, bd_was), no_update)]
  else
    let bd_ras = get_bd_ras registers bd_address in
    let bd_was = bd_ras in
    let bd_bytes = MAP memory bd_ras in
    let (bd, li) = form_bd_li bd_bytes in
      if li_to_eoq li then
        [(((bd, li), bd_ras, bd_was), no_update)]
      else
        let visited_bds = visited_bds ++ [bd_address] in
        let next_bd_address = li_to_next_bd_address registers li in
          (((bd, li), bd_ras, bd_was), no_update)::(rx_bds_to_fetch_rec memory registers visited_bds next_bd_address)’

val (rx_bds_to_fetch_rec, rx_bds_to_fetch_rec_ind) = Defn.tprove (
(*Defn.tgoal*) rx_bds_to_fetch_rec_tgoal,
(fn (A, t) =>
  let val goal_type = (type_of o #1 o dest_exists) t in
  let val measure_type = type_of “MEASURE_BDS_TO_FETCH_REC” in
  let val type_matching = match_type measure_type goal_type in
  let val type_r_measure_channel_id = inst type_matching “MEASURE_BDS_TO_FETCH_REC”  in
    EXISTS_TAC type_r_measure_channel_id (A, t)
  end end end end) THEN
CONJ_TAC THEN TRY (REWRITE_TAC [MEASURE_BDS_TO_FETCH_REC_EQ_LEMMA, WF_MEASURE_BDS_TO_FETCH_REC]) THEN
INTRO_TAC THEN
ETAC prim_recTheory.measure_thm THEN
ETAC measure_bds_to_fetch_rec THEN
IRTAC VISITED_BD_IMPLIES_MEASURE_LEMMA THEN
STAC
)

val rx_bds_to_fetch_rec = save_thm ("rx_bds_to_fetch_rec", GEN_ALL rx_bds_to_fetch_rec)
val rx_bds_to_fetch_rec_ind = save_thm ("rx_bds_to_fetch_rec_ind", rx_bds_to_fetch_rec_ind)

Definition rx_bds_to_fetch:
rx_bds_to_fetch queue_id memory internal_state =
  rx_bds_to_fetch_rec memory internal_state.registers [] (internal_state.qhp queue_id)
End

Theorem BD_BYTES_EXISTS_LEMMA:
!memory registers visited_bds bd_address bds.
  bd_address <> 0w /\
  bds = rx_bds_to_fetch_rec memory registers visited_bds bd_address
  ==>
  ?bd_ras bd_bytes bd (li : 32 word).
    bd_ras = get_bd_ras registers bd_address /\
    bd_bytes = MAP memory bd_ras /\
    (bd, li) = form_bd_li bd_bytes
Proof
INTRO_TAC THEN
EXISTS_EQ_TAC THEN
REWRITE_TAC [GSYM pairTheory.ABS_PAIR_THM]
QED

Theorem RX_BDS_TO_FETCH_REC_BD_RAS_WAS_EQ_IND_LEMMA:
!memory registers visited_bds bd_address.
  (\memory registers visited_bds bd_address.
   !bd bd_ras bd_was bd_update bds.
    bds = rx_bds_to_fetch_rec memory registers visited_bds bd_address /\
    MEM ((bd, bd_ras, bd_was), bd_update) bds
    ==>
    bd_ras = bd_was) memory registers visited_bds bd_address
Proof
MATCH_MP_TAC rx_bds_to_fetch_rec_ind THEN
BETA_TAC THEN
INTRO_TAC THEN
INTRO_TAC THEN
Cases_on ‘bd_address = 0w’ THEN TRY (PTAC rx_bds_to_fetch_rec THEN TRY (CONTR_NEG_ASM_TAC boolTheory.EQ_REFL) THEN LRTAC THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC) THEN
Cases_on ‘MEM bd_address visited_bds’ THEN TRY (PTAC rx_bds_to_fetch_rec THEN LRTAC THEN ETAC listTheory.MEM THEN REMOVE_F_DISJUNCTS_TAC THEN EQ_PAIR_ASM_TAC THEN STAC) THEN
INST_IMP_TAC BD_BYTES_EXISTS_LEMMA THEN
AXTAC THEN
Cases_on ‘li_to_eoq li’ THEN TRY (PTAC rx_bds_to_fetch_rec THEN LRTAC THEN ETAC listTheory.MEM THEN REMOVE_F_DISJUNCTS_TAC THEN EQ_PAIR_ASM_TAC THEN STAC) THEN
PTAC rx_bds_to_fetch_rec THEN
LRTAC THEN
ETAC listTheory.MEM THEN
SPLIT_ASM_DISJS_TAC THEN TRY (EQ_PAIR_ASM_TAC THEN STAC) THEN
AIRTAC THEN
AIRTAC THEN
STAC
QED

Theorem RX_BDS_TO_FETCH_REC_BD_RAS_WAS_EQ_LEMMA:
!memory registers visited_bds bd_address bd bd_ras bd_was bd_update bds.
  bds = rx_bds_to_fetch_rec memory registers visited_bds bd_address /\
  MEM ((bd, bd_ras, bd_was), bd_update) bds
  ==>
  bd_ras = bd_was
Proof
REWRITE_TAC [BETA_RULE RX_BDS_TO_FETCH_REC_BD_RAS_WAS_EQ_IND_LEMMA]
QED

Theorem RX_BDS_TO_FETCH_BD_RAS_WAS_EQ_LEMMA:
!channel_id memory internal_state bds bd bd_ras bd_was bd_update.
  bds = rx_bds_to_fetch channel_id memory internal_state /\
  MEM ((bd, bd_ras, bd_was), bd_update) bds
  ==>
  bd_ras = bd_was
Proof
INTRO_TAC THEN
ETAC rx_bds_to_fetch THEN
IRTAC RX_BDS_TO_FETCH_REC_BD_RAS_WAS_EQ_LEMMA THEN
STAC
QED

Theorem RX_FETCH_BD_UPDATES_QHP_LEMMA:
!internal_state1 internal_state2 channel_id bytes tag fetch_result.
  (internal_state2, SOME fetch_result) = rx_fetch_bd channel_id internal_state1 (SOME (bytes, tag))
  ==>
  ?bd li bd_ras.
    bd_ras = get_bd_ras internal_state1.registers (internal_state1.qhp channel_id) /\
    fetch_result = (((bd, li), bd_ras, bd_ras), no_update) /\
    (bd, li) = form_bd_li bytes /\
    ((li_to_eoq li /\ internal_state2.qhp channel_id = 0w) \/
     (~li_to_eoq li /\
      internal_state2.qhp channel_id = li_to_next_bd_address internal_state2.registers li /\
      internal_state2.qhp channel_id = li_to_next_bd_address internal_state1.registers li))
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.rx_fetch_bd THEN TRY (EQ_PAIR_ASM_TAC THEN IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC) THEN
IF_SPLIT_TAC THENL
[
 PAXTAC THEN
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 ETAC optionTheory.SOME_11 THEN
 CONJS_TAC THEN TRY STAC THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
 LRTAC THEN
 RECORD_TAC THEN
 REWRITE_TAC [combinTheory.UPDATE_def] THEN
 APP_SCALAR_TAC THEN
 STAC
 ,
 PAXTAC THEN
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 ETAC optionTheory.SOME_11 THEN
 CONJS_TAC THEN TRY STAC THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 LRTAC THEN
 RECORD_TAC THEN
 REWRITE_TAC [combinTheory.UPDATE_def] THEN
 APP_SCALAR_TAC THEN
 STAC
]
QED

Theorem RX_BDS_TO_FETCH_REC_BD_ADDRESS_ZERO_EQ_EMPTY_LEMMA:
!memory registers visited_bds.
  rx_bds_to_fetch_rec memory registers visited_bds 0w = []
Proof
REPEAT GEN_TAC THEN PTAC rx_bds_to_fetch_rec THEN TRY (CONTR_NEG_ASM_TAC boolTheory.EQ_REFL) THEN STAC
QED

Theorem RX_FETCHED_EOQ_LEMMA:
!internal_state1 internal_state2 channel_id bd li bd_ras bytes tag.
  (internal_state2, SOME (((bd, li), bd_ras, bd_ras), no_update)) = rx_fetch_bd channel_id internal_state1 (SOME (bytes, tag)) /\
  li_to_eoq li
  ==>
  internal_state2.qhp channel_id = 0w
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.rx_fetch_bd THEN TRY (EQ_PAIR_ASM_TAC THEN IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC) THEN
EQ_PAIR_ASM_TAC THEN
ETAC optionTheory.SOME_11 THEN
RLTAC THEN
EQ_PAIR_ASM_TAC THEN
LRTAC THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
REWRITE_TAC [] THEN
RLTAC THEN RLTAC THEN RLTAC THEN
IF_SPLIT_TAC THEN TRY CONTR_ASMS_TAC THEN STAC
QED

Theorem RX_FETCHED_NEOQ_LEMMA:
!internal_state1 internal_state2 channel_id bd li bd_ras bytes tag.
  (internal_state2, SOME (((bd, li), bd_ras, bd_ras), no_update)) = rx_fetch_bd channel_id internal_state1 (SOME (bytes, tag)) /\
  ~li_to_eoq li
  ==>
  internal_state2.qhp channel_id = li_to_next_bd_address internal_state1.registers li /\
  internal_state2.registers = internal_state1.registers
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.rx_fetch_bd THEN TRY (EQ_PAIR_ASM_TAC THEN IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC) THEN
EQ_PAIR_ASM_TAC THEN
ETAC optionTheory.SOME_11 THEN
RLTAC THEN
LRTAC THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
REWRITE_TAC [] THEN
RLTAC THEN
EQ_PAIR_ASM_TAC THEN
RLTAC THEN RLTAC THEN RLTAC THEN
IF_SPLIT_TAC THEN TRY CONTR_ASMS_TAC THEN STAC
QED

Theorem RX_FETCH_BD_POPS_BD_VISITS_POPPED_BD_LEMMA:
!memory internal_state1 internal_state2 channel_id bd li bd_ras bds bytes tag bd_address addresses.
  bd_address = internal_state1.qhp channel_id /\
  (internal_state2, SOME (((bd, li), bd_ras, bd_ras), no_update)) = rx_fetch_bd channel_id internal_state1 (SOME (bytes, tag)) /\
  (((bd, li), bd_ras, bd_ras), no_update)::bds = rx_bds_to_fetch_rec memory internal_state1.registers [] (internal_state1.qhp channel_id)
  ==>
  rx_bds_to_fetch_rec memory internal_state2.registers [bd_address] (internal_state2.qhp channel_id) = bds
Proof
INTRO_TAC THEN
RW_HYP_LEMMA_TAC rx_bds_to_fetch_rec THEN IF_SPLIT_TAC THEN TRY (IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC) THEN
IF_SPLIT_TAC THEN TRY (ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC) THEN
LETS_TAC THEN
IF_SPLIT_TAC THENL
[
 ETAC listTheory.CONS_11 THEN
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN RLTAC THEN
 IRTAC RX_FETCHED_EOQ_LEMMA THEN
 LRTAC THEN
 ALL_LRTAC THEN
 REWRITE_TAC [RX_BDS_TO_FETCH_REC_BD_ADDRESS_ZERO_EQ_EMPTY_LEMMA]
 ,
 ETAC listTheory.CONS_11 THEN
 ETAC listTheory.APPEND THEN
 EQ_PAIR_ASM_TAC THEN
 IRTAC RX_FETCHED_NEOQ_LEMMA THEN
 STAC
]
QED

Theorem QHP_IN_FETCHED_RX_BD_RAS_LEMMA:
!channel_id internal_state1 internal_state2 tag bytes bd bd_ras bd_address.
  (internal_state2, SOME ((bd, bd_ras, bd_ras), no_update)) = rx_fetch_bd channel_id internal_state1 (SOME (bytes, tag)) /\
  bd_address = internal_state1.qhp channel_id
  ==>
  MEM bd_address bd_ras
Proof
INTRO_TAC THEN
IRTAC RX_FETCH_BD_UPDATES_QHP_LEMMA THEN
AXTAC THEN
WEAKEN_TAC is_disj THEN
EQ_PAIR_ASM_TAC THEN
LRTAC THEN
IRTAC BD_ADDRESS_IN_GET_BD_RAS_LEMMA THEN
STAC
QED

Theorem BDS_TO_FETCH_DISJOINT_NOT_BD_RA_VISITED_BDS_PAIR_PRESERVES_RX_BDS_TO_FETCH_LEMMA:
!bds_to_fetch visited_bds1 visited_bds2 start_bd_address memory registers.
  BDS_TO_FETCH_DISJOINT bds_to_fetch /\
  NOT_BD_RA visited_bds1 bds_to_fetch /\
  NOT_BD_RA visited_bds2 bds_to_fetch /\
  rx_bds_to_fetch_rec memory registers visited_bds1 start_bd_address = bds_to_fetch
  ==>
  rx_bds_to_fetch_rec memory registers visited_bds2 start_bd_address = bds_to_fetch
Proof
Induct THENL
[
 INTRO_TAC THEN
 PTAC rx_bds_to_fetch_rec THEN TRY (STAC ORELSE (PTAC rx_bds_to_fetch_rec THEN (IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC))) THEN
 RW_HYP_LEMMA_TAC rx_bds_to_fetch_rec THEN
 IF_SPLIT_TAC THEN TRY CONTR_ASMS_TAC THEN
 IF_SPLIT_TAC THEN TRY (LETS_TAC THEN IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC) THEN
 LETS_TAC THEN
 IF_SPLIT_TAC THEN TRY (IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC)
 ,
 INTRO_TAC THEN
 RW_HYP_LEMMA_TAC rx_bds_to_fetch_rec THEN
 IF_SPLIT_TAC THEN TRY (IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC) THEN
 IF_SPLIT_TAC THENL
 [
  LETS_TAC THEN
  ETAC listTheory.CONS_11 THEN
  RLTAC THEN
  RLTAC THEN
  WEAKEN_TAC is_forall THEN
  ETAC NOT_BD_RA THEN
  RW_HYPS_TAC listTheory.MEM THEN
  RW_HYPS_TAC pairTheory.PAIR_EQ THEN
  ASSUME_TAC (REWRITE_RULE [] (Q.SPECL [‘get_bd_ras registers start_bd_address’, ‘registers’, ‘start_bd_address’] BD_ADDRESS_IN_GET_BD_RAS_LEMMA)) THEN
  RLTAC THEN
  RLTAC THEN
  FAIRTAC THEN
  CONTR_ASMS_TAC
  ,
  LETS_TAC THEN
  IF_SPLIT_TAC THEN TRY ((ETAC listTheory.CONS_11 THEN LRTAC THEN LRTAC THEN WEAKEN_TAC is_forall THEN PTAC rx_bds_to_fetch_rec THEN STAC) ORELSE (PTAC rx_bds_to_fetch_rec THEN STAC)) THEN
  ETAC listTheory.CONS_11 THEN
  RLTAC THEN
  PTAC rx_bds_to_fetch_rec THENL
  [
   ASSUME_TAC (REWRITE_RULE [] (Q.SPECL [‘get_bd_ras registers start_bd_address’, ‘registers’, ‘start_bd_address’] BD_ADDRESS_IN_GET_BD_RAS_LEMMA)) THEN
   PAT_X_ASSUM “bd_ras = get_bd_ras registers start_bd_address” (fn thm => ASSUME_TAC thm) THEN
   RLTAC THEN
   IRTAC NOT_BD_RA_VISITED_FIRST_BD_IMPLIES_F_LEMMA THEN
   SOLVE_F_ASM_TAC
   ,
   REWRITE_TAC [listTheory.CONS_11] THEN
   ITAC BDS_TO_FETCH_DISJOINT_TAIL_LEMMA THEN
   PAT_X_ASSUM “BDS_TO_FETCH_DISJOINT (bd::bds)” (fn thm => ASSUME_TAC thm THEN ASSUME_TAC thm) THEN
   ASSUME_TAC (REWRITE_RULE [] (Q.SPECL [‘get_bd_ras registers start_bd_address’, ‘registers’, ‘start_bd_address’] BD_ADDRESS_IN_GET_BD_RAS_LEMMA)) THEN
   PAT_X_ASSUM “bd_ras = get_bd_ras registers start_bd_address” (fn thm => ASSUME_TAC thm) THEN
   RLTAC THEN
   PAT_X_ASSUM “MEM start_bd_address bd_ras” (fn thm => ASSUME_TAC thm THEN ASSUME_TAC thm) THEN
   IRTAC DISJOINT_VISITED_BDS_EXTENDS_NOT_BD_RA_LEMMA THEN
   IRTAC DISJOINT_VISITED_BDS_EXTENDS_NOT_BD_RA_LEMMA THEN
   INST_IMP_ASM_GOAL_TAC THEN
   STAC
  ]
 ]
]
QED

Theorem BDS_TO_FETCH_DISJOINT_NOT_BD_RA_VISITED_BDS_IMPLIES_NO_VISITED_BDS_RX_BDS_TO_FETCH_LEMMA:
!bds_to_fetch visited_bds start_bd_address memory registers.
  BDS_TO_FETCH_DISJOINT bds_to_fetch /\
  NOT_BD_RA visited_bds bds_to_fetch /\
  bds_to_fetch = rx_bds_to_fetch_rec memory registers visited_bds start_bd_address
  ==>
  rx_bds_to_fetch_rec memory registers [] start_bd_address = bds_to_fetch
Proof
INTRO_TAC THEN
MATCH_MP_TAC BDS_TO_FETCH_DISJOINT_NOT_BD_RA_VISITED_BDS_PAIR_PRESERVES_RX_BDS_TO_FETCH_LEMMA THEN
PAXTAC THEN
ASM_REWRITE_TAC [NOT_BD_RA_EMPTY_LEMMA]
QED

Theorem BDS_TO_FETCH_DISJOINT_IMPLIES_RX_BDS_TO_FETCH_POP_LEMMA:
!memory internal_state1 internal_state2 channel_id bd li bd_ras bds bds_to_fetch bytes tag.
  bds_to_fetch = rx_bds_to_fetch channel_id memory internal_state1 /\
  BDS_TO_FETCH_DISJOINT bds_to_fetch /\
  (((bd, li), bd_ras, bd_ras), no_update)::bds = bds_to_fetch /\
  (internal_state2, SOME (((bd, li), bd_ras, bd_ras), no_update)) = rx_fetch_bd channel_id internal_state1 (SOME (bytes, tag))
  ==>
  rx_bds_to_fetch channel_id memory internal_state2 = bds
Proof
INTRO_TAC THEN
ITAC QHP_IN_FETCHED_RX_BD_RAS_LEMMA THEN
ITAC BDS_TO_FETCH_DISJOINT_MEM_NOT_BD_RA_LEMMA THEN
ETAC rx_bds_to_fetch THEN
MATCH_MP_TAC BDS_TO_FETCH_DISJOINT_NOT_BD_RA_VISITED_BDS_IMPLIES_NO_VISITED_BDS_RX_BDS_TO_FETCH_LEMMA THEN
PTAC rx_bds_to_fetch_rec THENL
[
 IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
 ,
 ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
 ,
 IRTAC BDS_TO_FETCH_DISJOINT_TAIL_LEMMA THEN
 Q.EXISTS_TAC ‘[]’ THEN
 CONJS_TAC THEN TRY (ASM_REWRITE_TAC [NOT_BD_RA_EMPTY_LEMMA]) THEN
 LRTAC THEN
 ETAC listTheory.CONS_11 THEN
 EQ_PAIR_ASM_TAC THEN
 NLRTAC 4 THEN
 IRTAC RX_FETCHED_EOQ_LEMMA THEN
 LRTAC THEN
 LRTAC THEN
 REWRITE_TAC [RX_BDS_TO_FETCH_REC_BD_ADDRESS_ZERO_EQ_EMPTY_LEMMA]
 ,
 PAXTAC THEN
 CONJS_TAC THEN TRY ((IRTAC BDS_TO_FETCH_DISJOINT_TAIL_LEMMA THEN STAC) ORELSE STAC) THEN
 LRTAC THEN
 ETAC listTheory.CONS_11 THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 4 THEN
 IRTAC RX_FETCHED_NEOQ_LEMMA THEN
 RLTAC THEN
 RLTAC THEN
 ETAC listTheory.APPEND THEN
 STAC
]
QED

Theorem NOT_NULL_QHP_IMPLIES_RX_FETCH_BD_ADDRESSES_EQ_GET_BD_RAS_QHP_LEMMA:
!internal_state channel_id addresses tag.
  internal_state.qhp channel_id <> 0w /\
  (addresses, tag) = rx_fetch_bd_addresses channel_id internal_state
  ==>
  addresses = get_bd_ras internal_state.registers (internal_state.qhp channel_id)
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.rx_fetch_bd_addresses THEN
EQ_PAIR_ASM_TAC THEN
STAC
QED

Theorem RX_FETCH_FIRST_BD_LEMMA:
!channel_id memory internal_state1 internal_state2 bd bds fetch_result bytes tag addresses.
  bd::bds = rx_bds_to_fetch channel_id memory internal_state1 /\
  (addresses, tag) = rx_fetch_bd_addresses channel_id internal_state1 /\
  bytes = MAP memory addresses /\
  (internal_state2, SOME fetch_result) = rx_fetch_bd channel_id internal_state1 (SOME (bytes, tag))
  ==>
  bd = fetch_result
Proof
INTRO_TAC THEN
PTAC rx_bds_to_fetch THEN
PTAC rx_bds_to_fetch_rec THEN TRY (IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC) ORELSE (ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC) THEN
 ETAC listTheory.CONS_11 THEN
 IRTAC NOT_NULL_QHP_IMPLIES_RX_FETCH_BD_ADDRESSES_EQ_GET_BD_RAS_QHP_LEMMA THEN
 IRTAC RX_FETCH_BD_UPDATES_QHP_LEMMA THEN
 AXTAC THEN
 SPLIT_ASM_DISJS_TAC THEN
  RLTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN LRTAC THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN STAC
QED

Theorem RX_FETCH_BD_EFFECT_LEMMA:
!channel_id memory internal_state1 internal_state2 bd bds addresses tag bytes fetch_result.
  channel_id <=+ 31w /\
  BDS_TO_FETCH_DISJOINT (bd::bds) /\
  bd::bds = rx_bds_to_fetch channel_id memory internal_state1 /\
  (addresses, tag) = rx_fetch_bd_addresses channel_id internal_state1 /\
  bytes = MAP memory addresses /\
  (internal_state2, SOME fetch_result) = rx_fetch_bd channel_id internal_state1 (SOME (bytes, tag))
  ==>
  rx_bds_to_fetch channel_id memory internal_state2 = bds
Proof
INTRO_TAC THEN
MATCH_MP_TAC BDS_TO_FETCH_DISJOINT_IMPLIES_RX_BDS_TO_FETCH_POP_LEMMA THEN
ITAC RX_FETCH_FIRST_BD_LEMMA THEN
ITAC RX_FETCH_BD_UPDATES_QHP_LEMMA THEN
AXTAC THEN
WEAKEN_TAC is_disj THEN
WEAKEN_TAC is_eq THEN
LRTAC THEN
PAXTAC THEN
RLTAC THEN
RLTAC THEN
STAC
QED

val _ = export_theory();

