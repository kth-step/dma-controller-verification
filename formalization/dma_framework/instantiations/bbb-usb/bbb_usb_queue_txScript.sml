open HolKernel Parse boolLib bossLib helper_tactics;
open bbb_usb_queueTheory;

val _ = new_theory "bbb_usb_queue_tx";

val tx_bds_of_transfer_rec_tgoal = Hol_defn "tx_bds_of_transfer_rec" ‘
tx_bds_of_transfer_rec memory registers visited_bds (bd_address : 32 word) =
  if bd_address = 0w then
    ([], SOME visited_bds) (* Not cyclic. *)
  else if MEM bd_address visited_bds then (* Let visited BD be last to terminate and indicate cyclicity (same BD occurs twice). *)
    let bd_ras = get_bd_ras registers bd_address in
    let bd_was = bd_ras in
    let bd_bytes = MAP memory bd_ras in
    let (bd, li) = form_bd_li bd_bytes in
      ([(((bd, li), bd_ras, bd_was), no_update)], NONE) (* Cyclic. *)
  else
    let bd_ras = get_bd_ras registers bd_address in
    let bd_was = bd_ras in
    let bd_bytes = MAP memory bd_ras in
    let (bd, li) = form_bd_li bd_bytes in
      if eop_bd bd then
        ([(((bd, li), bd_ras, bd_was), no_update)], SOME (visited_bds ++ [bd_address])) (* Not cyclic. *)
      else
        let visited_bds = visited_bds ++ [bd_address] in
        let next_bd_address = next_bd_pointer bd in
        let (bds_to_fetch, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds next_bd_address in
          ((((bd, li), bd_ras, bd_was), no_update)::bds_to_fetch, visited_bds_option)’

val (tx_bds_of_transfer_rec, tx_bds_of_transfer_rec_ind) = Defn.tprove (
(*Defn.tgoal*) tx_bds_of_transfer_rec_tgoal,
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

val tx_bds_of_transfer_rec = save_thm ("tx_bds_of_transfer_rec", GEN_ALL tx_bds_of_transfer_rec)
val tx_bds_of_transfer_rec_ind = save_thm ("tx_bds_of_transfer_rec_ind", tx_bds_of_transfer_rec_ind)

val tx_bds_of_transfers_rec_tgoal = Hol_defn "tx_bds_of_transfers_rec" ‘
tx_bds_of_transfers_rec memory registers visited_bds (sop_bd_address : 32 word) =
  if sop_bd_address = 0w then
    []
  else
    let (bds_of_transfer, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds sop_bd_address in
      if NULL bds_of_transfer then
        []
      else if IS_NONE visited_bds_option then (* Cyclic. *)
        bds_of_transfer
      else
        let li = (\(((bd, li), bd_ras, bd_was), update_flag). li) (HD bds_of_transfer) in
          if li_to_eoq li then
            bds_of_transfer
          else
            let visited_bds = THE visited_bds_option in
            let next_sop_bd_address = li_to_next_bd_address registers li in
              bds_of_transfer ++ (tx_bds_of_transfers_rec memory registers visited_bds next_sop_bd_address)’

Theorem TX_BDS_OF_TRANSFER_REC_NOT_REMOVING_VISITED_BDS_IND_LEMMA:
!memory registers visited_bds1 sop_bd_address.
  (\memory registers visited_bds1 sop_bd_address.
    !visited_bds2_option bds_of_transfer.
  ~IS_NONE visited_bds2_option /\
  (bds_of_transfer, visited_bds2_option) = tx_bds_of_transfer_rec memory registers visited_bds1 sop_bd_address
  ==>
  ?visited_bds2.
    visited_bds2 = THE visited_bds2_option /\
    LIST1_IN_LIST2 visited_bds1 visited_bds2) memory registers visited_bds1 sop_bd_address
Proof
MATCH_MP_TAC tx_bds_of_transfer_rec_ind THEN
APP_SCALAR_TAC THEN
INTRO_TAC THEN
INTRO_TAC THEN
PTAC tx_bds_of_transfer_rec THENL
[
 EQ_PAIR_ASM_TAC THEN LRTAC THEN ETAC optionTheory.THE_DEF THEN EXISTS_EQ_TAC THEN REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
 ,
 EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN ETAC optionTheory.IS_NONE_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC
 ,
 EQ_PAIR_ASM_TAC THEN LRTAC THEN ETAC optionTheory.THE_DEF THEN EXISTS_EQ_TAC THEN ETAC listsTheory.LIST1_IN_LIST2 THEN ETAC listTheory.EVERY_MEM THEN INTRO_TAC THEN APP_SCALAR_TAC THEN ETAC listTheory.MEM_APPEND THEN STAC
 ,
 AITAC THEN EQ_PAIR_ASM_TAC THEN AIRTAC THEN LRTAC THEN LRTAC THEN AXTAC THEN PAXTAC THEN CONJS_TAC THEN TRY STAC THEN ETAC listsTheory.LIST1_IN_LIST2 THEN ETAC listTheory.EVERY_MEM THEN APP_SCALAR_TAC THEN INTRO_TAC THEN INST_IMP_ASM_GOAL_TAC THEN ASM_REWRITE_TAC [listTheory.MEM_APPEND]
]
QED

Theorem TX_BDS_OF_TRANSFER_REC_NOT_REMOVING_VISITED_BDS_LEMMA:
!memory registers visited_bds1 sop_bd_address visited_bds2_option bds_of_transfer.
  ~IS_NONE visited_bds2_option /\
  (bds_of_transfer, visited_bds2_option) = tx_bds_of_transfer_rec memory registers visited_bds1 sop_bd_address
  ==>
  ?visited_bds2.
    visited_bds2 = THE visited_bds2_option /\
    LIST1_IN_LIST2 visited_bds1 visited_bds2
Proof
REWRITE_TAC [BETA_RULE TX_BDS_OF_TRANSFER_REC_NOT_REMOVING_VISITED_BDS_IND_LEMMA]
QED

val (tx_bds_of_transfers_rec, tx_bds_of_transfers_rec_ind) = Defn.tprove (
(*Defn.tgoal*) tx_bds_of_transfers_rec_tgoal,
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
PTAC tx_bds_of_transfer_rec THENL
[
 EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN PTAC optionTheory.IS_NONE_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC
 ,
 EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN ETAC optionTheory.THE_DEF THEN IRTAC VISITED_BD_IMPLIES_MEASURE_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 IRTAC TX_BDS_OF_TRANSFER_REC_NOT_REMOVING_VISITED_BDS_LEMMA THEN
 AXTAC THEN
 RLTAC THEN
 RLTAC THEN
 WEAKEN_TAC is_eq THEN
 LRTAC THEN
 IRTAC NOT_VISTED_BD_IN_LIST_IMPLIES_MEASURE_BDS_TO_FETCH_LEMMA THEN
 STAC
]
)

val tx_bds_of_transfers_rec = save_thm ("tx_bds_of_transfers_rec", GEN_ALL tx_bds_of_transfers_rec)
val tx_bds_of_transfers_rec_ind = save_thm ("tx_bds_of_transfers_rec_ind", tx_bds_of_transfers_rec_ind)

Definition tx_bds_to_fetch:
tx_bds_to_fetch (queue_id : 8 word) memory internal_state =
  let start_bd_address = internal_state.qhp queue_id in
  let (first_packet_bds, visited_bds_option) = tx_bds_of_transfer_rec memory internal_state.registers [] start_bd_address in
    if NULL first_packet_bds then
      []
    else if IS_NONE visited_bds_option then
      first_packet_bds
    else
      let endpoint_id = w2w ((queue_id - 32w) >>> 1) in
      let endpoint = internal_state.endpoints_tx endpoint_id in
      let offset = word_bit 0 queue_id in (* Each TX endpoint manages 2 channels; sop_li exists for two channels therefore, identified by LSB. *)
      let sop_li = if endpoint.sop offset then (SND o FST o FST) (HD first_packet_bds) else endpoint.sop_li offset in
        if li_to_eoq sop_li then
          first_packet_bds
        else
          let visited_bds = THE visited_bds_option in
          let next_sop_bd_address = li_to_next_bd_address internal_state.registers sop_li in
            first_packet_bds ++ (tx_bds_of_transfers_rec memory internal_state.registers visited_bds next_sop_bd_address)
End

Theorem TX_BDS_OF_TRANSFER_REC_ZERO_START_IMPLIES_EMPTY_BDS_LEMMA:
!memory registers visited_bds bds visited_bds_option.
  (bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds 0w
  ==>
  bds = []
Proof
INTRO_TAC THEN PTAC tx_bds_of_transfer_rec THEN TRY (CONTR_NEG_ASM_TAC boolTheory.EQ_REFL) THEN
EQ_PAIR_ASM_TAC THEN STAC
QED

Theorem BDS_TO_FETCH_DISJOINT_NOT_BD_RA_VISITED_BDS_PAIR_PRESERVES_TX_BDS_TO_FETCH_LEMMA:
!bds_to_fetch visited_bds1 visited_bds2 start_bd_address memory registers visited_bds_option.
  BDS_TO_FETCH_DISJOINT bds_to_fetch /\
  NOT_BD_RA visited_bds1 bds_to_fetch /\
  NOT_BD_RA visited_bds2 bds_to_fetch /\
  (bds_to_fetch, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds1 start_bd_address
  ==>
  ?visited_bds_option'.
    (bds_to_fetch, visited_bds_option') = tx_bds_of_transfer_rec memory registers visited_bds2 start_bd_address
Proof
Induct THENL
[
 INTRO_TAC THEN
 PTAC tx_bds_of_transfer_rec THENL
 [
  REWRITE_TAC [pairTheory.PAIR_EQ] THEN EXISTS_EQ_TAC
  ,
  PTAC tx_bds_of_transfer_rec THEN EQ_PAIR_ASM_TAC THEN IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
  ,
  PTAC tx_bds_of_transfer_rec THEN EQ_PAIR_ASM_TAC THEN IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
  ,
  PAT_X_ASSUM “([], x) = f a b c d” (fn thm => ASSUME_TAC thm) THEN
  PTAC tx_bds_of_transfer_rec THEN EQ_PAIR_ASM_TAC THEN IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
 ]
 ,
 INTRO_TAC THEN
 PTAC tx_bds_of_transfer_rec THEN REWRITE_TAC [pairTheory.PAIR_EQ] THEN EXISTS_EQ_TAC THENL
 [
  PTAC tx_bds_of_transfer_rec THEN EQ_PAIR_ASM_TAC THEN IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
  ,
  PTAC tx_bds_of_transfer_rec THEN TRY (EQ_PAIR_ASM_TAC THEN STAC) THEN
  EQ_PAIR_ASM_TAC THEN
  ASSUME_TAC (REWRITE_RULE [] (Q.SPECL [‘get_bd_ras registers start_bd_address’, ‘registers’, ‘start_bd_address’] BD_ADDRESS_IN_GET_BD_RAS_LEMMA)) THEN
  PAT_X_ASSUM “bd_ras = get_bd_ras registers start_bd_address” (fn thm => ASSUME_TAC thm) THEN
  RLTAC THEN
  ETAC listTheory.CONS_11 THEN
  LRTAC THEN
  RLTAC THEN
  RLTAC THEN
  ETAC NOT_BD_RA THEN
  RW_HYPS_TAC listTheory.MEM THEN
  RW_HYPS_TAC pairTheory.PAIR_EQ THEN
  PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (REWRITE_RULE [] (Q.SPECL [‘start_bd_address’, ‘(bd, li)’, ‘bd_ras’, ‘bd_ras’, ‘no_update’] thm))) THEN
  WEAKEN_TAC is_forall THEN
  WEAKEN_TAC is_forall THEN
  AIRTAC THEN
  CONTR_ASMS_TAC
  ,
  PTAC tx_bds_of_transfer_rec THEN TRY (EQ_PAIR_ASM_TAC THEN STAC) THEN
  PAT_X_ASSUM “(h::bds_to_fetch,visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds1 start_bd_address” (fn thm => ASSUME_TAC thm) THEN
  PTAC tx_bds_of_transfer_rec THENL
  [
   ASSUME_TAC (REWRITE_RULE [] (Q.SPECL [‘get_bd_ras registers start_bd_address’, ‘registers’, ‘start_bd_address’] BD_ADDRESS_IN_GET_BD_RAS_LEMMA)) THEN
   PAT_X_ASSUM “bd_ras = get_bd_ras registers start_bd_address” (fn thm => ASSUME_TAC thm) THEN
   RLTAC THEN
   EQ_PAIR_ASM_TAC THEN
   ETAC listTheory.CONS_11 THEN
   LRTAC THEN
   ETAC NOT_BD_RA THEN
   WEAKEN_TAC is_forall THEN
   RW_HYPS_TAC listTheory.MEM THEN
   RW_HYPS_TAC pairTheory.PAIR_EQ THEN
   PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (REWRITE_RULE [] (Q.SPECL [‘start_bd_address’, ‘(bd, li)’, ‘bd_ras’, ‘bd_ras’, ‘no_update’] thm))) THEN
   WEAKEN_TAC is_forall THEN
   AIRTAC THEN
   CONTR_ASMS_TAC
   ,
   EQ_PAIR_ASM_TAC THEN
   ETAC listTheory.CONS_11 THEN
   LRTAC THEN
   RLTAC THEN
   ASSUME_TAC (REWRITE_RULE [] (Q.SPECL [‘get_bd_ras registers start_bd_address’, ‘registers’, ‘start_bd_address’] BD_ADDRESS_IN_GET_BD_RAS_LEMMA)) THEN
   PAT_X_ASSUM “bd_ras = get_bd_ras registers start_bd_address” (fn thm => ASSUME_TAC thm) THEN
   RLTAC THEN
   ITAC DISJOINT_VISITED_BDS_EXTENDS_NOT_BD_RA_LEMMA THEN
   PAT_X_ASSUM “visited_bds'' = visited_bds1 ++ [start_bd_address]” (fn thm => ALL_TAC) THEN
   ITAC DISJOINT_VISITED_BDS_EXTENDS_NOT_BD_RA_LEMMA THEN
   IRTAC BDS_TO_FETCH_DISJOINT_TAIL_LEMMA THEN
   FAIRTAC THEN
   AXTAC THEN
   RLTAC THEN
   EQ_PAIR_ASM_TAC THEN
   STAC
  ]
  ,
  PAT_X_ASSUM “(h::bds_to_fetch,visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds1 start_bd_address” (fn thm => ASSUME_TAC thm) THEN
  PTAC tx_bds_of_transfer_rec THENL
  [
   ASSUME_TAC (REWRITE_RULE [] (Q.SPECL [‘get_bd_ras registers start_bd_address’, ‘registers’, ‘start_bd_address’] BD_ADDRESS_IN_GET_BD_RAS_LEMMA)) THEN
   PAT_X_ASSUM “bd_ras = get_bd_ras registers start_bd_address” (fn thm => ASSUME_TAC thm) THEN
   RLTAC THEN
   EQ_PAIR_ASM_TAC THEN
   ETAC listTheory.CONS_11 THEN
   LRTAC THEN
   ETAC NOT_BD_RA THEN
   WEAKEN_TAC is_forall THEN
   RW_HYPS_TAC listTheory.MEM THEN
   RW_HYPS_TAC pairTheory.PAIR_EQ THEN
   PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (REWRITE_RULE [] (Q.SPECL [‘start_bd_address’, ‘(bd, li)’, ‘bd_ras’, ‘bd_ras’, ‘no_update’] thm))) THEN
   WEAKEN_TAC is_forall THEN
   AIRTAC THEN
   CONTR_ASMS_TAC
   ,
   EQ_PAIR_ASM_TAC THEN
   ETAC listTheory.CONS_11 THEN
   LRTAC THEN
   RLTAC THEN
   ASSUME_TAC (REWRITE_RULE [] (Q.SPECL [‘get_bd_ras registers start_bd_address’, ‘registers’, ‘start_bd_address’] BD_ADDRESS_IN_GET_BD_RAS_LEMMA)) THEN
   PAT_X_ASSUM “bd_ras = get_bd_ras registers start_bd_address” (fn thm => ASSUME_TAC thm) THEN
   RLTAC THEN
   ITAC DISJOINT_VISITED_BDS_EXTENDS_NOT_BD_RA_LEMMA THEN
   PAT_X_ASSUM “visited_bds'' = visited_bds1 ++ [start_bd_address]” (fn thm => ALL_TAC) THEN
   ITAC DISJOINT_VISITED_BDS_EXTENDS_NOT_BD_RA_LEMMA THEN
   IRTAC BDS_TO_FETCH_DISJOINT_TAIL_LEMMA THEN
   FAIRTAC THEN
   AXTAC THEN
   RLTAC THEN
   EQ_PAIR_ASM_TAC THEN
   STAC
  ]
 ]
]
QED

Theorem BDS_TO_FETCH_DISJOINT_NOT_BD_RA_TX_BDS_OF_TRANSFER_REC_CYCLIC_IMPLIES_F_LEMMA:
!bds memory registers start_bd_address visited_bds.
  BDS_TO_FETCH_DISJOINT bds /\
  NOT_BD_RA visited_bds bds /\
  (bds, NONE) = tx_bds_of_transfer_rec memory registers visited_bds start_bd_address
  ==>
  F
Proof
Induct THENL
[
 INTRO_TAC THEN PTAC tx_bds_of_transfer_rec THEN EQ_PAIR_ASM_TAC THEN TRY (IRTAC optionTheory.NOT_NONE_SOME ORELSE IRTAC listTheory.NOT_CONS_NIL) THEN STAC
 ,
 INTRO_TAC THEN
 ITAC BDS_TO_FETCH_DISJOINT_TAIL_LEMMA THEN
 PAT_X_ASSUM “!x.P” (fn thm => MATCH_MP_TAC thm) THEN
 ASM_REWRITE_TAC [] THEN
 WEAKEN_TAC (fn _ => true) THEN
 RW_HYP_LEMMA_TAC tx_bds_of_transfer_rec THEN
 IF_SPLIT_TAC THEN TRY (EQ_PAIR_ASM_TAC THEN IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC) THEN
 IF_SPLIT_TAC THEN LETS_TAC THENL
 [
  EQ_PAIR_ASM_TAC THEN
  ETAC listTheory.CONS_11 THEN
  NLRTAC 2 THEN
  IRTAC BD_ADDRESS_IN_GET_BD_RAS_LEMMA THEN
  ETAC NOT_BD_RA THEN
  RW_HYPS_TAC listTheory.MEM THEN
  RW_HYPS_TAC pairTheory.PAIR_EQ THEN
  AITAC THEN
  CONTR_ASMS_TAC
  ,
  IF_SPLIT_TAC THEN TRY (EQ_PAIR_ASM_TAC THEN IRTAC optionTheory.NOT_NONE_SOME THEN SOLVE_F_ASM_TAC) THEN
  EQ_PAIR_ASM_TAC THEN
  ETAC listTheory.CONS_11 THEN
  WEAKEN_TAC is_neg THEN
  NLRTAC 2 THEN
  RLTAC THEN
  IRTAC BD_ADDRESS_IN_GET_BD_RAS_LEMMA THEN
  IRTAC DISJOINT_VISITED_BDS_EXTENDS_NOT_BD_RA_LEMMA THEN
  PAXTAC THEN  
  STAC
 ]
]
QED

Theorem NO_BDS_TO_FETCH_NON_ZERO_START_BD_ADDRESS_IMPLIES_F_LEMMA:
!start_bd_address memory registers visited_bds visited_bds_option.
  start_bd_address <> 0w /\
  ([], visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds start_bd_address
  ==>
  F
Proof
INTRO_TAC THEN
PTAC tx_bds_of_transfer_rec THEN
 EQ_PAIR_ASM_TAC THEN IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
QED

Definition visited_tx_bds_to_fetch:
visited_tx_bds_to_fetch FBD_SOP endpoint_sop_li memory registers initially_visited_bds start_bd_address =
  let (first_packet_bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers initially_visited_bds start_bd_address in
    if NULL first_packet_bds then
      []
    else if IS_NONE visited_bds_option then
      first_packet_bds
    else
      let sop_li = if FBD_SOP then (SND o FST o FST) (HD first_packet_bds) else endpoint_sop_li in
        if li_to_eoq sop_li then
          first_packet_bds
        else
          let visited_bds = THE visited_bds_option in
          let next_sop_bd_address = li_to_next_bd_address registers sop_li in
            first_packet_bds ++ (tx_bds_of_transfers_rec memory registers visited_bds next_sop_bd_address)
End

Definition NOT_EOP_BD:
NOT_EOP_BD bd next_bd_address = (
  ~eop_bd bd /\
  next_bd_address = next_bd_pointer bd
)
End

Definition EOP_BD_NOT_SOP_NOT_EOQ:
EOP_BD_NOT_SOP_NOT_EOQ registers FBD_SOP endpoint_sop_li bd next_bd_address = (
  eop_bd bd /\
  ~FBD_SOP /\
  ~li_to_eoq endpoint_sop_li /\
  next_bd_address = li_to_next_bd_address registers endpoint_sop_li
)
End

Definition EOP_BD_SOP_NOT_EOQ:
EOP_BD_SOP_NOT_EOQ registers FBD_SOP bd li next_bd_address = (
  eop_bd bd /\
  FBD_SOP /\
  ~li_to_eoq li /\
  next_bd_address = li_to_next_bd_address registers li
)
End

Definition EOP_BD_NOT_SOP_EOQ:
EOP_BD_NOT_SOP_EOQ FBD_SOP endpoint_sop_li bd next_bd_address = (
  eop_bd bd /\
  ~FBD_SOP /\
  li_to_eoq endpoint_sop_li /\
  next_bd_address = 0w
)
End

Definition EOP_BD_SOP_EOQ:
EOP_BD_SOP_EOQ FBD_SOP bd li next_bd_address = (
  eop_bd bd /\
  FBD_SOP /\
  li_to_eoq li /\
  next_bd_address = 0w
)
End

Definition NOT_EOQ_BD:
NOT_EOQ_BD registers FBD_SOP endpoint_sop_li bd li next_bd_address = (
  EOP_BD_NOT_SOP_NOT_EOQ registers FBD_SOP endpoint_sop_li bd next_bd_address \/
  EOP_BD_SOP_NOT_EOQ registers FBD_SOP bd li next_bd_address
)
End

Definition EOQ_BD:
EOQ_BD FBD_SOP endpoint_sop_li bd li next_bd_address = (
  EOP_BD_NOT_SOP_EOQ FBD_SOP endpoint_sop_li bd next_bd_address \/
  EOP_BD_SOP_EOQ FBD_SOP bd li next_bd_address
)
End

Definition EOP_BD:
EOP_BD registers FBD_SOP endpoint_sop_li bd li next_bd_address = (
  NOT_EOQ_BD registers FBD_SOP endpoint_sop_li bd li next_bd_address \/
  EOQ_BD FBD_SOP endpoint_sop_li bd li next_bd_address
)
End

Theorem FIRST_PACKET_BDS_VISITED_TX_BDS_TO_FETCH_LEMMA:
!memory registers visited_bds start_bd_address bds FBD_SOP sop_li.
  bds = visited_tx_bds_to_fetch FBD_SOP sop_li memory registers visited_bds start_bd_address
  ==>
  ?remaining_bds first_packet_bds visited_bds_option.
    (first_packet_bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds start_bd_address /\
    bds = first_packet_bds ++ remaining_bds
Proof
INTRO_TAC THEN
PTAC visited_tx_bds_to_fetch THENL
[
 PAXTAC THEN ETAC listTheory.NULL_EQ THEN NLRTAC 2 THEN REWRITE_TAC [listTheory.APPEND] THEN EXISTS_EQ_TAC THEN STAC
 ,
 PAXTAC THEN LRTAC THEN Q.EXISTS_TAC ‘[]’ THEN ASM_REWRITE_TAC [listTheory.APPEND_NIL]
 ,
 PAXTAC THEN Q.EXISTS_TAC ‘[]’ THEN ASM_REWRITE_TAC [listTheory.APPEND_NIL]
 ,
 PAXTAC THEN LRTAC THEN EXISTS_EQ_TAC THEN STAC
]
QED

Theorem BDS_TO_FETCH_DISJOINT_NOT_BD_RA_TX_BDS_OF_TRANSFER_REC_NONE_IMPLIES_F_LEMMA:
!visited_bds bds visited_bds_option memory registers start_bd_address.
  BDS_TO_FETCH_DISJOINT bds /\
  NOT_BD_RA visited_bds bds /\
  IS_NONE visited_bds_option /\
  (bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds start_bd_address
  ==>
  F
Proof
INTRO_TAC THEN
PTAC optionTheory.IS_NONE_DEF THEN TRY STAC THEN
IRTAC BDS_TO_FETCH_DISJOINT_NOT_BD_RA_TX_BDS_OF_TRANSFER_REC_CYCLIC_IMPLIES_F_LEMMA THEN
STAC
QED

Theorem VISITED_TX_BDS_TO_FETCH_START_ZERO_EQ_EMPTY_LEMMA:
!queue_id memory internal_state visited_bds FBD_SOP endpoint_sop_li.
  visited_tx_bds_to_fetch FBD_SOP endpoint_sop_li memory internal_state visited_bds 0w = []
Proof
REPEAT GEN_TAC THEN
PTAC visited_tx_bds_to_fetch THEN TRY STAC THENL
[
 IRTAC TX_BDS_OF_TRANSFER_REC_ZERO_START_IMPLIES_EMPTY_BDS_LEMMA THEN STAC
 ,
 IRTAC TX_BDS_OF_TRANSFER_REC_ZERO_START_IMPLIES_EMPTY_BDS_LEMMA THEN STAC
 ,
 IRTAC TX_BDS_OF_TRANSFER_REC_ZERO_START_IMPLIES_EMPTY_BDS_LEMMA THEN LRTAC THEN PTAC listTheory.NULL_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC
]
QED

Theorem TX_BDS_OF_TRANSFER_REC_VISITED_TX_BDS_TO_FETCH_TAIL_EOP_EOQ_LEMMA:
!registers fbd bd li r w u bds visited_bds_option memory visited_bds start_bd_address FBD_SOP endpoint_sop_li sop_li.
  BDS_TO_FETCH_DISJOINT (fbd::bds) /\
  NOT_BD_RA visited_bds (fbd::bds) /\
  fbd = (((bd, li), r, w), u) /\
  (fbd::bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds start_bd_address /\
  sop_li = (if FBD_SOP then li else endpoint_sop_li) /\
  li_to_eoq sop_li /\
  eop_bd bd
  ==>
  bds = visited_tx_bds_to_fetch T sop_li memory registers (visited_bds ++ [start_bd_address]) 0w /\
  EOP_BD registers FBD_SOP endpoint_sop_li bd li 0w
Proof
INTRO_TAC THEN
PTAC tx_bds_of_transfer_rec THENL
[
 EQ_PAIR_ASM_TAC THEN IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
 ,
 IRTAC BD_ADDRESS_IN_GET_BD_RAS_LEMMA THEN
 EQ_PAIR_ASM_TAC THEN
 ETAC listTheory.CONS_11 THEN
 LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 5 THEN
 WEAKEN_TAC is_eq THEN
 LRTAC THEN
 ETAC NOT_BD_RA THEN
 RW_HYPS_TAC listTheory.MEM THEN
 RW_HYPS_TAC pairTheory.PAIR_EQ THEN
 FAIRTAC THEN
 CONTR_ASMS_TAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ETAC listTheory.CONS_11 THEN
 NLRTAC 2 THEN
 REWRITE_TAC [VISITED_TX_BDS_TO_FETCH_START_ZERO_EQ_EMPTY_LEMMA] THEN
 EQ_PAIR_ASM_TAC THEN
 LRTAC THEN
 ETAC EOP_BD THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 ETAC EOQ_BD THEN
 REWRITE_TAC [EOP_BD_NOT_SOP_EOQ, EOP_BD_SOP_EOQ] THEN
 IF_SPLIT_TAC THEN ALL_LRTAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ETAC listTheory.CONS_11 THEN
 NLRTAC 3 THEN
 WEAKEN_TAC (fn _ => true) THEN WEAKEN_TAC (fn _ => true) THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 5 THEN
 ETAC bbb_usb_functionsTheory.next_bd_pointer THEN
 CONTR_ASMS_TAC
]
QED

Theorem TX_BDS_OF_TRANSFER_REC_VISITED_TX_BDS_TO_FETCH_TAIL_NOT_EOP_EOQ_LEMMA:
!registers fbd bd li r w u bds visited_bds_option memory visited_bds start_bd_address sop_li next_bd_address.
  BDS_TO_FETCH_DISJOINT (fbd::bds) /\
  NOT_BD_RA visited_bds (fbd::bds) /\
  fbd = (((bd, li), r, w), u) /\
  (fbd::bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds start_bd_address /\
  li_to_eoq sop_li /\
  ~eop_bd bd /\
  next_bd_address = next_bd_pointer bd
  ==>
  bds = visited_tx_bds_to_fetch F sop_li memory registers (visited_bds ++ [start_bd_address]) next_bd_address /\
  NOT_EOP_BD bd next_bd_address
Proof
INTRO_TAC THEN
PTAC tx_bds_of_transfer_rec THENL
[
 EQ_PAIR_ASM_TAC THEN IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
 ,
 IRTAC BD_ADDRESS_IN_GET_BD_RAS_LEMMA THEN
 EQ_PAIR_ASM_TAC THEN
 ETAC listTheory.CONS_11 THEN
 LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 5 THEN
 WEAKEN_TAC (fn _ => true) THEN
 LRTAC THEN
 ETAC NOT_BD_RA THEN
 RW_HYPS_TAC listTheory.MEM THEN
 RW_HYPS_TAC pairTheory.PAIR_EQ THEN
 AIRTAC THEN
 CONTR_ASMS_TAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ETAC listTheory.CONS_11 THEN
 NLRTAC 2 THEN
 EQ_PAIR_ASM_TAC THEN
 LRTAC THEN
 ETAC bbb_usb_functionsTheory.eop_bd THEN
 ETAC bbb_usb_functionsTheory.next_bd_pointer THEN
 CONTR_ASMS_TAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ETAC listTheory.CONS_11 THEN
 NLRTAC 3 THEN
 PAT_X_ASSUM “x = y” (fn thm => ASSUME_TAC thm) THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 5 THEN
 ETAC NOT_EOP_BD THEN
 CONJS_TAC THEN TRY STAC THEN
 PAT_X_ASSUM “visited_bds' = visited_bds ++ [start_bd_address]” (fn thm => ASSUME_TAC thm) THEN
 RLTAC THEN
 RLTAC THEN
 LRTAC THEN
 ETAC visited_tx_bds_to_fetch THEN
 LETS_TAC THEN
 IF_SPLIT_TAC THEN TRY (ETAC listTheory.NULL_EQ THEN STAC) THEN
 IF_SPLIT_TAC THEN TRY STAC THEN
 ETAC boolTheory.bool_case_thm THEN
 LRTAC THEN
 STAC
]
QED

Theorem FIRST_PACKET_BDS_TAIL_LEMMA:
!fbd bds first_packet_bds remaining_bds.
  fbd::bds = first_packet_bds ++ remaining_bds /\
  ~NULL first_packet_bds
  ==>
  ?other_bds.
    first_packet_bds = fbd::other_bds
Proof
INTRO_TAC THEN
Cases_on ‘first_packet_bds’ THEN TRY (PTAC listTheory.NULL_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC) THEN
ETAC listTheory.APPEND THEN
ETAC listTheory.CONS_11 THEN
LRTAC THEN
EXISTS_EQ_TAC
QED

Theorem TX_BDS_OF_TRANSFER_REC_EOP_BD_IMPLIES_EMPTY_TAIL_LEMMA:
!fbd bd li r w u bds visited_bds_option memory registers visited_bds start_bd_address.
  BDS_TO_FETCH_DISJOINT (fbd::bds) /\
  NOT_BD_RA visited_bds (fbd::bds) /\
  fbd = (((bd, li), r, w), u) /\
  (fbd::bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds start_bd_address /\
  eop_bd bd
  ==>
  bds = [] /\
  visited_bds_option = SOME (visited_bds ++ [start_bd_address])
Proof
INTRO_TAC THEN
PTAC tx_bds_of_transfer_rec THENL
[
 EQ_PAIR_ASM_TAC THEN IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ETAC listTheory.CONS_11 THEN
 NLRTAC 3 THEN
 IRTAC BD_ADDRESS_IN_GET_BD_RAS_LEMMA THEN
 ETAC NOT_BD_RA THEN
 RW_HYPS_TAC listTheory.MEM THEN
 RW_HYPS_TAC pairTheory.PAIR_EQ THEN
 ALL_LRTAC THEN
 AITAC THEN
 CONTR_ASMS_TAC
 ,
 EQ_PAIR_ASM_TAC THEN ETAC listTheory.CONS_11 THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN ETAC listTheory.CONS_11 THEN LRTAC THEN EQ_PAIR_ASM_TAC THEN NRLTAC 5 THEN CONTR_ASMS_TAC
]
QED

Theorem TX_BDS_OF_TRANSFERS_REC_EQ_VISITED_TX_BDS_TO_FETCH_SOP_LEMMA:
!memory registers visited_bds sop_bd_address sop_li bds1 bds2.
  tx_bds_of_transfers_rec memory registers visited_bds sop_bd_address =
  visited_tx_bds_to_fetch T sop_li memory registers visited_bds sop_bd_address
Proof
REPEAT GEN_TAC THEN
PTAC tx_bds_of_transfers_rec THEN PTAC visited_tx_bds_to_fetch THEN TRY STAC THENL
[
 IRTAC TX_BDS_OF_TRANSFER_REC_ZERO_START_IMPLIES_EMPTY_BDS_LEMMA THEN STAC
 ,
 IRTAC TX_BDS_OF_TRANSFER_REC_ZERO_START_IMPLIES_EMPTY_BDS_LEMMA THEN STAC
 ,
 IRTAC TX_BDS_OF_TRANSFER_REC_ZERO_START_IMPLIES_EMPTY_BDS_LEMMA THEN LRTAC THEN PTAC listTheory.NULL_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC
 ,
 ETAC boolTheory.bool_case_thm THEN ETAC combinTheory.o_THM THEN RLTAC THEN RLTAC THEN CONTR_ASMS_TAC
 ,
 ETAC boolTheory.bool_case_thm THEN ETAC combinTheory.o_THM THEN RLTAC THEN RLTAC THEN CONTR_ASMS_TAC
 ,
 ETAC boolTheory.bool_case_thm THEN ETAC combinTheory.o_THM THEN RLTAC THEN RLTAC THEN RLTAC THEN STAC
]
QED

Theorem TX_BDS_OF_TRANSFER_REC_VISITED_TX_BDS_TO_FETCH_TAIL_EOP_NOT_EOQ_LEMMA:
!registers fbd bd li r w u bds visited_bds_option memory visited_bds start_bd_address sop_li next_sop_bd_address remaining_bds visited_bds' FBD_SOP endpoint_sop_li.
  BDS_TO_FETCH_DISJOINT (fbd::bds) /\
  NOT_BD_RA visited_bds (fbd::bds) /\
  fbd = (((bd, li), r, w), u) /\
  (fbd::bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds start_bd_address /\
  sop_li = (if FBD_SOP then li else endpoint_sop_li) /\
  ~li_to_eoq sop_li /\
  eop_bd bd /\
  next_sop_bd_address = li_to_next_bd_address registers sop_li /\
  ~IS_NONE visited_bds_option /\
  visited_bds' = THE visited_bds_option /\
  remaining_bds = tx_bds_of_transfers_rec memory registers visited_bds' next_sop_bd_address
  ==>
  bds ++ remaining_bds = visited_tx_bds_to_fetch T sop_li memory registers (visited_bds ++ [start_bd_address]) next_sop_bd_address /\
  EOP_BD registers FBD_SOP endpoint_sop_li bd li next_sop_bd_address
Proof
INTRO_TAC THEN
ITAC TX_BDS_OF_TRANSFER_REC_EOP_BD_IMPLIES_EMPTY_TAIL_LEMMA THEN
LRTAC THEN
ETAC listTheory.APPEND THEN
LRTAC THEN
ETAC optionTheory.THE_DEF THEN
LRTAC THEN
ETAC TX_BDS_OF_TRANSFERS_REC_EQ_VISITED_TX_BDS_TO_FETCH_SOP_LEMMA THEN
CONJS_TAC THEN TRY STAC THEN
ETAC EOP_BD THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
IF_SPLIT_TAC THENL
[
 ETAC NOT_EOQ_BD THEN MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN ETAC EOP_BD_SOP_NOT_EOQ THEN STAC
 ,
 ETAC NOT_EOQ_BD THEN MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN ETAC EOP_BD_NOT_SOP_NOT_EOQ THEN STAC
]
QED

Theorem NOT_ZERO_START_IMPLIES_TX_BDS_OF_TRANSFER_REC_NULL_F_LEMMA:
!bd_address first_packet_bds visited_bds_option memory registers visited_bds.
  bd_address <> 0w /\
  (first_packet_bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds bd_address /\
  NULL first_packet_bds
  ==>
  F
Proof
INTRO_TAC THEN
ETAC listTheory.NULL_EQ THEN
LRTAC THEN
PTAC tx_bds_of_transfer_rec THEN
 EQ_PAIR_ASM_TAC THEN IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
QED

Theorem TX_BDS_OF_TRANSFER_REC_VISITED_TX_BDS_TO_FETCH_TAIL_NOT_EOP_NOT_EOQ_LEMMA:
!registers fbd bd li r w u bds visited_bds_option memory visited_bds start_bd_address sop_li next_bd_address next_sop_bd_address remaining_bds visited_bds'.
  BDS_TO_FETCH_DISJOINT (fbd::bds) /\
  NOT_BD_RA visited_bds (fbd::bds) /\
  fbd = (((bd, li), r, w), u) /\
  (fbd::bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds start_bd_address /\
  ~li_to_eoq sop_li /\
  ~eop_bd bd /\
  next_bd_address = next_bd_pointer bd /\
  next_sop_bd_address = li_to_next_bd_address registers sop_li /\
  ~IS_NONE visited_bds_option /\
  visited_bds' = THE visited_bds_option /\
  remaining_bds = tx_bds_of_transfers_rec memory registers visited_bds' next_sop_bd_address
  ==>
  bds ++ remaining_bds = visited_tx_bds_to_fetch F sop_li memory registers (visited_bds ++ [start_bd_address]) next_bd_address /\
  NOT_EOP_BD bd next_bd_address
Proof
INTRO_TAC THEN
PTAC tx_bds_of_transfer_rec THENL
[
 EQ_PAIR_ASM_TAC THEN IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
 ,
 EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN ETAC optionTheory.IS_NONE_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ETAC listTheory.CONS_11 THEN
 NLRTAC 3 THEN
 ETAC listTheory.APPEND THEN
 ETAC optionTheory.THE_DEF THEN
 LRTAC THEN
 LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 WEAKEN_TAC (fn _ => true) THEN WEAKEN_TAC (fn _ => true) THEN WEAKEN_TAC (fn _ => true) THEN
 NRLTAC 5 THEN
 CONTR_ASMS_TAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ETAC listTheory.CONS_11 THEN
 NLRTAC 3 THEN
 WEAKEN_TAC is_neg THEN
 PAT_X_ASSUM “(((bd',li'),bd_ras,bd_ras),no_update) = (((bd,li),r,w),u)” (fn thm => ASSUME_TAC thm) THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 5 THEN
 PTAC visited_tx_bds_to_fetch THENL
 [
  ETAC bbb_usb_functionsTheory.eop_bd THEN ETAC bbb_usb_functionsTheory.next_bd_pointer THEN FIRTAC NOT_ZERO_START_IMPLIES_TX_BDS_OF_TRANSFER_REC_NULL_F_LEMMA THEN SOLVE_F_ASM_TAC
  ,
  PAT_X_ASSUM “visited_bds'' = visited_bds ++ [start_bd_address]” (fn thm => ASSUME_TAC thm) THEN
  LRTAC THEN
  REPEAT (WEAKEN_TAC is_neg) THEN
  ASM_RL_RW_OTHERS_KEEP_TAC THEN RLTAC THEN
  ASM_LR_RW_OTHERS_KEEP_TAC THEN EQ_PAIR_ASM_TAC THEN NRLTAC 2 THEN
  IRTAC BD_ADDRESS_IN_GET_BD_RAS_LEMMA THEN
  ITAC DISJOINT_VISITED_BDS_EXTENDS_NOT_BD_RA_LEMMA THEN
  IRTAC BDS_TO_FETCH_DISJOINT_TAIL_LEMMA THEN
  IRTAC BDS_TO_FETCH_DISJOINT_NOT_BD_RA_TX_BDS_OF_TRANSFER_REC_NONE_IMPLIES_F_LEMMA THEN
  SOLVE_F_ASM_TAC
  ,
  ETAC boolTheory.bool_case_thm THEN LRTAC THEN CONTR_ASMS_TAC
  ,
  ETAC boolTheory.bool_case_thm THEN RLTAC THEN
  RLTAC THEN RLTAC THEN
  WEAKEN_TAC is_neg THEN
  PAT_X_ASSUM “~eop_bd bd'” (fn _ => ALL_TAC) THEN
  ASM_RL_RW_OTHERS_KEEP_TAC THEN RLTAC THEN
  PAT_X_ASSUM “visited_bds'³' = THE visited_bds_option” (fn thm => ASSUME_TAC thm) THEN
  PAT_X_ASSUM “visited_bds' = THE visited_bds_option'” (fn thm => ASSUME_TAC thm) THEN
  PAT_X_ASSUM “visited_bds'' = visited_bds ++ [start_bd_address]” (fn thm => ASSUME_TAC thm) THEN
  RLTAC THEN LRTAC THEN EQ_PAIR_ASM_TAC THEN NRLTAC 2 THEN
  ETAC listTheory.APPEND_11 THEN
  LRTAC THEN
  LRTAC THEN
  LRTAC THEN
  REWRITE_TAC [] THEN
  ETAC NOT_EOP_BD THEN
  STAC
 ]
]
QED

Theorem VISITED_TX_BDS_TO_FETCH_TAIL_CASES_LEMMA:
!registers memory visited_bds bd li r w u fbd bds start_bd_address sop_li FBD_SOP endpoint_sop_li.
  BDS_TO_FETCH_DISJOINT (fbd::bds) /\
  NOT_BD_RA visited_bds (fbd::bds) /\
  fbd = (((bd, li), r, w), u) /\
  fbd::bds = visited_tx_bds_to_fetch FBD_SOP endpoint_sop_li memory registers visited_bds start_bd_address /\
  sop_li = (if FBD_SOP then li else endpoint_sop_li)
  ==>
  ?next_bd_address.
    (NOT_EOP_BD bd next_bd_address /\
     bds = visited_tx_bds_to_fetch F sop_li memory registers (visited_bds ++ [start_bd_address]) next_bd_address) \/
    (EOP_BD registers FBD_SOP endpoint_sop_li bd li next_bd_address /\
     bds = visited_tx_bds_to_fetch T sop_li memory registers (visited_bds ++ [start_bd_address]) next_bd_address)
Proof
INTRO_TAC THEN
ITAC FIRST_PACKET_BDS_VISITED_TX_BDS_TO_FETCH_LEMMA THEN
AXTAC THEN
ASM_LR_RW_OTHERS_KEEP_TAC THEN
IRTAC BDS_TO_FETCH_DISJOINT_APPEND_LEMMA THEN
IRTAC NOT_BD_RA_APPEND_LEMMA THEN
ETAC visited_tx_bds_to_fetch THEN
LETS_TAC THEN
IF_SPLIT_TAC THEN TRY (IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC) THEN
IF_SPLIT_TAC THEN TRY (IRTAC BDS_TO_FETCH_DISJOINT_NOT_BD_RA_TX_BDS_OF_TRANSFER_REC_NONE_IMPLIES_F_LEMMA THEN SOLVE_F_ASM_TAC) THEN
IF_SPLIT_TAC THENL
[
 ETAC listTheory.APPEND_EQ_SELF THEN
 LRTAC THEN
 ETAC listTheory.APPEND_NIL THEN
 RLTAC THEN
 ETAC listTheory.HD THEN
 PAT_X_ASSUM “fbd = (((bd,li),r,w),u)” (fn thm => ASSUME_TAC thm) THEN
 LRTAC THEN
 ETAC combinTheory.o_THM THEN
 ETAC pairTheory.FST THEN
 ETAC pairTheory.SND THEN
 REPEAT (WEAKEN_TAC is_neg) THEN
 ASM_RL_RW_OTHERS_KEEP_TAC THEN
 RLTAC THEN
 WEAKEN_TAC is_eq THEN
 Cases_on ‘eop_bd bd’ THENL
 [
  Q.EXISTS_TAC ‘0w’ THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  ONCE_REWRITE_TAC [boolTheory.CONJ_COMM] THEN
  MATCH_MP_TAC TX_BDS_OF_TRANSFER_REC_VISITED_TX_BDS_TO_FETCH_TAIL_EOP_EOQ_LEMMA THEN
  PAXTAC THEN
  STAC
  ,
  Q.EXISTS_TAC ‘next_bd_pointer bd’ THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
  ONCE_REWRITE_TAC [boolTheory.CONJ_COMM] THEN
  MATCH_MP_TAC TX_BDS_OF_TRANSFER_REC_VISITED_TX_BDS_TO_FETCH_TAIL_NOT_EOP_EOQ_LEMMA THEN
  PAXTAC THEN
  STAC
 ]
 ,
 ITAC FIRST_PACKET_BDS_TAIL_LEMMA THEN
 AXTAC THEN
 LRTAC THEN
 ETAC listTheory.APPEND THEN
 ETAC listTheory.CONS_11 THEN
 WEAKEN_TAC is_eq THEN
 LRTAC THEN
 ETAC listTheory.APPEND_11 THEN
 ETAC listTheory.HD THEN
 PAT_X_ASSUM “fbd = (((bd,li),r,w),u)” (fn thm => ASSUME_TAC thm) THEN
 LRTAC THEN
 ETAC combinTheory.o_THM THEN
 ETAC pairTheory.FST THEN
 ETAC pairTheory.SND THEN
 ASM_RL_RW_OTHERS_KEEP_TAC THEN
 LRTAC THEN
 ASM_RL_RW_OTHERS_KEEP_TAC THEN
 Cases_on ‘eop_bd bd’ THENL
 [
  Q.EXISTS_TAC ‘next_sop_bd_address’ THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  ONCE_REWRITE_TAC [boolTheory.CONJ_COMM] THEN
  MATCH_MP_TAC TX_BDS_OF_TRANSFER_REC_VISITED_TX_BDS_TO_FETCH_TAIL_EOP_NOT_EOQ_LEMMA THEN
  PAXTAC THEN
  STAC
  ,
  Q.EXISTS_TAC ‘next_bd_pointer bd’ THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
  ONCE_REWRITE_TAC [boolTheory.CONJ_COMM] THEN
  MATCH_MP_TAC TX_BDS_OF_TRANSFER_REC_VISITED_TX_BDS_TO_FETCH_TAIL_NOT_EOP_NOT_EOQ_LEMMA THEN
  PAXTAC THEN
  STAC
 ]
]
QED

Theorem TX_BDS_OF_TRANSFER_REC_BD_ADDRESS_R_LEMMA:
!memory registers visited_bds bd_address fbd bd li r w u bds visited_bds_option.
  BDS_TO_FETCH_DISJOINT (fbd::bds) /\
  NOT_BD_RA visited_bds (fbd::bds) /\
  fbd = (((bd, li), r, w), u) /\
  (fbd::bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds bd_address
  ==>
  MEM bd_address r
Proof
INTRO_TAC THEN
PTAC tx_bds_of_transfer_rec THEN EQ_PAIR_ASM_TAC THENL
[
 IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
 ,
 IRTAC BD_ADDRESS_IN_GET_BD_RAS_LEMMA THEN ETAC listTheory.CONS_11 THEN LRTAC THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 IRTAC BD_ADDRESS_IN_GET_BD_RAS_LEMMA THEN ETAC listTheory.CONS_11 THEN LRTAC THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 IRTAC BD_ADDRESS_IN_GET_BD_RAS_LEMMA THEN ETAC listTheory.CONS_11 THEN LRTAC THEN EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem VISITED_TX_BDS_TO_FETCH_BD_ADDRESS_R_LEMMA:
!FBD_SOP endpoint_sop_li memory registers visited_bds bd_address fbd bd li r w u bds.
  BDS_TO_FETCH_DISJOINT (fbd::bds) /\
  NOT_BD_RA visited_bds (fbd::bds) /\
  fbd = (((bd, li), r, w), u) /\
  fbd::bds = visited_tx_bds_to_fetch FBD_SOP endpoint_sop_li memory registers visited_bds bd_address
  ==>
  MEM bd_address r
Proof
INTRO_TAC THEN
PTAC visited_tx_bds_to_fetch THENL
[
 IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
 ,
 IRTAC BDS_TO_FETCH_DISJOINT_NOT_BD_RA_TX_BDS_OF_TRANSFER_REC_NONE_IMPLIES_F_LEMMA THEN SOLVE_F_ASM_TAC
 ,
 IRTAC TX_BDS_OF_TRANSFER_REC_BD_ADDRESS_R_LEMMA THEN STAC
 ,
 Cases_on ‘first_packet_bds’ THEN TRY (ETAC listTheory.NULL_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC) THEN
 ETAC listTheory.APPEND THEN
 ETAC listTheory.CONS_11 THEN
 RLTAC THEN
 LRTAC THEN
 WEAKEN_TAC is_neg THEN WEAKEN_TAC is_eq THEN
 LRTAC THEN
 ETAC (CONJUNCT2 listTheory.APPEND) THEN
 IRTAC BDS_TO_FETCH_DISJOINT_APPEND_LEMMA THEN
 IRTAC NOT_BD_RA_APPEND_LEMMA THEN
 IRTAC TX_BDS_OF_TRANSFER_REC_BD_ADDRESS_R_LEMMA THEN
 STAC
]
QED

Theorem TX_BDS_OF_TRANSFER_REC_FBD_LEMMA:
!bd li r w u bds visited_bds_option memory registers visited_bds start_bd_address.
  ((((bd, li), r, w), u)::bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds start_bd_address
  ==>
  start_bd_address <> 0w /\
  r = get_bd_ras registers start_bd_address /\
  w = r /\
  (bd, li) = form_bd_li (MAP memory r)   
Proof
INTRO_TAC THEN
PTAC tx_bds_of_transfer_rec THEN EQ_PAIR_ASM_TAC THENL
[
 IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
 ,
 ETAC listTheory.CONS_11 THEN EQ_PAIR_ASM_TAC THEN NLRTAC 6 THEN STAC
 ,
 ETAC listTheory.CONS_11 THEN EQ_PAIR_ASM_TAC THEN NLRTAC 6 THEN STAC
 ,
 ETAC listTheory.CONS_11 THEN EQ_PAIR_ASM_TAC THEN NLRTAC 7 THEN STAC
]
QED

Theorem VISITED_TX_BDS_TO_FETCH_FBD_LEMMA:
!bd li r w u bds FBD_SOP endpoint_sop_li memory registers visited_bds start_bd_address.
  (((bd, li), r, w), u)::bds = visited_tx_bds_to_fetch FBD_SOP endpoint_sop_li memory registers visited_bds start_bd_address
  ==>
  start_bd_address <> 0w /\
  r = get_bd_ras registers start_bd_address /\
  w = r /\
  (bd, li) = form_bd_li (MAP memory r)
Proof
INTRO_TAC THEN
PTAC visited_tx_bds_to_fetch THENL
[
 IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
 ,
 IRTAC TX_BDS_OF_TRANSFER_REC_FBD_LEMMA THEN STAC
 ,
 IRTAC TX_BDS_OF_TRANSFER_REC_FBD_LEMMA THEN STAC
 ,
 Cases_on ‘first_packet_bds’ THEN TRY (ETAC listTheory.NULL_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC) THEN
 ETAC listTheory.APPEND THEN
 ETAC listTheory.CONS_11 THEN
 IRTAC TX_BDS_OF_TRANSFER_REC_FBD_LEMMA THEN
 STAC
]
QED

Theorem TX_BDS_OF_TRANSFER_REC_FBD_NO_UPDATE_LEMMA:
!memory registers visited_bds start_bd_address fbd bds visited_bds_option.
  (fbd::bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds start_bd_address
  ==>
  ?bd li r.
    fbd = (((bd, li), r, r), no_update)
Proof
INTRO_TAC THEN
PTAC tx_bds_of_transfer_rec THEN EQ_PAIR_ASM_TAC THENL
[
 IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
 ,
 ETAC listTheory.CONS_11 THEN LRTAC THEN EXISTS_EQ_TAC
 ,
 ETAC listTheory.CONS_11 THEN LRTAC THEN EXISTS_EQ_TAC
 ,
 ETAC listTheory.CONS_11 THEN LRTAC THEN EXISTS_EQ_TAC
]
QED

Theorem VISITED_TX_BDS_TO_FETCH_FBD_NO_UPDATE_LEMMA:
!FBD_SOP endpoint_sop_li memory registers visited_bds start_bd_address fbd bds.
  fbd::bds = visited_tx_bds_to_fetch FBD_SOP endpoint_sop_li memory registers visited_bds start_bd_address
  ==>
  ?bd li r.
    fbd = (((bd, li), r, r), no_update)
Proof
INTRO_TAC THEN
PTAC visited_tx_bds_to_fetch THENL
[
 IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
 ,
 IRTAC TX_BDS_OF_TRANSFER_REC_FBD_NO_UPDATE_LEMMA THEN STAC
 ,
 IRTAC TX_BDS_OF_TRANSFER_REC_FBD_NO_UPDATE_LEMMA THEN STAC
 ,
 PTAC listTheory.NULL_DEF THEN TRY (ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC) THEN
 LRTAC THEN
 ETAC listTheory.APPEND THEN
 ETAC listTheory.CONS_11 THEN
 IRTAC TX_BDS_OF_TRANSFER_REC_FBD_NO_UPDATE_LEMMA THEN
 STAC
]
QED

Theorem TX_BDS_OF_TRANSER_REC_NOT_EOP_BD_TAIL_LEMMA:
!start_bd_address r registers bd li memory fbd visited_bds next_bd_address first_packet_bds visited_bds_option.
  start_bd_address <> 0w /\
  r = get_bd_ras registers start_bd_address /\
  (bd, li) = form_bd_li (MAP memory r) /\
  fbd = (((bd, li), r, r), no_update) /\
  NOT_BD_RA visited_bds [fbd] /\
  NOT_EOP_BD bd next_bd_address /\
  (first_packet_bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds start_bd_address
  ==>
  ?bds.
    first_packet_bds = fbd::bds /\
    (bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers (visited_bds ++ [start_bd_address]) next_bd_address
Proof
INTRO_TAC THEN
RW_HYP_LEMMA_TAC tx_bds_of_transfer_rec THEN
IF_SPLIT_TAC THEN TRY CONTR_ASMS_TAC THEN
IF_SPLIT_TAC THEN TRY (IRTAC BD_ADDRESS_IN_GET_BD_RAS_LEMMA THEN ETAC NOT_BD_RA THEN RW_HYPS_TAC listTheory.MEM THEN AITAC THEN CONTR_ASMS_TAC) THEN
LETS_TAC THEN
PAT_X_ASSUM “bd_bytes = MAP memory r” (fn thm => ASSUME_TAC thm) THEN
RLTAC THEN
RLTAC THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 2 THEN
IF_SPLIT_TAC THEN TRY (ETAC NOT_EOP_BD THEN CONTR_ASMS_TAC) THEN
EQ_PAIR_ASM_TAC THEN
REPEAT (WEAKEN_TAC is_neg) THEN
LRTAC THEN
ASM_REWRITE_TAC [listTheory.CONS_11] THEN
ETAC NOT_EOP_BD THEN
RLTAC THEN
RLTAC THEN
RLTAC THEN
LRTAC THEN
LRTAC THEN
EXISTS_EQ_TAC
QED

Theorem VISITED_TX_BDS_TO_FETCH_ADD_NOT_EOP_BD_LEMMA:
!registers memory visited_bds bd li r fbd bds start_bd_address sop_li FBD_SOP endpoint_sop_li next_bd_address.
  BDS_TO_FETCH_DISJOINT (fbd::bds) /\
  NOT_BD_RA visited_bds (fbd::bds) /\
  start_bd_address <> 0w /\
  fbd = (((bd, li), r, r), no_update) /\
  r = get_bd_ras registers start_bd_address /\
  (bd, li) = form_bd_li (MAP memory r) /\
  sop_li = (if FBD_SOP then li else endpoint_sop_li) /\
  NOT_EOP_BD bd next_bd_address /\
  bds = visited_tx_bds_to_fetch F sop_li memory registers (visited_bds ++ [start_bd_address]) next_bd_address
  ==>
  fbd::bds = visited_tx_bds_to_fetch FBD_SOP endpoint_sop_li memory registers visited_bds start_bd_address
Proof
INTRO_TAC THEN
PTAC visited_tx_bds_to_fetch THENL
[
 IRTAC NOT_ZERO_START_IMPLIES_TX_BDS_OF_TRANSFER_REC_NULL_F_LEMMA THEN SOLVE_F_ASM_TAC
 ,
 IRTAC NOT_BD_RA_HD_TL_LEMMA THEN
 IRTAC TX_BDS_OF_TRANSER_REC_NOT_EOP_BD_TAIL_LEMMA THEN
 AXTAC THEN
 LRTAC THEN
 REWRITE_TAC [listTheory.CONS_11] THEN
 PTAC visited_tx_bds_to_fetch THEN TRY STAC THEN ETAC listTheory.NULL_EQ THEN STAC
 ,
 IRTAC NOT_BD_RA_HD_TL_LEMMA THEN
 ITAC TX_BDS_OF_TRANSER_REC_NOT_EOP_BD_TAIL_LEMMA THEN
 AXTAC THEN
 LRTAC THEN
 REWRITE_TAC [listTheory.CONS_11] THEN
 PTAC visited_tx_bds_to_fetch THEN TRY (STAC ORELSE ETAC listTheory.NULL_EQ THEN STAC) THEN
 ETAC boolTheory.bool_case_thm THEN
 IF_SPLIT_TAC THENL
 [
  WEAKEN_TAC (fn _ => true) THEN WEAKEN_TAC (fn _ => true) THEN WEAKEN_TAC (fn _ => true) THEN WEAKEN_TAC (fn _ => true) THEN
  LRTAC THEN
  ETAC listTheory.HD THEN ETAC combinTheory.o_THM THEN PAT_X_ASSUM “fbd = (((bd,li),r,r),no_update)” (fn thm => ASSUME_TAC thm) THEN
  LRTAC THEN ETAC pairTheory.FST THEN ETAC pairTheory.SND THEN LRTAC THEN ALL_LRTAC THEN CONTR_ASMS_TAC
  ,
  WEAKEN_TAC (fn _ => true) THEN WEAKEN_TAC (fn _ => true) THEN WEAKEN_TAC (fn _ => true) THEN WEAKEN_TAC (fn _ => true) THEN
  LRTAC THEN ALL_LRTAC THEN CONTR_ASMS_TAC
 ]
 ,
 IRTAC NOT_BD_RA_HD_TL_LEMMA THEN
 ITAC TX_BDS_OF_TRANSER_REC_NOT_EOP_BD_TAIL_LEMMA THEN
 AXTAC THEN
 LRTAC THEN
 REWRITE_TAC [listTheory.APPEND, listTheory.CONS_11] THEN
 PTAC visited_tx_bds_to_fetch THENL
 [
  ETAC listTheory.NULL_EQ THEN NLRTAC 2 THEN
  PTAC NOT_EOP_BD THEN
  ETAC bbb_usb_functionsTheory.eop_bd THEN
  ETAC bbb_usb_functionsTheory.next_bd_pointer THEN
  RLTAC THEN
  IRTAC NO_BDS_TO_FETCH_NON_ZERO_START_BD_ADDRESS_IMPLIES_F_LEMMA THEN
  SOLVE_F_ASM_TAC
  ,
  ETAC boolTheory.bool_case_thm THEN
  RLTAC THEN
  IF_SPLIT_TAC THENL
  [
   ETAC listTheory.HD THEN ETAC combinTheory.o_THM THEN PAT_X_ASSUM “fbd = (((bd,li),r,r),no_update)” (fn thm => ASSUME_TAC thm) THEN
   LRTAC THEN ETAC pairTheory.FST THEN ETAC pairTheory.SND THEN ALL_LRTAC THEN CONTR_ASMS_TAC
   ,
   ALL_LRTAC THEN CONTR_ASMS_TAC
  ]
  ,
  ETAC boolTheory.bool_case_thm THEN
  LRTAC THEN
  WEAKEN_TAC (fn _ => true) THEN WEAKEN_TAC (fn _ => true) THEN
  LRTAC THEN
  WEAKEN_TAC (fn _ => true) THEN
  LRTAC THEN
  ETAC listTheory.HD THEN ETAC combinTheory.o_THM THEN PAT_X_ASSUM “fbd = (((bd,li),r,r),no_update)” (fn thm => ASSUME_TAC thm) THEN
  LRTAC THEN
  IF_SPLIT_TAC THEN TRY STAC THEN
  ETAC pairTheory.FST THEN ETAC pairTheory.SND THEN LRTAC THEN STAC
 ]
]
QED

Theorem EOP_BD_IMPLIES_EOP_LEMMA:
!registers FBD_SOP endpoint_sop_li bd li next_bd_address.
  EOP_BD registers FBD_SOP endpoint_sop_li bd li next_bd_address
  ==>
  eop_bd bd
Proof
INTRO_TAC THEN
ETAC EOP_BD THEN
SPLIT_ASM_DISJS_TAC THENL
[
 ETAC NOT_EOQ_BD THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  ETAC EOP_BD_NOT_SOP_NOT_EOQ THEN STAC
  ,
  ETAC EOP_BD_SOP_NOT_EOQ THEN STAC
 ]
 ,
 ETAC EOQ_BD THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  ETAC EOP_BD_NOT_SOP_EOQ THEN STAC
  ,
  ETAC EOP_BD_SOP_EOQ THEN STAC
 ]
]
QED

Theorem EOP_BD_TX_TRANSFER_REC_NONE_IMPLIES_F_LEMMA:
!visited_bds fbd start_bd_address registers r bd li memory first_packet_bds visited_bds_option FBD_SOP endpoint_sop_li next_bd_address.
  NOT_BD_RA visited_bds [fbd] /\
  start_bd_address <> 0w /\
  r = get_bd_ras registers start_bd_address /\
  (bd, li) = form_bd_li (MAP memory r) /\
  fbd = (((bd, li), r, r), no_update) /\
  EOP_BD registers FBD_SOP endpoint_sop_li bd li next_bd_address /\
  (first_packet_bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds start_bd_address /\
  IS_NONE visited_bds_option
  ==>
  F
Proof
INTRO_TAC THEN
PTAC tx_bds_of_transfer_rec THENL
[
 IRTAC BD_ADDRESS_IN_GET_BD_RAS_LEMMA THEN ETAC NOT_BD_RA THEN RW_HYPS_TAC listTheory.MEM THEN AITAC THEN CONTR_ASMS_TAC
 ,
 EQ_PAIR_ASM_TAC THEN LRTAC THEN ETAC optionTheory.IS_NONE_DEF THEN STAC
 ,
 WEAKEN_TAC (fn _ => true) THEN WEAKEN_TAC (fn _ => true) THEN
 RLTAC THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN NRLTAC 2 THEN
 IRTAC EOP_BD_IMPLIES_EOP_LEMMA THEN
 CONTR_ASMS_TAC
]
QED

Theorem EOP_FBD_TX_TRANSFER_REC_NOT_NONE_IMPLIES_EMPTY_TAIL_LEMMA:
!visited_bds fbd bds start_bd_address registers r w bd li memory visited_bds_option.
  fbd = (((bd, li), r, w), no_update) /\
  eop_bd bd /\
  (fbd::bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds start_bd_address /\
  ~IS_NONE visited_bds_option
  ==>
  bds = []
Proof
INTRO_TAC THEN
PTAC tx_bds_of_transfer_rec THENL
[
 EQ_PAIR_ASM_TAC THEN IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
 ,
 EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN ETAC optionTheory.IS_NONE_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC
 ,
 EQ_PAIR_ASM_TAC THEN ETAC listTheory.CONS_11 THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ETAC listTheory.CONS_11 THEN
 LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 LRTAC THEN
 CONTR_ASMS_TAC
]
QED

Theorem EOP_BD_TX_TRANSFER_REC_NOT_NONE_IMPLIES_FBD_LEMMA:
!visited_bds fbd start_bd_address registers r bd li memory first_packet_bds visited_bds_option FBD_SOP endpoint_sop_li next_bd_address.
  start_bd_address <> 0w /\
  r = get_bd_ras registers start_bd_address /\
  (bd, li) = form_bd_li (MAP memory r) /\
  fbd = (((bd, li), r, r), no_update) /\
  EOP_BD registers FBD_SOP endpoint_sop_li bd li next_bd_address /\
  (first_packet_bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds start_bd_address /\
  ~IS_NONE visited_bds_option
  ==>
  first_packet_bds = [fbd]
Proof
INTRO_TAC THEN
PTAC tx_bds_of_transfer_rec THENL
[
 EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN ETAC optionTheory.IS_NONE_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC
 ,
 EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN STAC
 ,
 PAT_X_ASSUM “bd_bytes = MAP memory r” (fn thm => ASSUME_TAC thm) THEN
 RLTAC THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN NRLTAC 2 THEN
 IRTAC EOP_BD_IMPLIES_EOP_LEMMA THEN
 CONTR_ASMS_TAC
]
QED

Theorem EOP_BD_EOQ_IMPLIES_NEXT_BD_ADDRESS_ZERO_LEMMA:
!registers FBD_SOP endpoint_sop_li bd li next_bd_address sop_li.
  sop_li = (if FBD_SOP then li else endpoint_sop_li) /\
  li_to_eoq sop_li /\
  EOP_BD registers FBD_SOP endpoint_sop_li bd li next_bd_address
  ==>
  next_bd_address = 0w
Proof
INTRO_TAC THEN
ETAC EOP_BD THEN
ETAC NOT_EOQ_BD THEN ETAC EOQ_BD THEN
ETAC EOP_BD_NOT_SOP_NOT_EOQ THEN ETAC EOP_BD_SOP_NOT_EOQ THEN ETAC EOP_BD_NOT_SOP_EOQ THEN ETAC EOP_BD_SOP_EOQ THEN
IF_SPLIT_TAC THEN LRTAC THEN SPLIT_ASM_DISJS_TAC THEN TRY CONTR_ASMS_TAC THEN STAC
QED

Theorem EOP_BD_NOT_EOQ_IMPLIES_NEXT_BD_ADDRESS_ZERO_LEMMA:
!sop_li FBD_SOP li endpoint_sop_li bd next_bd_address registers.
  sop_li = (if FBD_SOP then li else endpoint_sop_li) /\
  ~li_to_eoq sop_li /\
  EOP_BD registers FBD_SOP endpoint_sop_li bd li next_bd_address
  ==>
  next_bd_address = li_to_next_bd_address registers sop_li
Proof
INTRO_TAC THEN
ETAC EOP_BD THEN
ETAC NOT_EOQ_BD THEN ETAC EOQ_BD THEN
ETAC EOP_BD_NOT_SOP_NOT_EOQ THEN ETAC EOP_BD_SOP_NOT_EOQ THEN ETAC EOP_BD_NOT_SOP_EOQ THEN ETAC EOP_BD_SOP_EOQ THEN
IF_SPLIT_TAC THEN LRTAC THEN SPLIT_ASM_DISJS_TAC THEN TRY CONTR_ASMS_TAC THEN STAC
QED

Theorem EOP_BD_TX_BDS_OF_TRANSFER_REC_VISITED_BDS_ADDED_START_BD_ADDRESS_LEMMA:
!start_bd_address visited_bds_option bd li r memory registers visited_bds.
  ~IS_NONE visited_bds_option /\
  eop_bd bd /\
  ([(((bd, li), r, r), no_update)], visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds start_bd_address
  ==>
  visited_bds_option = SOME (visited_bds ++ [start_bd_address])
Proof
INTRO_TAC THEN
PTAC tx_bds_of_transfer_rec THEN EQ_PAIR_ASM_TAC THENL
[
 IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
 ,
 ETAC listTheory.CONS_11 THEN LRTAC THEN ETAC optionTheory.IS_NONE_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC
 ,
 STAC
 ,
 ETAC listTheory.CONS_11 THEN EQ_PAIR_ASM_TAC THEN RLTAC THEN CONTR_ASMS_TAC
]
QED

Theorem VISITED_TX_BDS_TO_FETCH_ADD_EOP_BD_LEMMA:
!registers memory visited_bds bd li r fbd bds start_bd_address sop_li FBD_SOP endpoint_sop_li next_bd_address.
  BDS_TO_FETCH_DISJOINT (fbd::bds) /\
  NOT_BD_RA visited_bds (fbd::bds) /\
  start_bd_address <> 0w /\
  fbd = (((bd, li), r, r), no_update) /\
  r = get_bd_ras registers start_bd_address /\
  (bd, li) = form_bd_li (MAP memory r) /\
  sop_li = (if FBD_SOP then li else endpoint_sop_li) /\
  EOP_BD registers FBD_SOP endpoint_sop_li bd li next_bd_address /\
  bds = visited_tx_bds_to_fetch T sop_li memory registers (visited_bds ++ [start_bd_address]) next_bd_address
  ==>
  fbd::bds = visited_tx_bds_to_fetch FBD_SOP endpoint_sop_li memory registers visited_bds start_bd_address
Proof
INTRO_TAC THEN
PTAC visited_tx_bds_to_fetch THENL
[
 IRTAC NOT_ZERO_START_IMPLIES_TX_BDS_OF_TRANSFER_REC_NULL_F_LEMMA THEN SOLVE_F_ASM_TAC
 ,
 IRTAC NOT_BD_RA_HD_TL_LEMMA THEN IRTAC EOP_BD_TX_TRANSFER_REC_NONE_IMPLIES_F_LEMMA THEN SOLVE_F_ASM_TAC
 ,
 PAT_X_ASSUM “fbd = (((bd, li), r, r), no_update)” (fn thm => ASSUME_TAC thm) THEN LRTAC THEN
 ITAC EOP_BD_TX_TRANSFER_REC_NOT_NONE_IMPLIES_FBD_LEMMA THEN
 LRTAC THEN
 REWRITE_TAC [listTheory.CONS_11] THEN
 ETAC listTheory.HD THEN ETAC combinTheory.o_THM THEN ETAC pairTheory.FST THEN ETAC pairTheory.SND THEN
 ASM_RL_RW_OTHERS_KEEP_TAC THEN LRTAC THEN ASM_RL_RW_OTHERS_KEEP_TAC THEN
 IRTAC EOP_BD_EOQ_IMPLIES_NEXT_BD_ADDRESS_ZERO_LEMMA THEN
 ALL_LRTAC THEN
 ETAC VISITED_TX_BDS_TO_FETCH_START_ZERO_EQ_EMPTY_LEMMA THEN
 STAC
 ,
 PAT_X_ASSUM “fbd = (((bd, li), r, r), no_update)” (fn thm => ASSUME_TAC thm) THEN LRTAC THEN
 ITAC EOP_BD_TX_TRANSFER_REC_NOT_NONE_IMPLIES_FBD_LEMMA THEN
 LRTAC THEN
 REWRITE_TAC [listTheory.APPEND, listTheory.CONS_11] THEN
 ETAC listTheory.HD THEN ETAC combinTheory.o_THM THEN ETAC pairTheory.FST THEN ETAC pairTheory.SND THEN
 ASM_RL_RW_OTHERS_KEEP_TAC THEN LRTAC THEN ASM_RL_RW_OTHERS_KEEP_TAC THEN
 ITAC EOP_BD_IMPLIES_EOP_LEMMA THEN
 IRTAC EOP_BD_NOT_EOQ_IMPLIES_NEXT_BD_ADDRESS_ZERO_LEMMA THEN
 RLTAC THEN
 LRTAC THEN
 IRTAC EOP_BD_TX_BDS_OF_TRANSFER_REC_VISITED_BDS_ADDED_START_BD_ADDRESS_LEMMA THEN
 LRTAC THEN
 ETAC optionTheory.THE_DEF THEN
 RLTAC THEN
 ASM_REWRITE_TAC [TX_BDS_OF_TRANSFERS_REC_EQ_VISITED_TX_BDS_TO_FETCH_SOP_LEMMA]
]
QED

Theorem BDS_TO_FETCH_DISJOINT_NOT_BD_RA_IMPLIES_LEMMA:
!bds visited_bds1 visited_bds2 memory registers start_bd_address endpoint_sop_li FBD_SOP.
  BDS_TO_FETCH_DISJOINT bds /\
  NOT_BD_RA visited_bds1 bds /\
  NOT_BD_RA visited_bds2 bds /\
  bds = visited_tx_bds_to_fetch FBD_SOP endpoint_sop_li memory registers visited_bds1 start_bd_address
  ==>
  bds = visited_tx_bds_to_fetch FBD_SOP endpoint_sop_li memory registers visited_bds2 start_bd_address
Proof
Induct THENL
[
 INTRO_TAC THEN
 RW_HYPS_TAC visited_tx_bds_to_fetch THEN
 LETS_TAC THEN
 IF_SPLIT_TAC THENL
 [
  PTAC visited_tx_bds_to_fetch THENL
  [
   STAC
   ,
   Cases_on ‘first_packet_bds’ THEN TRY (ETAC listTheory.NULL_DEF THEN SOLVE_F_ASM_TAC) THEN
   PAT_X_ASSUM “NOT_BD_RA visited_bds2 []” (fn thm => ASSUME_TAC thm) THEN
   FITAC BDS_TO_FETCH_DISJOINT_NOT_BD_RA_VISITED_BDS_PAIR_PRESERVES_TX_BDS_TO_FETCH_LEMMA THEN
   AXTAC THEN
   RLTAC THEN
   EQ_PAIR_ASM_TAC THEN
   STAC
   ,
   Cases_on ‘first_packet_bds’ THEN TRY (ETAC listTheory.NULL_DEF THEN SOLVE_F_ASM_TAC) THEN
   PAT_X_ASSUM “NOT_BD_RA visited_bds2 []” (fn thm => ASSUME_TAC thm) THEN
   FITAC BDS_TO_FETCH_DISJOINT_NOT_BD_RA_VISITED_BDS_PAIR_PRESERVES_TX_BDS_TO_FETCH_LEMMA THEN
   AXTAC THEN
   RLTAC THEN
   EQ_PAIR_ASM_TAC THEN
   STAC
   ,
   Cases_on ‘first_packet_bds’ THEN TRY (ETAC listTheory.NULL_DEF THEN SOLVE_F_ASM_TAC) THEN
   PAT_X_ASSUM “NOT_BD_RA visited_bds2 []” (fn thm => ASSUME_TAC thm) THEN
   FITAC BDS_TO_FETCH_DISJOINT_NOT_BD_RA_VISITED_BDS_PAIR_PRESERVES_TX_BDS_TO_FETCH_LEMMA THEN
   AXTAC THEN
   RLTAC THEN
   EQ_PAIR_ASM_TAC THEN
   RLTAC THEN
   ETAC listTheory.NULL_DEF THEN
   ETAC boolTheory.NOT_CLAUSES THEN
   SOLVE_F_ASM_TAC
  ]
  ,
  IF_SPLIT_TAC THENL
  [
   Cases_on ‘visited_bds_option’ THEN TRY (ETAC optionTheory.IS_NONE_DEF THEN SOLVE_F_ASM_TAC) THEN
   RLTAC THEN
   IRTAC BDS_TO_FETCH_DISJOINT_NOT_BD_RA_TX_BDS_OF_TRANSFER_REC_CYCLIC_IMPLIES_F_LEMMA THEN
   SOLVE_F_ASM_TAC
   ,
   IF_SPLIT_TAC THENL
   [
    RLTAC THEN ETAC listTheory.NULL_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC
    ,
    ETAC listTheory.APPEND_eq_NIL THEN LRTAC THEN ETAC listTheory.NULL_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC
   ]
  ]
 ]
 ,
 INTRO_TAC THEN
 ITAC VISITED_TX_BDS_TO_FETCH_FBD_NO_UPDATE_LEMMA THEN AXTAC THEN LRTAC THEN
 FITAC VISITED_TX_BDS_TO_FETCH_TAIL_CASES_LEMMA THEN
 AXTAC THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  FITAC VISITED_TX_BDS_TO_FETCH_BD_ADDRESS_R_LEMMA THEN
  PAT_X_ASSUM “NOT_BD_RA visited_bds1 (fbd::bds)” (fn thm => ASSUME_TAC thm) THEN
  ITAC DISJOINT_VISITED_BDS_EXTENDS_NOT_BD_RA_LEMMA THEN
  PAT_X_ASSUM “NOT_BD_RA visited_bds2 (fbd::bds)” (fn thm => ASSUME_TAC thm) THEN
  ITAC DISJOINT_VISITED_BDS_EXTENDS_NOT_BD_RA_LEMMA THEN
  ITAC BDS_TO_FETCH_DISJOINT_TAIL_LEMMA THEN
  FAITAC THEN
  ITAC VISITED_TX_BDS_TO_FETCH_FBD_LEMMA THEN
  IRTAC VISITED_TX_BDS_TO_FETCH_ADD_NOT_EOP_BD_LEMMA THEN
  STAC
  ,
  FITAC VISITED_TX_BDS_TO_FETCH_BD_ADDRESS_R_LEMMA THEN
  PAT_X_ASSUM “NOT_BD_RA visited_bds1 (fbd::bds)” (fn thm => ASSUME_TAC thm) THEN
  ITAC DISJOINT_VISITED_BDS_EXTENDS_NOT_BD_RA_LEMMA THEN
  PAT_X_ASSUM “NOT_BD_RA visited_bds2 (fbd::bds)” (fn thm => ASSUME_TAC thm) THEN
  ITAC DISJOINT_VISITED_BDS_EXTENDS_NOT_BD_RA_LEMMA THEN
  ITAC BDS_TO_FETCH_DISJOINT_TAIL_LEMMA THEN
  FAITAC THEN
  ITAC VISITED_TX_BDS_TO_FETCH_FBD_LEMMA THEN
  IRTAC VISITED_TX_BDS_TO_FETCH_ADD_EOP_BD_LEMMA THEN
  STAC
 ]
]
QED

Theorem EOP_EOQ_FETCH_BD_IMPLIES_TAIL_VISITED_TX_BDS_TO_FETCH_LEMMA:
!fbd bds visited_bds1 visited_bds2 (queue_id : 8 word) internal_state1 bd li r memory endpoint_id endpoint start_bd_address sop_li offset.
  BDS_TO_FETCH_DISJOINT (fbd::bds) /\
  NOT_BD_RA visited_bds1 (fbd::bds) /\
  endpoint_id = w2w ((queue_id - 32w) >>> 1) /\
  endpoint = internal_state1.endpoints_tx endpoint_id /\
  visited_bds2 = visited_bds1 ++ [start_bd_address] /\
  offset = word_bit 0 queue_id /\
  fbd::bds = visited_tx_bds_to_fetch (endpoint.sop offset) (endpoint.sop_li offset) memory internal_state1.registers visited_bds1 start_bd_address /\
  fbd = (((bd, li), r, r), no_update) /\
  sop_li = (if endpoint.sop offset then li else endpoint.sop_li offset) /\
  eop_bd bd /\
  li_to_eoq sop_li
  ==>
  !endpoint_sop_li  internal_state2.
    bds = visited_tx_bds_to_fetch T endpoint_sop_li memory internal_state2.registers visited_bds2 0w
Proof
INTRO_TAC THEN
GEN_TAC THEN
RW_HYP_LEMMA_TAC visited_tx_bds_to_fetch THEN
LETS_TAC THEN
IF_SPLIT_TAC THEN TRY (IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC) THEN
IF_SPLIT_TAC THEN TRY (IRTAC BDS_TO_FETCH_DISJOINT_NOT_BD_RA_TX_BDS_OF_TRANSFER_REC_NONE_IMPLIES_F_LEMMA THEN SOLVE_F_ASM_TAC) THEN
IF_SPLIT_TAC THEN IF_SPLIT_TAC THENL
[
 IRTAC EOP_FBD_TX_TRANSFER_REC_NOT_NONE_IMPLIES_EMPTY_TAIL_LEMMA THEN
 LRTAC THEN
 REWRITE_TAC [VISITED_TX_BDS_TO_FETCH_START_ZERO_EQ_EMPTY_LEMMA]
 ,
 IRTAC EOP_FBD_TX_TRANSFER_REC_NOT_NONE_IMPLIES_EMPTY_TAIL_LEMMA THEN
 LRTAC THEN
 REWRITE_TAC [VISITED_TX_BDS_TO_FETCH_START_ZERO_EQ_EMPTY_LEMMA]
 ,
 Cases_on ‘first_packet_bds’ THEN TRY (PTAC listTheory.NULL_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC) THEN
 ETAC listTheory.APPEND THEN
 ETAC listTheory.CONS_11 THEN
 LRTAC THEN
 LRTAC THEN
 ITAC EOP_FBD_TX_TRANSFER_REC_NOT_NONE_IMPLIES_EMPTY_TAIL_LEMMA THEN
 LRTAC THEN
 ETAC listTheory.APPEND THEN
 ETAC listTheory.HD THEN
 ETAC combinTheory.o_THM THEN ETAC pairTheory.FST THEN PTAC pairTheory.SND THEN LRTAC THEN ALL_LRTAC THEN CONTR_ASMS_TAC
 ,
 Cases_on ‘first_packet_bds’ THEN TRY (PTAC listTheory.NULL_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC) THEN
 ETAC listTheory.APPEND THEN
 ETAC listTheory.CONS_11 THEN
 LRTAC THEN
 LRTAC THEN
 ITAC EOP_FBD_TX_TRANSFER_REC_NOT_NONE_IMPLIES_EMPTY_TAIL_LEMMA THEN
 LRTAC THEN
 ETAC listTheory.APPEND THEN
 ALL_RLTAC THEN
 CONTR_ASMS_TAC
]
QED

Theorem TX_FETCH_BD_PRESERVES_REGISTERS_LEMMA:
!channel_id internal_state1 internal_state2 reply_option fetch_result.
  (internal_state2, fetch_result) = tx_fetch_bd channel_id internal_state1 reply_option
  ==>
  internal_state2.registers = internal_state1.registers
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_fetch_bd THEN EQ_PAIR_ASM_TAC THEN TRY STAC THEN
RLTAC THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem TX_FETCH_BD_UPDATES_SOP_LI_LEMMA:
!endpoint_id endpoint1 endpoint2 channel_id internal_state1 internal_state2 reply_option bd li r w u offset.
  endpoint_id = w2w ((channel_id - 32w) >>> 1) /\
  endpoint1 = internal_state1.endpoints_tx endpoint_id /\
  endpoint2 = internal_state2.endpoints_tx endpoint_id /\
  offset = word_bit 0 channel_id /\
  endpoint1.sop offset /\
  (internal_state2, SOME (((bd, li), r, w), u)) = tx_fetch_bd channel_id internal_state1 reply_option
  ==>
  li = endpoint2.sop_li offset
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_fetch_bd THEN EQ_PAIR_ASM_TAC THEN TRY (IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC) THEN
ETAC optionTheory.SOME_11 THEN
EQ_PAIR_ASM_TAC THEN
NLRTAC 6 THEN
LRTAC THEN
LRTAC THEN
RECORD_TAC THEN
LRTAC THEN
PAT_X_ASSUM “P” (fn thm1 => PAT_X_ASSUM “Q” (fn thm2 => ASSUME_TAC (REWRITE_RULE [thm1] thm2))) THEN
RLTAC THEN
WEAKEN_TAC (fn _ => true) THEN
LRTAC THEN
LRTAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
REWRITE_TAC [] THEN
RECORD_TAC THEN
APP_SCALAR_TAC THEN
STAC
QED

Theorem EOP_NOT_EOQ_FETCH_BD_IMPLIES_TAIL_VISITED_TX_BDS_TO_FETCH_LEMMA:
!fbd bds visited_bds1 visited_bds2 queue_id internal_state1 internal_state2 reply_option bd li r memory endpoint_id endpoint1 endpoint2 start_bd_address sop_li next_bd_address offset.
  BDS_TO_FETCH_DISJOINT (fbd::bds) /\
  NOT_BD_RA visited_bds1 (fbd::bds) /\
  endpoint_id = w2w ((queue_id - 32w) >>> 1) /\
  endpoint1 = internal_state1.endpoints_tx endpoint_id /\
  endpoint2 = internal_state2.endpoints_tx endpoint_id /\
  (internal_state2, SOME fbd) = tx_fetch_bd queue_id internal_state1 reply_option /\
  start_bd_address = internal_state1.qhp queue_id /\
  visited_bds2 = visited_bds1 ++ [start_bd_address] /\
  offset = word_bit 0 queue_id /\
  fbd::bds = visited_tx_bds_to_fetch (endpoint1.sop offset) (endpoint1.sop_li offset) memory internal_state1.registers visited_bds1 start_bd_address /\
  fbd = (((bd, li), r, r), no_update) /\
  sop_li = (if endpoint1.sop offset then li else endpoint1.sop_li offset) /\
  next_bd_address = li_to_next_bd_address internal_state2.registers sop_li /\
  eop_bd bd /\
  ~li_to_eoq sop_li
  ==>
  !endpoint_sop_li.
    bds = visited_tx_bds_to_fetch T endpoint_sop_li memory internal_state2.registers visited_bds2 next_bd_address
Proof
INTRO_TAC THEN
GEN_TAC THEN
RW_HYP_LEMMA_TAC visited_tx_bds_to_fetch THEN
LETS_TAC THEN
IF_SPLIT_TAC THEN TRY (IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC) THEN
IF_SPLIT_TAC THEN TRY (IRTAC BDS_TO_FETCH_DISJOINT_NOT_BD_RA_TX_BDS_OF_TRANSFER_REC_NONE_IMPLIES_F_LEMMA THEN SOLVE_F_ASM_TAC) THEN
IF_SPLIT_TAC THEN IF_SPLIT_TAC THENL
[
 ITAC EOP_FBD_TX_TRANSFER_REC_NOT_NONE_IMPLIES_EMPTY_TAIL_LEMMA THEN
 LRTAC THEN
 RLTAC THEN
 ALL_LRTAC THEN
 ETAC listTheory.HD THEN
 ETAC combinTheory.o_THM THEN ETAC pairTheory.FST THEN PTAC pairTheory.SND THEN CONTR_ASMS_TAC
 ,
 ITAC EOP_FBD_TX_TRANSFER_REC_NOT_NONE_IMPLIES_EMPTY_TAIL_LEMMA THEN LRTAC THEN RLTAC THEN ALL_LRTAC THEN CONTR_ASMS_TAC
 ,
 Cases_on ‘first_packet_bds’ THEN TRY (PTAC listTheory.NULL_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC) THEN
 ETAC listTheory.APPEND THEN ETAC listTheory.CONS_11 THEN LRTAC THEN LRTAC THEN
 ITAC EOP_FBD_TX_TRANSFER_REC_NOT_NONE_IMPLIES_EMPTY_TAIL_LEMMA THEN
 LRTAC THEN
 ETAC listTheory.APPEND THEN
 ETAC listTheory.HD THEN ETAC combinTheory.o_THM THEN ETAC pairTheory.FST THEN PTAC pairTheory.SND THEN LRTAC THEN
 RLTAC THEN
 IRTAC TX_FETCH_BD_PRESERVES_REGISTERS_LEMMA THEN
 LRTAC THEN
 RLTAC THEN
 LRTAC THEN
 LRTAC THEN
 IRTAC EOP_BD_TX_BDS_OF_TRANSFER_REC_VISITED_BDS_ADDED_START_BD_ADDRESS_LEMMA THEN
 LRTAC THEN
 ETAC optionTheory.THE_DEF THEN
 LRTAC THEN
 PAT_X_ASSUM “l = l1 ++ l2” (fn thm => ASSUME_TAC thm) THEN
 LRTAC THEN
 REWRITE_TAC [GSYM TX_BDS_OF_TRANSFERS_REC_EQ_VISITED_TX_BDS_TO_FETCH_SOP_LEMMA]
 ,
 Cases_on ‘first_packet_bds’ THEN TRY (PTAC listTheory.NULL_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC) THEN
 ETAC listTheory.APPEND THEN ETAC listTheory.CONS_11 THEN LRTAC THEN LRTAC THEN
 ITAC EOP_FBD_TX_TRANSFER_REC_NOT_NONE_IMPLIES_EMPTY_TAIL_LEMMA THEN
 LRTAC THEN
 ETAC listTheory.APPEND THEN
 LRTAC THEN
 WEAKEN_TAC (fn _ => true) THEN WEAKEN_TAC (fn _ => true) THEN
 IRTAC TX_FETCH_BD_PRESERVES_REGISTERS_LEMMA THEN
 LRTAC THEN
 RLTAC THEN
 RLTAC THEN
 RLTAC THEN
 LRTAC THEN
 IRTAC EOP_BD_TX_BDS_OF_TRANSFER_REC_VISITED_BDS_ADDED_START_BD_ADDRESS_LEMMA THEN
 LRTAC THEN
 ETAC optionTheory.THE_DEF THEN
 LRTAC THEN
 PAT_X_ASSUM “l = l1 ++ l2” (fn thm => ASSUME_TAC thm) THEN
 LRTAC THEN
 REWRITE_TAC [GSYM TX_BDS_OF_TRANSFERS_REC_EQ_VISITED_TX_BDS_TO_FETCH_SOP_LEMMA]
]
QED

Theorem TX_FETCH_BD_PRESERVES_ENDPOINT_SOP_LI_LEMMA:
!endpoint_id endpoint1 endpoint2 channel_id internal_state1 internal_state2 reply_option bd li r w u offset.
  endpoint_id = w2w ((channel_id - 32w) >>> 1) /\
  endpoint1 = internal_state1.endpoints_tx endpoint_id /\
  endpoint2 = internal_state2.endpoints_tx endpoint_id /\
  offset = word_bit 0 channel_id /\
  ~endpoint1.sop offset /\
  (internal_state2, SOME (((bd, li), r, w), u)) = tx_fetch_bd channel_id internal_state1 reply_option
  ==>
  endpoint2.sop_li offset = endpoint1.sop_li offset
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_fetch_bd THEN EQ_PAIR_ASM_TAC THEN TRY (IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC) THEN
ETAC optionTheory.SOME_11 THEN
EQ_PAIR_ASM_TAC THEN
NLRTAC 6 THEN
LRTAC THEN
LRTAC THEN
LRTAC THEN
LRTAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
RECORD_TAC THEN
APP_SCALAR_TAC THEN
REWRITE_TAC [] THEN
RECORD_TAC THEN
APP_SCALAR_TAC THEN
STAC
QED

Theorem NOT_EOP_FETCH_BD_IMPLIES_TAIL_VISITED_TX_BDS_TO_FETCH_LEMMA:
!fbd bds visited_bds1 visited_bds2 queue_id internal_state1 internal_state2 reply_option bd li r memory endpoint_id endpoint1 endpoint2 start_bd_address next_bd_address offset.
  BDS_TO_FETCH_DISJOINT (fbd::bds) /\
  NOT_BD_RA visited_bds1 (fbd::bds) /\
  endpoint_id = w2w ((queue_id - 32w) >>> 1) /\
  endpoint1 = internal_state1.endpoints_tx endpoint_id /\
  endpoint2 = internal_state2.endpoints_tx endpoint_id /\
  (internal_state2, SOME fbd) = tx_fetch_bd queue_id internal_state1 reply_option /\
  start_bd_address = internal_state1.qhp queue_id /\
  visited_bds2 = visited_bds1 ++ [start_bd_address] /\
  offset = word_bit 0 queue_id /\
  fbd::bds = visited_tx_bds_to_fetch (endpoint1.sop offset) (endpoint1.sop_li offset) memory internal_state1.registers visited_bds1 start_bd_address /\
  fbd = (((bd, li), r, r), no_update) /\
  next_bd_address = next_bd_pointer bd /\
  ~eop_bd bd
  ==>
  bds = visited_tx_bds_to_fetch F (endpoint2.sop_li offset) memory internal_state2.registers visited_bds2 next_bd_address
Proof
INTRO_TAC THEN
RW_HYP_LEMMA_TAC visited_tx_bds_to_fetch THEN
LETS_TAC THEN
IF_SPLIT_TAC THEN TRY (IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC) THEN
IF_SPLIT_TAC THEN TRY (IRTAC BDS_TO_FETCH_DISJOINT_NOT_BD_RA_TX_BDS_OF_TRANSFER_REC_NONE_IMPLIES_F_LEMMA THEN SOLVE_F_ASM_TAC) THEN
IF_SPLIT_TAC THEN IF_SPLIT_TAC THENL
[
 ITAC TX_BDS_OF_TRANSFER_REC_VISITED_TX_BDS_TO_FETCH_TAIL_NOT_EOP_EOQ_LEMMA THEN
 LRTAC THEN
 RLTAC THEN
 PAT_X_ASSUM “fbd = (((bd,li),r,r),no_update)” (fn thm => ASSUME_TAC thm) THEN LRTAC THEN
 ETAC listTheory.HD THEN ETAC combinTheory.o_THM THEN ETAC pairTheory.FST THEN ETAC pairTheory.SND THEN LRTAC THEN
 LRTAC THEN
 FITAC TX_FETCH_BD_UPDATES_SOP_LI_LEMMA THEN
 IRTAC TX_FETCH_BD_PRESERVES_REGISTERS_LEMMA THEN
 STAC
 ,
 ITAC TX_BDS_OF_TRANSFER_REC_VISITED_TX_BDS_TO_FETCH_TAIL_NOT_EOP_EOQ_LEMMA THEN
 LRTAC THEN
 RLTAC THEN
 PAT_X_ASSUM “fbd = (((bd,li),r,r),no_update)” (fn thm => ASSUME_TAC thm) THEN LRTAC THEN
 FITAC TX_FETCH_BD_PRESERVES_ENDPOINT_SOP_LI_LEMMA THEN
 RLTAC THEN
 RLTAC THEN
 IRTAC TX_FETCH_BD_PRESERVES_REGISTERS_LEMMA THEN
 STAC
 ,
 PTAC listTheory.NULL_DEF THEN TRY (ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC) THEN LRTAC THEN
 PAT_X_ASSUM “x::xs = l1 ++ l2” (fn thm => ASSUME_TAC thm) THEN
 ASM_LR_RW_OTHERS_KEEP_TAC THEN
 IRTAC BDS_TO_FETCH_DISJOINT_APPEND_LEMMA THEN
 IRTAC NOT_BD_RA_APPEND_LEMMA THEN
 PAT_X_ASSUM “fbd = (((bd,li),r,r),no_update)” (fn thm => ASSUME_TAC thm) THEN LRTAC THEN
 ETAC listTheory.APPEND THEN
 ETAC listTheory.CONS_11 THEN
 RLTAC THEN
 ETAC listTheory.HD THEN ETAC combinTheory.o_THM THEN ETAC pairTheory.FST THEN ETAC pairTheory.SND THEN LRTAC THEN
 PAT_X_ASSUM “l = l1 ++ l2” (fn thm => ASSUME_TAC thm) THEN
 LRTAC THEN
 FITAC TX_FETCH_BD_UPDATES_SOP_LI_LEMMA THEN RLTAC THEN
 IRTAC TX_FETCH_BD_PRESERVES_REGISTERS_LEMMA THEN LRTAC THEN
 PAT_X_ASSUM “visited_bds2 = visited_bds1 ++ [start_bd_address]” (fn thm => ASSUME_TAC thm) THEN LRTAC THEN
 MATCH_MP_TAC ((GEN_ALL o DISCH_ALL o CONJUNCT1 o UNDISCH o SPEC_ALL) TX_BDS_OF_TRANSFER_REC_VISITED_TX_BDS_TO_FETCH_TAIL_NOT_EOP_NOT_EOQ_LEMMA) THEN
 PAXTAC THEN
 LRTAC THEN
 PAT_X_ASSUM “next_bd_address = next_bd_pointer bd” (fn thm => ASSUME_TAC thm) THEN LRTAC THEN
 PAT_X_ASSUM “visited_bds = THE visited_bds_option” (fn thm => ASSUME_TAC thm) THEN LRTAC THEN
 LRTAC THEN
 REWRITE_TAC [] THEN
 REPEAT (WEAKEN_TAC is_eq) THEN
 CONJS_TAC THEN CCONTR_TAC THEN CONTR_ASMS_TAC
 ,
 PTAC listTheory.NULL_DEF THEN TRY (ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC) THEN LRTAC THEN
 PAT_X_ASSUM “x::xs = l1 ++ l2” (fn thm => ASSUME_TAC thm) THEN
 ASM_LR_RW_OTHERS_KEEP_TAC THEN
 IRTAC BDS_TO_FETCH_DISJOINT_APPEND_LEMMA THEN
 IRTAC NOT_BD_RA_APPEND_LEMMA THEN
 PAT_X_ASSUM “fbd = (((bd,li),r,r),no_update)” (fn thm => ASSUME_TAC thm) THEN LRTAC THEN
 ETAC listTheory.APPEND THEN
 ETAC listTheory.CONS_11 THEN
 RLTAC THEN
 PAT_X_ASSUM “l = l1 ++ l2” (fn thm => ASSUME_TAC thm) THEN
 LRTAC THEN
 FITAC TX_FETCH_BD_PRESERVES_ENDPOINT_SOP_LI_LEMMA THEN RLTAC THEN RLTAC THEN
 IRTAC TX_FETCH_BD_PRESERVES_REGISTERS_LEMMA THEN LRTAC THEN
 PAT_X_ASSUM “visited_bds2 = visited_bds1 ++ [start_bd_address]” (fn thm => ASSUME_TAC thm) THEN LRTAC THEN
 MATCH_MP_TAC ((GEN_ALL o DISCH_ALL o CONJUNCT1 o UNDISCH o SPEC_ALL) TX_BDS_OF_TRANSFER_REC_VISITED_TX_BDS_TO_FETCH_TAIL_NOT_EOP_NOT_EOQ_LEMMA) THEN
 PAXTAC THEN
 LRTAC THEN
 PAT_X_ASSUM “next_bd_address = next_bd_pointer bd” (fn thm => ASSUME_TAC thm) THEN LRTAC THEN
 PAT_X_ASSUM “visited_bds = THE visited_bds_option” (fn thm => ASSUME_TAC thm) THEN LRTAC THEN
 LRTAC THEN
 REWRITE_TAC [] THEN
 REPEAT (WEAKEN_TAC is_eq) THEN
 CONJS_TAC THEN CCONTR_TAC THEN CONTR_ASMS_TAC
]
QED

Theorem ENDPOINT_NOT_SOP_TX_BDS_TO_FETCH_EQ_VISITED_TX_BDS_TO_FETCH_LEMMA:
!channel_id endpoint_id endpoint internal_state start_bd_address memory offset.
  endpoint_id = w2w ((channel_id - 32w) >>> 1) /\
  endpoint = internal_state.endpoints_tx endpoint_id /\
  offset = word_bit 0 channel_id /\
  ~endpoint.sop offset /\
  start_bd_address = internal_state.qhp channel_id
  ==>
  tx_bds_to_fetch channel_id memory internal_state =
  visited_tx_bds_to_fetch F (endpoint.sop_li offset) memory internal_state.registers [] start_bd_address
Proof
INTRO_TAC THEN
ETAC tx_bds_to_fetch THEN
ETAC visited_tx_bds_to_fetch THEN
LETS_TAC THEN
STAC
QED

Theorem ENDPOINT_SOP_TX_BDS_TO_FETCH_EQ_VISITED_TX_BDS_TO_FETCH_LEMMA:
!channel_id endpoint_id endpoint internal_state start_bd_address memory offset.
  endpoint_id = w2w ((channel_id - 32w) >>> 1) /\
  endpoint = internal_state.endpoints_tx endpoint_id /\
  offset = word_bit 0 channel_id /\
  endpoint.sop offset /\
  start_bd_address = internal_state.qhp channel_id
  ==>
  !endpoint_sop_li.
    tx_bds_to_fetch channel_id memory internal_state =
    visited_tx_bds_to_fetch T endpoint_sop_li memory internal_state.registers [] start_bd_address
Proof
INTRO_TAC THEN
GEN_TAC THEN
ETAC tx_bds_to_fetch THEN
ETAC visited_tx_bds_to_fetch THEN
LETS_TAC THEN
STAC
QED

Theorem FETCH_NOT_EOP_IMPLIES_SETS_NOT_SOP_LEMMA:
!channel_id endpoint_id endpoint2 internal_state1 internal_state2 bd li r w u reply_option offset.
  endpoint_id = w2w ((channel_id - 32w) >>> 1) /\
  endpoint2 = internal_state2.endpoints_tx endpoint_id /\
  offset = word_bit 0 channel_id /\
  ~eop_bd bd /\
  (internal_state2, SOME (((bd, li), r, w), u)) = tx_fetch_bd channel_id internal_state1 reply_option
  ==>
  ~endpoint2.sop offset
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_fetch_bd THEN TRY (EQ_PAIR_ASM_TAC THEN IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC) THEN
EQ_PAIR_ASM_TAC THEN
ETAC optionTheory.SOME_11 THEN
EQ_PAIR_ASM_TAC THEN
ALL_LRTAC  THEN
RECORD_TAC THEN
ETAC bbb_usb_functionsTheory.next_bd_pointer THEN
ETAC bbb_usb_functionsTheory.eop_bd THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
ASM_REWRITE_TAC [] THEN
RECORD_TAC THEN
APP_SCALAR_TAC THEN
STAC
QED

Theorem FETCH_EOP_IMPLIES_SETS_SOP_LEMMA:
!channel_id endpoint_id endpoint2 internal_state1 internal_state2 bd li r w u reply_option offset.
  endpoint_id = w2w ((channel_id - 32w) >>> 1) /\
  endpoint2 = internal_state2.endpoints_tx endpoint_id /\
  offset = word_bit 0 channel_id /\
  eop_bd bd /\
  (internal_state2, SOME (((bd, li), r, w), u)) = tx_fetch_bd channel_id internal_state1 reply_option
  ==>
  endpoint2.sop offset
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_fetch_bd THEN TRY (EQ_PAIR_ASM_TAC THEN IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC) THEN
EQ_PAIR_ASM_TAC THEN
ETAC optionTheory.SOME_11 THEN
EQ_PAIR_ASM_TAC THEN
ALL_LRTAC  THEN
RECORD_TAC THEN
ETAC bbb_usb_functionsTheory.next_bd_pointer THEN
ETAC bbb_usb_functionsTheory.eop_bd THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
ASM_REWRITE_TAC [] THEN
RECORD_TAC THEN
APP_SCALAR_TAC THEN
STAC
QED

Theorem FETCH_NOT_EOP_QHP_EQ_NEXT_BD_POINTER_LEMMA:
!channel_id internal_state1 internal_state2 bd li r w u reply_option.
  ~eop_bd bd /\
  (internal_state2, SOME (((bd, li), r, w), u)) = tx_fetch_bd channel_id internal_state1 reply_option
  ==>
  internal_state2.qhp channel_id = next_bd_pointer bd
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_fetch_bd THEN TRY (EQ_PAIR_ASM_TAC THEN IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC) THEN
EQ_PAIR_ASM_TAC THEN
ETAC optionTheory.SOME_11 THEN
EQ_PAIR_ASM_TAC THEN
ALL_LRTAC  THEN
RECORD_TAC THEN
ETAC bbb_usb_functionsTheory.next_bd_pointer THEN
ETAC bbb_usb_functionsTheory.eop_bd THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
ASM_REWRITE_TAC [] THEN
RECORD_TAC THEN
REWRITE_TAC []
QED

Theorem FETCH_SOP_EOP_EOQ_QHP_EQ_ZERO_LEMMA:
!endpoint_id endpoint channel_id internal_state1 internal_state2 bd li r w u reply_option offset.
  endpoint_id = w2w ((channel_id - 32w) >>> 1) /\
  endpoint = internal_state1.endpoints_tx endpoint_id /\
  offset = word_bit 0 channel_id /\
  endpoint.sop offset /\
  eop_bd bd /\
  li_to_eoq li /\
  (internal_state2, SOME (((bd, li), r, w), u)) = tx_fetch_bd channel_id internal_state1 reply_option
  ==>
  internal_state2.qhp channel_id = 0w
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_fetch_bd THEN TRY (EQ_PAIR_ASM_TAC THEN IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC) THEN
EQ_PAIR_ASM_TAC THEN
ETAC optionTheory.SOME_11 THEN
EQ_PAIR_ASM_TAC THEN
ALL_LRTAC  THEN
RECORD_TAC THEN
ETAC bbb_usb_functionsTheory.next_bd_pointer THEN
ETAC bbb_usb_functionsTheory.eop_bd THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
ASM_REWRITE_TAC [] THEN
RECORD_TAC THEN
REWRITE_TAC []
QED

Theorem FETCH_NOT_SOP_EOP_EOQ_QHP_EQ_ZERO_LEMMA:
!endpoint_id endpoint channel_id internal_state1 internal_state2 bd li r w u reply_option offset.
  endpoint_id = w2w ((channel_id - 32w) >>> 1) /\
  endpoint = internal_state1.endpoints_tx endpoint_id /\
  offset = word_bit 0 channel_id /\
  ~endpoint.sop offset /\
  eop_bd bd /\
  li_to_eoq (endpoint.sop_li offset) /\
  (internal_state2, SOME (((bd, li), r, w), u)) = tx_fetch_bd channel_id internal_state1 reply_option
  ==>
  internal_state2.qhp channel_id = 0w
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_fetch_bd THEN TRY (EQ_PAIR_ASM_TAC THEN IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC) THEN
EQ_PAIR_ASM_TAC THEN
ETAC optionTheory.SOME_11 THEN
EQ_PAIR_ASM_TAC THEN
ALL_LRTAC  THEN
RECORD_TAC THEN
ETAC bbb_usb_functionsTheory.next_bd_pointer THEN
ETAC bbb_usb_functionsTheory.eop_bd THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
ASM_REWRITE_TAC [] THEN
RECORD_TAC THEN
REWRITE_TAC []
QED

Theorem FETCH_SOP_EOP_NOT_EOQ_QHP_EQ_NEXT_SOP_BD_ADDRESS_LEMMA:
!endpoint_id endpoint channel_id internal_state1 internal_state2 bd li r w u reply_option offset.
  endpoint_id = w2w ((channel_id - 32w) >>> 1) /\
  endpoint = internal_state1.endpoints_tx endpoint_id /\
  offset = word_bit 0 channel_id /\
  endpoint.sop offset /\
  eop_bd bd /\
  ~li_to_eoq li /\
  (internal_state2, SOME (((bd, li), r, w), u)) = tx_fetch_bd channel_id internal_state1 reply_option
  ==>
  internal_state2.qhp channel_id = li_to_next_bd_address internal_state2.registers li
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_fetch_bd THEN TRY (EQ_PAIR_ASM_TAC THEN IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC) THEN
EQ_PAIR_ASM_TAC THEN
ETAC optionTheory.SOME_11 THEN
EQ_PAIR_ASM_TAC THEN
ALL_LRTAC  THEN
RECORD_TAC THEN
ETAC bbb_usb_functionsTheory.next_bd_pointer THEN
ETAC bbb_usb_functionsTheory.eop_bd THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
ASM_REWRITE_TAC [] THEN
RECORD_TAC THEN
REWRITE_TAC []
QED

Theorem FETCH_NOT_SOP_EOP_NOT_EOQ_QHP_EQ_NEXT_SOP_BD_ADDRESS_LEMMA:
!endpoint_id endpoint channel_id internal_state1 internal_state2 bd li r w u reply_option offset.
  endpoint_id = w2w ((channel_id - 32w) >>> 1) /\
  endpoint = internal_state1.endpoints_tx endpoint_id /\
  offset = word_bit 0 channel_id /\
  ~endpoint.sop offset /\
  eop_bd bd /\
  ~li_to_eoq (endpoint.sop_li offset) /\
  (internal_state2, SOME (((bd, li), r, w), u)) = tx_fetch_bd channel_id internal_state1 reply_option
  ==>
  internal_state2.qhp channel_id = li_to_next_bd_address internal_state2.registers (endpoint.sop_li offset)
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_fetch_bd THEN TRY (EQ_PAIR_ASM_TAC THEN IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC) THEN
EQ_PAIR_ASM_TAC THEN
ETAC optionTheory.SOME_11 THEN
EQ_PAIR_ASM_TAC THEN
ALL_LRTAC  THEN
RECORD_TAC THEN
ETAC bbb_usb_functionsTheory.next_bd_pointer THEN
ETAC bbb_usb_functionsTheory.eop_bd THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
ASM_REWRITE_TAC []
QED

Theorem TX_FETCH_BD_RESULT_LEMMA:
!channel_id internal_state1 internal_state2 bytes tag fetch_result.
  (internal_state2, SOME fetch_result) = tx_fetch_bd channel_id internal_state1 (SOME (bytes, tag))
  ==>
  ?bd li bd_ras.
     (bd, li) = form_bd_li bytes /\
     bd_ras = get_bd_ras internal_state1.registers (internal_state1.qhp channel_id) /\
     fetch_result = (((bd, li), bd_ras, bd_ras), no_update)
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_fetch_bd THEN TRY (EQ_PAIR_ASM_TAC THEN IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC) THEN
EQ_PAIR_ASM_TAC THEN
ETAC optionTheory.SOME_11 THEN
PAXTAC THEN
STAC
QED

Theorem FETCHED_TX_BD_EQ_HD_TX_BDS_OF_TRANSFER_REC_LEMMA:
!memory internal_state1 internal_state2 channel_id bd bds fetched_bd bytes tag addresses visited_bds_option.
  (addresses, tag) = tx_fetch_bd_addresses channel_id internal_state1 /\
  bytes = MAP memory addresses /\
  (internal_state2, SOME fetched_bd) = tx_fetch_bd channel_id internal_state1 (SOME (bytes, tag)) /\
  (bd::bds, visited_bds_option) = tx_bds_of_transfer_rec memory internal_state1.registers [] (internal_state1.qhp channel_id)
  ==>
  bd = fetched_bd
Proof
INTRO_TAC THEN
PTAC tx_bds_of_transfer_rec THEN TRY ((EQ_PAIR_ASM_TAC THEN IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC) ORELSE (ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC)) THEN
 EQ_PAIR_ASM_TAC THEN
 ETAC listTheory.CONS_11 THEN
 ETAC bbb_usb_txTheory.tx_fetch_bd_addresses THEN
 IF_SPLIT_TAC THEN TRY CONTR_ASMS_TAC THEN
 EQ_PAIR_ASM_TAC THEN
 IRTAC TX_FETCH_BD_RESULT_LEMMA THEN
 AXTAC THEN
 RLTAC THEN NRLTAC 2 THEN RLTAC THEN RLTAC THEN LRTAC THEN LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 NLRTAC 2 THEN
 STAC
QED

Theorem FETCHED_TX_BD_EQ_HD_TX_BDS_TO_FETCH_LEMMA:
!memory internal_state1 internal_state2 channel_id bd bds fetched_bd bytes tag addresses.
  (addresses, tag) = tx_fetch_bd_addresses channel_id internal_state1 /\
  bytes = MAP memory addresses /\
  (internal_state2, SOME fetched_bd) = tx_fetch_bd channel_id internal_state1 (SOME (bytes, tag)) /\
  bd::bds = tx_bds_to_fetch channel_id memory internal_state1
  ==>
  bd = fetched_bd
Proof
INTRO_TAC THEN
PTAC tx_bds_to_fetch THEN TRY (
 (EQ_PAIR_ASM_TAC THEN IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC) ORELSE
 (IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC)) THEN
 Cases_on ‘first_packet_bds’ THEN TRY (PTAC listTheory.NULL_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC) THEN
 TRY (RW_HYP_LEMMA_TAC listTheory.APPEND) THEN
 ETAC listTheory.CONS_11 THEN
 NRLTAC 2 THEN
 IRTAC FETCHED_TX_BD_EQ_HD_TX_BDS_OF_TRANSFER_REC_LEMMA THEN
 STAC
QED

Theorem TX_FETCH_BD_UPDATES_QHP_LEMMA:
!channel_id internal_state1 internal_state2 bytes tag fetch_result.
  (internal_state2, SOME fetch_result) = tx_fetch_bd channel_id internal_state1 (SOME (bytes, tag))
  ==>
  ?endpoint_id endpoint bd li bd_ras next_bd_address sop offset sop_li.
    endpoint_id = w2w ((channel_id - 32w) >>> 1) /\
    endpoint = internal_state1.endpoints_tx endpoint_id /\
    offset = word_bit 0 channel_id /\
    (bd, li) = form_bd_li bytes /\
    bd_ras = get_bd_ras internal_state1.registers (internal_state1.qhp channel_id) /\
    fetch_result = (((bd, li), bd_ras, bd_ras), no_update) /\
    next_bd_address = next_bd_pointer bd /\
    sop = (next_bd_pointer bd = 0w) /\
    ((sop_li = li /\ endpoint.sop offset) \/ (sop_li = endpoint.sop_li offset /\ ~endpoint.sop offset)) /\
    ((internal_state2.qhp channel_id = 0w /\ next_bd_address = 0w /\ li_to_eoq sop_li) \/
     (internal_state2.qhp channel_id = li_to_next_bd_address internal_state1.registers sop_li /\ next_bd_address = 0w /\ ~li_to_eoq sop_li) \/
     (internal_state2.qhp channel_id = next_bd_address /\ next_bd_address <> 0w))
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_fetch_bd THEN TRY (EQ_PAIR_ASM_TAC THEN IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC) THEN
EQ_PAIR_ASM_TAC THEN
RLTAC THEN
ETAC optionTheory.SOME_11 THEN
INST_EXISTS_NAMES_TAC ["endpoint_id", "endpoint", "bd", "li", "bd_ras"] THEN
Q.EXISTS_TAC ‘next_bd_pointer bd’ THEN
Q.EXISTS_TAC ‘next_bd_pointer bd = 0w’ THEN
Q.EXISTS_TAC ‘offset’ THEN
Cases_on ‘endpoint.sop offset’ THENL
[
 Q.EXISTS_TAC ‘li’ THEN
 CONJS_TAC THEN TRY STAC THEN
 IF_SPLIT_TAC THENL
 [
  IF_SPLIT_TAC THEN
   ALL_LRTAC THEN RECORD_TAC THEN REWRITE_TAC [combinTheory.UPDATE_def] THEN APP_SCALAR_TAC THEN STAC
  ,
   ALL_LRTAC THEN RECORD_TAC THEN REWRITE_TAC [combinTheory.UPDATE_def] THEN APP_SCALAR_TAC THEN STAC
 ]
 ,
 Q.EXISTS_TAC ‘endpoint.sop_li offset’ THEN
 CONJS_TAC THEN TRY STAC THEN
 IF_SPLIT_TAC THENL
 [
  IF_SPLIT_TAC THEN
   ALL_LRTAC THEN RECORD_TAC THEN REWRITE_TAC [combinTheory.UPDATE_def] THEN APP_SCALAR_TAC THEN STAC
  ,
   ALL_LRTAC THEN RECORD_TAC THEN REWRITE_TAC [combinTheory.UPDATE_def] THEN APP_SCALAR_TAC THEN STAC
 ]
]
QED

Theorem QHP_IN_FETCHED_TX_BD_RAS_LEMMA:
!channel_id internal_state1 internal_state2 tag bytes bd bd_ras bd_was bd_address bd_update.
  (internal_state2, SOME ((bd, bd_ras, bd_was), bd_update)) = tx_fetch_bd channel_id internal_state1 (SOME (bytes, tag)) /\
  bd_address = internal_state1.qhp channel_id
  ==>
  MEM bd_address bd_ras
Proof
INTRO_TAC THEN
IRTAC TX_FETCH_BD_UPDATES_QHP_LEMMA THEN
AXTAC THEN
EQ_PAIR_ASM_TAC THEN
IRTAC BD_ADDRESS_IN_GET_BD_RAS_LEMMA THEN
STAC
QED

Theorem NO_VISITED_BDS_IMPLIES_VISISTED_TX_BDS_TO_FETCH_EQ_TX_BDS_TO_FETCH_LEMMA:
!queue_id memory internal_state endpoint_id endpoint offset.
  endpoint_id = w2w ((queue_id - 32w) >>> 1) /\
  endpoint = internal_state.endpoints_tx endpoint_id /\
  offset = word_bit 0 queue_id
  ==>
  visited_tx_bds_to_fetch (endpoint.sop offset) (endpoint.sop_li offset) memory internal_state.registers [] (internal_state.qhp queue_id) =
  tx_bds_to_fetch queue_id memory internal_state
Proof
REWRITE_TAC [visited_tx_bds_to_fetch, tx_bds_to_fetch] THEN
INTRO_TAC THEN
LETS_TAC THEN
RLTAC THEN
LRTAC THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 2 THEN
STAC
QED

Theorem QHP_EQ_ZERO_IMPLIES_TX_BDS_TO_FETCH_EQ_NULL:
!channel_id internal_state.
  internal_state.qhp channel_id = 0w
  ==>
  !memory.
    tx_bds_to_fetch channel_id memory internal_state = []
Proof
INTRO_TAC THEN GEN_TAC THEN PTAC tx_bds_to_fetch THEN TRY STAC THENL
[
 LRTAC THEN IRTAC TX_BDS_OF_TRANSFER_REC_ZERO_START_IMPLIES_EMPTY_BDS_LEMMA THEN STAC
 ,
 RLTAC THEN IRTAC TX_BDS_OF_TRANSFER_REC_ZERO_START_IMPLIES_EMPTY_BDS_LEMMA THEN STAC
 ,
 ALL_LRTAC THEN PTAC tx_bds_of_transfer_rec THEN TRY (CONTR_NEG_ASM_TAC boolTheory.EQ_REFL) THEN EQ_PAIR_ASM_TAC THEN RLTAC THEN PTAC listTheory.NULL_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC
]
QED

Theorem VISITED_TX_BDS_TO_FETCH_MEMBER_IMPLIES_WAS_EQ_RAS_LEMMA:
!bds FBD_SOP endpoint_sop_li memory registers visited_bds start_bd_address bd ras was uf.
  bds = visited_tx_bds_to_fetch FBD_SOP endpoint_sop_li memory registers visited_bds start_bd_address /\
  MEM ((bd, ras, was), uf) bds
  ==>
  was = ras
Proof
Induct THEN TRY (REWRITE_TAC [listTheory.MEM]) THEN
INTRO_TAC THEN
SPLIT_ASM_DISJS_TAC THEN TRY (IRTAC VISITED_TX_BDS_TO_FETCH_FBD_NO_UPDATE_LEMMA THEN RLTAC THEN AXTAC THEN EQ_PAIR_ASM_TAC THEN STAC) THEN
PAT_X_ASSUM “!x.P” (fn thm => MATCH_MP_TAC thm) THEN
PTAC visited_tx_bds_to_fetch THEN TRY (IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC) THENL
[
 PTAC tx_bds_of_transfer_rec THEN EQ_PAIR_ASM_TAC THEN TRY (IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC) THENL
 [
  RLTAC THEN ETAC listTheory.CONS_11 THEN LRTAC THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
  ,
  RLTAC THEN ETAC listTheory.CONS_11 THEN LRTAC THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
  ,
  RLTAC THEN ETAC listTheory.CONS_11 THEN RLTAC THEN RLTAC THEN
  Q.EXISTS_TAC ‘F’ THEN
  Q.EXISTS_TAC ‘endpoint_sop_li’ THEN
  Q.EXISTS_TAC ‘memory’ THEN
  Q.EXISTS_TAC ‘registers’ THEN
  Q.EXISTS_TAC ‘visited_bds'’ THEN
  Q.EXISTS_TAC ‘next_bd_address’ THEN
  Q.EXISTS_TAC ‘bd’ THEN
  Q.EXISTS_TAC ‘uf’ THEN
  PTAC visited_tx_bds_to_fetch THEN TRY (STAC ORELSE (ETAC listTheory.NULL_EQ THEN STAC)) THEN
  PAT_X_ASSUM “visited_bds_option' = visited_bds_option : 32 interconnect_addresses_type option” (fn thm => ASSUME_TAC thm) THEN
  LRTAC THEN
  CONTR_ASMS_TAC
 ]
 ,
 PTAC tx_bds_of_transfer_rec THEN EQ_PAIR_ASM_TAC THEN TRY (IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC) THENL
 [
  ALL_RLTAC THEN ETAC optionTheory.IS_NONE_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC
  ,
  PAT_X_ASSUM “h::bds = first_packet_bds” (fn thm => ASSUME_TAC thm) THEN RLTAC THEN ETAC listTheory.CONS_11 THEN PAT_X_ASSUM “[] = bds” (fn thm => ASSUME_TAC thm) THEN RLTAC THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
  ,
  RLTAC THEN ETAC listTheory.CONS_11 THEN RLTAC THEN RLTAC THEN
  Q.EXISTS_TAC ‘F’ THEN
  Q.EXISTS_TAC ‘sop_li’ THEN
  Q.EXISTS_TAC ‘memory’ THEN
  Q.EXISTS_TAC ‘registers’ THEN
  Q.EXISTS_TAC ‘visited_bds'’ THEN
  Q.EXISTS_TAC ‘next_bd_address’ THEN
  Q.EXISTS_TAC ‘bd’ THEN
  Q.EXISTS_TAC ‘uf’ THEN
  PTAC visited_tx_bds_to_fetch THEN TRY (STAC ORELSE (ETAC listTheory.NULL_EQ THEN STAC)) THEN
  ETAC boolTheory.bool_case_thm THEN
  RLTAC THEN
  CONTR_ASMS_TAC
 ]
 ,
 PTAC tx_bds_of_transfer_rec THEN EQ_PAIR_ASM_TAC THENL
 [
  RLTAC THEN ETAC listTheory.NULL_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC
  ,
  NRLTAC 2 THEN ETAC optionTheory.IS_NONE_DEF THEN ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC
  ,
  RLTAC THEN ETAC listTheory.APPEND THEN ETAC listTheory.CONS_11 THEN
  WEAKEN_TAC (fn _ => true) THEN WEAKEN_TAC (fn _ => true) THEN WEAKEN_TAC (fn _ => true) THEN
  Q.EXISTS_TAC ‘T’ THEN
  Q.EXISTS_TAC ‘sop_li’ THEN
  Q.EXISTS_TAC ‘memory’ THEN
  Q.EXISTS_TAC ‘registers’ THEN
  Q.EXISTS_TAC ‘visited_bds'’ THEN
  Q.EXISTS_TAC ‘next_sop_bd_address’ THEN
  Q.EXISTS_TAC ‘bd’ THEN
  Q.EXISTS_TAC ‘uf’ THEN
  LRTAC THEN
  ASM_REWRITE_TAC [TX_BDS_OF_TRANSFERS_REC_EQ_VISITED_TX_BDS_TO_FETCH_SOP_LEMMA]
  ,
  RLTAC THEN ETAC listTheory.APPEND THEN ETAC listTheory.CONS_11 THEN
  WEAKEN_TAC (fn _ => true) THEN WEAKEN_TAC (fn _ => true) THEN WEAKEN_TAC (fn _ => true) THEN
  Q.EXISTS_TAC ‘F’ THEN
  Q.EXISTS_TAC ‘sop_li’ THEN
  Q.EXISTS_TAC ‘memory’ THEN
  Q.EXISTS_TAC ‘registers’ THEN
  Q.EXISTS_TAC ‘visited_bds''’ THEN
  Q.EXISTS_TAC ‘next_bd_address’ THEN
  Q.EXISTS_TAC ‘bd’ THEN
  Q.EXISTS_TAC ‘uf’ THEN
  CONJS_TAC THEN TRY STAC THEN
  PTAC visited_tx_bds_to_fetch THENL
  [
   ETAC listTheory.NULL_EQ THEN LRTAC THEN PTAC bbb_usb_functionsTheory.next_bd_pointer THEN LRTAC THEN PTAC bbb_usb_functionsTheory.eop_bd THEN IRTAC NO_BDS_TO_FETCH_NON_ZERO_START_BD_ADDRESS_IMPLIES_F_LEMMA THEN SOLVE_F_ASM_TAC
   ,
   PAT_X_ASSUM “visited_bds_option' = visited_bds_option : 32 interconnect_addresses_type option” (fn thm => ASSUME_TAC thm) THEN
   LRTAC THEN
   CONTR_ASMS_TAC
   ,
   ETAC boolTheory.bool_case_thm THEN RLTAC THEN CONTR_ASMS_TAC
   ,
   PAT_X_ASSUM “visited_bds_option' = visited_bds_option : 32 interconnect_addresses_type option” (fn thm => ASSUME_TAC thm) THEN
   LRTAC THEN
   RLTAC THEN
   RLTAC THEN
   ETAC boolTheory.bool_case_thm THEN
   STAC
  ]
 ]
]
QED

Theorem TX_BDS_TO_FETCH_BD_RAS_WAS_EQ_LEMMA_LEMMA:
!bds_to_fetch channel_id memory internal_state bd bd_ras bd_was uf.
  bds_to_fetch = tx_bds_to_fetch channel_id memory internal_state /\
  MEM ((bd, bd_ras, bd_was), uf) bds_to_fetch
  ==>
  bd_was = bd_ras
Proof
INTRO_TAC THEN
IRTAC NO_VISITED_BDS_IMPLIES_VISISTED_TX_BDS_TO_FETCH_EQ_TX_BDS_TO_FETCH_LEMMA THEN
QRLTAC THEN
IRTAC VISITED_TX_BDS_TO_FETCH_MEMBER_IMPLIES_WAS_EQ_RAS_LEMMA THEN
STAC
QED

Theorem TX_FETCH_BD_EFFECT_ENDPOINT_LEMMA:
!channel_id memory internal_state1 internal_state2 bd bds addresses tag bytes fetched_bd endpoint endpoint_id.
  32w <=+ channel_id /\ channel_id <=+ 91w /\
  endpoint_id = w2w ((channel_id - 32w) >>> 1) /\
  endpoint = internal_state1.endpoints_tx endpoint_id /\
  BDS_TO_FETCH_DISJOINT (bd::bds) /\
  bd::bds = tx_bds_to_fetch channel_id memory internal_state1 /\
  (addresses, tag) = tx_fetch_bd_addresses channel_id internal_state1 /\
  bytes = MAP memory addresses /\
  (internal_state2, SOME fetched_bd) = tx_fetch_bd channel_id internal_state1 (SOME (bytes, tag))
  ==>
  tx_bds_to_fetch channel_id memory internal_state2 = bds
Proof
INTRO_TAC THEN
ITAC FETCHED_TX_BD_EQ_HD_TX_BDS_TO_FETCH_LEMMA THEN RLTAC THEN
ITAC QHP_IN_FETCHED_TX_BD_RAS_LEMMA THEN
ITAC TX_FETCH_BD_RESULT_LEMMA THEN
AXTAC THEN
WEAKEN_TAC (fn _ => true) THEN WEAKEN_TAC (fn _ => true) THEN
EQ_PAIR_ASM_TAC THEN
NLRTAC 4 THEN
FITAC bbb_usb_queueTheory.BDS_TO_FETCH_DISJOINT_MEM_NOT_BD_RA_LEMMA THEN
ITAC NO_VISITED_BDS_IMPLIES_VISISTED_TX_BDS_TO_FETCH_EQ_TX_BDS_TO_FETCH_LEMMA THEN
QRLTAC THEN
Cases_on ‘eop_bd bd’ THENL
[
 FITAC FETCH_EOP_IMPLIES_SETS_SOP_LEMMA THEN
 Cases_on ‘endpoint.sop (word_bit 0 channel_id)’ THENL
 [
  Cases_on ‘li_to_eoq li’ THENL
  [
   ITAC FETCH_SOP_EOP_EOQ_QHP_EQ_ZERO_LEMMA THEN
   IRTAC QHP_EQ_ZERO_IMPLIES_TX_BDS_TO_FETCH_EQ_NULL THEN
   QLRTAC THEN
   ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
   MATCH_MP_TAC (REWRITE_RULE [VISITED_TX_BDS_TO_FETCH_START_ZERO_EQ_EMPTY_LEMMA] EOP_EOQ_FETCH_BD_IMPLIES_TAIL_VISITED_TX_BDS_TO_FETCH_LEMMA) THEN
   Q.EXISTS_TAC ‘(((bd,li),bd_ras',bd_ras'),no_update)’ THEN
   Q.EXISTS_TAC ‘[]’ THEN
   REWRITE_TAC [listTheory.APPEND, bbb_usb_queueTheory.NOT_BD_RA_EMPTY_LEMMA] THEN
   Q.EXISTS_TAC ‘[internal_state1.qhp channel_id]’ THEN
   PAXTAC THEN
   ALL_LRTAC THEN
   STAC
   ,
   ITAC FETCH_SOP_EOP_NOT_EOQ_QHP_EQ_NEXT_SOP_BD_ADDRESS_LEMMA THEN
   FITAC (Q.SPECL [‘channel_id’, ‘endpoint_id’, ‘internal_state2.endpoints_tx endpoint_id’, ‘internal_state2’] ENDPOINT_SOP_TX_BDS_TO_FETCH_EQ_VISITED_TX_BDS_TO_FETCH_LEMMA) THEN
   QLRTAC THEN
   RLTAC THEN
   ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
   MATCH_MP_TAC BDS_TO_FETCH_DISJOINT_NOT_BD_RA_IMPLIES_LEMMA THEN
   Q.EXISTS_TAC ‘[internal_state1.qhp channel_id]’ THEN
   ITAC bbb_usb_queueTheory.BDS_TO_FETCH_DISJOINT_TAIL_LEMMA THEN
   CONJS_TAC THEN TRY (ASM_REWRITE_TAC [bbb_usb_queueTheory.NOT_BD_RA_EMPTY_LEMMA] THEN STAC) THEN
   MATCH_MP_TAC ((GEN_ALL o DISCH_ALL o SPEC_ALL o UNDISCH o SPEC_ALL) EOP_NOT_EOQ_FETCH_BD_IMPLIES_TAIL_VISITED_TX_BDS_TO_FETCH_LEMMA) THEN
   Q.EXISTS_TAC ‘[]’ THEN
   REWRITE_TAC [listTheory.APPEND, listTheory.CONS_11] THEN
   Q.EXISTS_TAC ‘internal_state1.qhp channel_id’ THEN
   Q.EXISTS_TAC ‘li’ THEN
   Q.EXISTS_TAC ‘SOME (bytes, tag')’ THEN
   Q.EXISTS_TAC ‘bd_ras'’ THEN
   Q.EXISTS_TAC ‘channel_id’ THEN
   Q.EXISTS_TAC ‘word_bit 0 channel_id’ THEN
   Q.EXISTS_TAC ‘li’ THEN
   Q.EXISTS_TAC ‘internal_state1’ THEN
   Q.EXISTS_TAC ‘(((bd,li),bd_ras',bd_ras'),no_update)’ THEN
   Q.EXISTS_TAC ‘endpoint_id’ THEN
   EXISTS_EQ_TAC THEN
   REWRITE_TAC [bbb_usb_queueTheory.NOT_BD_RA_EMPTY_LEMMA] THEN
   CONJS_TAC THEN TRY STAC THEN
   IRTAC FETCH_SOP_EOP_NOT_EOQ_QHP_EQ_NEXT_SOP_BD_ADDRESS_LEMMA THEN
   STAC
  ]
  ,
  Cases_on ‘li_to_eoq (endpoint.sop_li (word_bit 0 channel_id))’ THENL
  [
   ITAC FETCH_NOT_SOP_EOP_EOQ_QHP_EQ_ZERO_LEMMA THEN
   IRTAC QHP_EQ_ZERO_IMPLIES_TX_BDS_TO_FETCH_EQ_NULL THEN
   QLRTAC THEN
   ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
   MATCH_MP_TAC (REWRITE_RULE [VISITED_TX_BDS_TO_FETCH_START_ZERO_EQ_EMPTY_LEMMA] EOP_EOQ_FETCH_BD_IMPLIES_TAIL_VISITED_TX_BDS_TO_FETCH_LEMMA) THEN
   Q.EXISTS_TAC ‘(((bd,li),bd_ras',bd_ras'),no_update)’ THEN
   Q.EXISTS_TAC ‘[]’ THEN
   REWRITE_TAC [listTheory.APPEND, bbb_usb_queueTheory.NOT_BD_RA_EMPTY_LEMMA] THEN
   Q.EXISTS_TAC ‘[internal_state1.qhp channel_id]’ THEN
   PAXTAC THEN
   ALL_LRTAC THEN
   STAC
   ,
   ITAC FETCH_NOT_SOP_EOP_NOT_EOQ_QHP_EQ_NEXT_SOP_BD_ADDRESS_LEMMA THEN
   FITAC (Q.SPECL [‘channel_id’, ‘endpoint_id’, ‘internal_state2.endpoints_tx endpoint_id’, ‘internal_state2’] ENDPOINT_SOP_TX_BDS_TO_FETCH_EQ_VISITED_TX_BDS_TO_FETCH_LEMMA) THEN
   QLRTAC THEN
   RLTAC THEN
   ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
   MATCH_MP_TAC BDS_TO_FETCH_DISJOINT_NOT_BD_RA_IMPLIES_LEMMA THEN
   Q.EXISTS_TAC ‘[internal_state1.qhp channel_id]’ THEN
   ITAC bbb_usb_queueTheory.BDS_TO_FETCH_DISJOINT_TAIL_LEMMA THEN
   CONJS_TAC THEN TRY (ASM_REWRITE_TAC [bbb_usb_queueTheory.NOT_BD_RA_EMPTY_LEMMA] THEN STAC) THEN
   MATCH_MP_TAC ((GEN_ALL o DISCH_ALL o SPEC_ALL o UNDISCH o SPEC_ALL) EOP_NOT_EOQ_FETCH_BD_IMPLIES_TAIL_VISITED_TX_BDS_TO_FETCH_LEMMA) THEN
   Q.EXISTS_TAC ‘[]’ THEN
   REWRITE_TAC [listTheory.APPEND, listTheory.CONS_11] THEN
   Q.EXISTS_TAC ‘internal_state1.qhp channel_id’ THEN
   Q.EXISTS_TAC ‘endpoint.sop_li (word_bit 0 channel_id)’ THEN
   Q.EXISTS_TAC ‘SOME (bytes, tag')’ THEN
   Q.EXISTS_TAC ‘bd_ras'’ THEN
   Q.EXISTS_TAC ‘channel_id’ THEN
   Q.EXISTS_TAC ‘word_bit 0 channel_id’ THEN
   Q.EXISTS_TAC ‘li’ THEN
   Q.EXISTS_TAC ‘internal_state1’ THEN
   Q.EXISTS_TAC ‘(((bd,li),bd_ras',bd_ras'),no_update)’ THEN
   Q.EXISTS_TAC ‘endpoint_id’ THEN
   EXISTS_EQ_TAC THEN
   REWRITE_TAC [bbb_usb_queueTheory.NOT_BD_RA_EMPTY_LEMMA] THEN
   CONJS_TAC THEN TRY STAC THEN
   IRTAC FETCH_NOT_SOP_EOP_NOT_EOQ_QHP_EQ_NEXT_SOP_BD_ADDRESS_LEMMA THEN
   STAC
  ]
 ]
 ,
 FITAC FETCH_NOT_EOP_IMPLIES_SETS_NOT_SOP_LEMMA THEN
 FITAC ENDPOINT_NOT_SOP_TX_BDS_TO_FETCH_EQ_VISITED_TX_BDS_TO_FETCH_LEMMA THEN
 QLRTAC THEN
 ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
 MATCH_MP_TAC BDS_TO_FETCH_DISJOINT_NOT_BD_RA_IMPLIES_LEMMA THEN
 Q.EXISTS_TAC ‘[internal_state1.qhp channel_id]’ THEN
 ITAC bbb_usb_queueTheory.BDS_TO_FETCH_DISJOINT_TAIL_LEMMA THEN
 CONJS_TAC THEN TRY (ASM_REWRITE_TAC [bbb_usb_queueTheory.NOT_BD_RA_EMPTY_LEMMA] THEN STAC) THEN
 MATCH_MP_TAC NOT_EOP_FETCH_BD_IMPLIES_TAIL_VISITED_TX_BDS_TO_FETCH_LEMMA THEN
 Q.EXISTS_TAC ‘(((bd,li),bd_ras',bd_ras'),no_update)’ THEN
 Q.EXISTS_TAC ‘[]’ THEN
 PAXTAC THEN
 FITAC FETCH_NOT_EOP_QHP_EQ_NEXT_BD_POINTER_LEMMA THEN
 ALL_LRTAC THEN
 ASM_REWRITE_TAC [listTheory.APPEND, bbb_usb_queueTheory.NOT_BD_RA_EMPTY_LEMMA]
]
QED

Theorem CHANNEL_ID_ENDPOINT_LEMMA:
!channel_id internal_state.
  ?endpoint_id endpoint.
    endpoint_id = w2w ((channel_id - 32w) >>> 1) /\
    endpoint = internal_state.endpoints_tx endpoint_id
Proof
REPEAT GEN_TAC THEN
EXISTS_EQ_TAC
QED

Theorem TX_FETCH_BD_EFFECT_LEMMA:
!channel_id memory internal_state1 internal_state2 bd bds addresses tag bytes fetched_bd.
  32w <=+ channel_id /\ channel_id <=+ 91w /\
  BDS_TO_FETCH_DISJOINT (bd::bds) /\
  bd::bds = tx_bds_to_fetch channel_id memory internal_state1 /\
  (addresses, tag) = tx_fetch_bd_addresses channel_id internal_state1 /\
  bytes = MAP memory addresses /\
  (internal_state2, SOME fetched_bd) = tx_fetch_bd channel_id internal_state1 (SOME (bytes, tag))
  ==>
  tx_bds_to_fetch channel_id memory internal_state2 = bds
Proof
INTRO_TAC THEN
ASSUME_TAC CHANNEL_ID_ENDPOINT_LEMMA THEN
IRTAC TX_FETCH_BD_EFFECT_ENDPOINT_LEMMA THEN
STAC
QED

val _ = export_theory();

