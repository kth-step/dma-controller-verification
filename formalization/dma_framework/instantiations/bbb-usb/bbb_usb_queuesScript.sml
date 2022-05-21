open HolKernel Parse boolLib bossLib helper_tactics;
open bbb_usb_instantiationTheory;

val _ = new_theory "bbb_usb_queues";

Definition BDS_TO_FETCH_RAS_WAS_DISJOINT:
BDS_TO_FETCH_RAS_WAS_DISJOINT bds_to_fetch =
!bd1 bd_ras1 bd_was1 uf1 bd2 bd_ras2 bd_was2 uf2 preceding_bds following_bds.
  preceding_bds ++ [((bd1, bd_ras1, bd_was1), uf1)] ++ following_bds = bds_to_fetch /\
  MEM ((bd2, bd_ras2, bd_was2), uf2) (preceding_bds ++ following_bds)
  ==>
  DISJOINT_LISTS bd_was1 bd_ras2
End

Theorem NOT_LEQ_31_IMPLIES_GEQ_32_LEMMA:
!channel_id : 8 word.
  ~(channel_id <=+ 31w)
  ==>
  32w <=+ channel_id
Proof
blastLib.BBLAST_TAC
QED

Theorem BDS_TO_FETCH_RAS_WAS_DISJOINT_IMPLIES_BDS_TO_FETCH_RAS_RAS_DISJOINT_LEMMA:
!memory internal_state channel_id bds_to_fetch.
  VALID_CHANNEL_ID bbb_usb_device_characteristics channel_id /\
  bds_to_fetch = (cverification bbb_usb_device_characteristics channel_id).bds_to_fetch memory internal_state /\
  BDS_TO_FETCH_RAS_WAS_DISJOINT bds_to_fetch
  ==>
  BDS_TO_FETCH_DISJOINT bds_to_fetch
Proof
REWRITE_TAC [BDS_TO_FETCH_RAS_WAS_DISJOINT, bd_queuesTheory.BDS_TO_FETCH_DISJOINT, stateTheory.VALID_CHANNEL_ID] THEN
REWRITE_TAC [stateTheory.cverification, bbb_usb_device_characteristics, bbb_usb_dma_characteristics] THEN
RECORD_TAC THEN
INTRO_TAC THEN
INTRO_TAC THEN
AITAC THEN
ETAC bbb_usb_verification THEN
IF_SPLIT_TAC THENL
[
 ETAC optionTheory.THE_DEF THEN
 ETAC rx_verification THEN
 RECORD_TAC THEN
 ITAC lists_lemmasTheory.MEM_PRECEDING_FOLLOWING_IMPLIES_MEM_MID_LEMMA THEN
 IRTAC bbb_usb_queue_rxTheory.RX_BDS_TO_FETCH_BD_RAS_WAS_EQ_LEMMA THEN
 STAC
 ,
 IRTAC NOT_LEQ_31_IMPLIES_GEQ_32_LEMMA THEN
 IF_SPLIT_TAC THEN TRY (ETAC boolTheory.DE_MORGAN_THM THEN SPLIT_ASM_DISJS_TAC THEN CONTR_ASMS_TAC) THEN
 ETAC optionTheory.THE_DEF THEN
 ETAC tx_verification THEN
 RECORD_TAC THEN
 ITAC lists_lemmasTheory.MEM_PRECEDING_FOLLOWING_IMPLIES_MEM_MID_LEMMA THEN
 IRTAC bbb_usb_queue_txTheory.TX_BDS_TO_FETCH_BD_RAS_WAS_EQ_LEMMA_LEMMA THEN
 STAC
]
QED

Theorem BETWEEN_31_32_IMPLIES_F_LEMMA:
!channel_id : 8 word.
  31w <+ channel_id /\
  channel_id <+ 32w
  ==>
  F
Proof
blastLib.BBLAST_TAC
QED

Theorem GT_91_LEQ_91_IMPLIES_F_LEMMA:
!channel_id : 8 word.
  91w <+ channel_id /\
  channel_id <=+ 91w
  ==>
  F
Proof
blastLib.BBLAST_TAC
QED

Theorem BBB_USB_DEVICE_PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT_LEMMA:
  PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT bbb_usb_device_characteristics
Proof
ETAC proof_obligationsTheory.PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT THEN
REWRITE_TAC [bbb_usb_instantiationTheory.bbb_usb_device_characteristics, bbb_usb_instantiationTheory.bbb_usb_dma_characteristics] THEN
REWRITE_TAC [stateTheory.coperation, stateTheory.VALID_CHANNEL_ID, stateTheory.cverification, stateTheory.EXTERNAL_BDS] THEN
RECORD_TAC THEN
REWRITE_TAC [] THEN
INTRO_TAC THEN
ETAC bbb_usb_instantiationTheory.bbb_usb_operation THEN
ETAC bbb_usb_instantiationTheory.bbb_usb_verification THEN
REPEAT IF_SPLIT_TAC THENL
[
 ETAC optionTheory.THE_DEF THEN
 ETAC bbb_usb_instantiationTheory.rx_operation THEN
 ETAC bbb_usb_instantiationTheory.rx_verification THEN
 RECORD_TAC THEN
 IRTAC bbb_usb_queue_rxTheory.RX_FETCH_BD_EFFECT_LEMMA THEN
 STAC
 ,
 ETAC optionTheory.THE_DEF THEN
 ETAC bbb_usb_instantiationTheory.tx_operation THEN
 ETAC bbb_usb_instantiationTheory.tx_verification THEN
 RECORD_TAC THEN
 IRTAC bbb_usb_queue_txTheory.TX_FETCH_BD_EFFECT_LEMMA THEN
 STAC
 ,
 ETAC boolTheory.DE_MORGAN_THM THEN
 SPLIT_ASM_DISJS_TAC THEN
  ETAC wordsTheory.WORD_NOT_LOWER_EQUAL THEN ((FIRTAC BETWEEN_31_32_IMPLIES_F_LEMMA) ORELSE (FIRTAC GT_91_LEQ_91_IMPLIES_F_LEMMA)) THEN SOLVE_F_ASM_TAC
]
QED



Definition INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4:
INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4 device_characteristics memory device =
!channel_id bd1 bd_ras1 bd_was1 uf1 bd2 bd_ras2 bd_was2 uf2 bds_to_fetch preceding_bds following_bds.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory device.dma_state.internal_state /\
  preceding_bds ++ [((bd1, bd_ras1, bd_was1), uf1)] ++ following_bds = bds_to_fetch /\
  MEM ((bd2, bd_ras2, bd_was2), uf2) (preceding_bds ++ following_bds)
  ==>
  DISJOINT_LISTS bd_was1 bd_ras2
End

Theorem INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4_IMPLIES_BDS_TO_FETCH_RAS_WAS_DISJOINT_LEMMA:
!device_characteristics memory device bds_to_fetch channel_id.
  INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4 device_characteristics memory device /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory device.dma_state.internal_state
  ==>
  BDS_TO_FETCH_RAS_WAS_DISJOINT bds_to_fetch
Proof
INTRO_TAC THEN
ETAC INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4 THEN
ETAC BDS_TO_FETCH_RAS_WAS_DISJOINT THEN
INTRO_TAC THEN
FAIRTAC THEN
STAC
QED


val _ = export_theory();

