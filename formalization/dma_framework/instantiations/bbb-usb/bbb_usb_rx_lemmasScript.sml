open HolKernel Parse boolLib bossLib helper_tactics;
open bbb_usb_rxTheory;

val _ = new_theory "bbb_usb_rx_lemmas";

Theorem RX_BD_TRANSFER_RAS_WAS_DEPENDS_ON_BD_LEMMA:
!(internal_state1 : internal_state_type) (internal_state2 : internal_state_type) bd.
  rx_bd_transfer_ras_was internal_state1 bd = rx_bd_transfer_ras_was internal_state2 bd
Proof
REPEAT GEN_TAC THEN
REPEAT (PTAC bbb_usb_rxTheory.rx_bd_transfer_ras_was) THEN
STAC
QED

Theorem ENDPOINT_SCHEDULABLE_RX_IMPLIES_SOME_QUEUE_ID_LEQ_91_LEMMA:
!internal_state1 internal_state2 channels endpoint_id queue_id environment.
  SOME (internal_state2, queue_id) = endpoint_schedulable_rx environment internal_state1 channels endpoint_id
  ==>
  queue_id <=+ 91w
Proof
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.endpoint_schedulable_rx THEN
PTAC bbb_usb_schedulerTheory.validate_queue_id THENL
[
 HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
 ,
 ETAC optionTheory.SOME_11 THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
]
QED

Theorem IS_RX_SOP_WRITTEN_BACK_IMPLIES_CHANNEL_ID_LEQ_91_LEMMA:
!internal_state1 internal_state2 bds_to_write_back channel_id channel_id' dma_operation.
  ~(channel_id >=+ 32w) /\
  SOME (internal_state2, channel_id', dma_operation) = is_rx_sop_written_back internal_state1 bds_to_write_back channel_id
  ==>
  channel_id' <=+ 91w
Proof
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.is_rx_sop_written_back THEN TRY (HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE) THEN
ETAC optionTheory.SOME_11 THEN
EQ_PAIR_ASM_TAC THEN
ETAC wordsTheory.WORD_HIGHER_EQ THEN
ETAC wordsTheory.WORD_NOT_LOWER_EQUAL THEN
IRTAC bbb_usb_lemmasTheory.LT_32_IMPLIES_LEQ_91_LEMMA THEN
STAC
QED

Theorem IS_RX_BD_POPPED_IMPLIES_CHANNEL_ID_LEQ_91_LEMMA:
!internal_state1 internal_state2 bds_to_write_back channel_id channel_id' dma_operation.
  ~(channel_id >=+ 32w) /\
  SOME (internal_state2, channel_id', dma_operation) = is_rx_bd_popped internal_state1 bds_to_write_back channel_id
  ==>
  channel_id' <=+ 91w
Proof
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.is_rx_bd_popped THEN TRY (HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE) THEN
ETAC optionTheory.SOME_11 THEN
EQ_PAIR_ASM_TAC THEN
ETAC wordsTheory.WORD_HIGHER_EQ THEN
ETAC wordsTheory.WORD_NOT_LOWER_EQUAL THEN
IRTAC bbb_usb_lemmasTheory.LT_32_IMPLIES_LEQ_91_LEMMA THEN
STAC
QED

Theorem IS_RX_WRITE_BACK_IMPLIES_CHANNEL_ID_LEQ_91_IND_LEMMA:
!queue_id internal_state1 channels.
  (\internal_state1 channels queue_id.
   !internal_state2 dma_operation channel_id.
    SOME (internal_state2, channel_id, dma_operation) = is_rx_write_back internal_state1 channels queue_id
    ==>
    channel_id <=+ 91w) internal_state1 channels queue_id
Proof
MATCH_MP_TAC bbb_usb_schedulerTheory.is_rx_write_back_ind THEN
BETA_TAC THEN
INTRO_TAC THEN
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.is_rx_write_back THENL
[
 HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
 ,
 PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
 LRTAC THEN
 ETAC optionTheory.SOME_11 THEN
 RLTAC THEN
 IRTAC IS_RX_SOP_WRITTEN_BACK_IMPLIES_CHANNEL_ID_LEQ_91_LEMMA THEN
 STAC
 ,
 PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
 LRTAC THEN
 LRTAC THEN
 IRTAC IS_RX_BD_POPPED_IMPLIES_CHANNEL_ID_LEQ_91_LEMMA THEN
 STAC
 ,
 AIRTAC THEN AIRTAC THEN STAC
 ,
 HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
]
QED

Theorem IS_RX_WRITE_BACK_IMPLIES_CHANNEL_ID_LEQ_91_LEMMA:
!queue_id internal_state1 internal_state2 channels dma_operation channel_id.
  SOME (internal_state2, channel_id, dma_operation) = is_rx_write_back internal_state1 channels queue_id
  ==>
  channel_id <=+ 91w
Proof
REWRITE_TAC [BETA_RULE IS_RX_WRITE_BACK_IMPLIES_CHANNEL_ID_LEQ_91_IND_LEMMA]
QED

Theorem IS_RX_WRITE_BACK_PRESERVES_REGISTERS_QHP_IND_LEMMA:
!queue_id internal_state1 channels.
  (\internal_state1 channels queue_id.
   !internal_state2 dma_operation channel_id.
    SOME (internal_state2, channel_id, dma_operation) = is_rx_write_back internal_state1 channels queue_id
    ==>
    internal_state2.registers = internal_state1.registers /\
    internal_state2.qhp = internal_state1.qhp) queue_id internal_state1 channels
Proof
MATCH_MP_TAC bbb_usb_schedulerTheory.is_rx_write_back_ind THEN
BETA_TAC THEN
INTRO_TAC THEN
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.is_rx_write_back THENL
[
 HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
 ,
 PTAC bbb_usb_schedulerTheory.is_rx_sop_written_back THENL
 [
  WEAKEN_TAC is_forall THEN NLRTAC 2 THEN ETAC optionTheory.SOME_11 THEN EQ_PAIR_ASM_TAC THEN LRTAC THEN RECORD_TAC THEN STAC
  ,
  LRTAC THEN PTAC optionTheory.IS_SOME_DEF THEN SOLVE_F_ASM_TAC
 ]
 ,
 RLTAC THEN
 PTAC bbb_usb_schedulerTheory.is_rx_bd_popped THENL
 [
  ETAC optionTheory.SOME_11 THEN EQ_PAIR_ASM_TAC THEN RLTAC THEN LRTAC THEN RECORD_TAC THEN STAC
  ,
  HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
 ]
 ,
 AIRTAC THEN AIRTAC THEN STAC
 ,
 HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
]
QED

Theorem IS_RX_WRITE_BACK_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_IND_LEMMA:
!queue_id internal_state1 channels.
  (\internal_state1 channels queue_id.
   !internal_state2 dma_operation channel_id.
    SOME (internal_state2, channel_id, dma_operation) = is_rx_write_back internal_state1 channels queue_id
    ==>
    ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx) queue_id internal_state1 channels
Proof
MATCH_MP_TAC bbb_usb_schedulerTheory.is_rx_write_back_ind THEN
BETA_TAC THEN
INTRO_TAC THEN
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.is_rx_write_back THENL
[
 HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
 ,
 PTAC bbb_usb_schedulerTheory.is_rx_sop_written_back THENL
 [
  ALL_LRTAC THEN ETAC optionTheory.SOME_11 THEN EQ_PAIR_ASM_TAC THEN LRTAC THEN RECORD_TAC THEN REWRITE_TAC [bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ_REFL_LEMMA]
  ,
  LRTAC THEN PTAC optionTheory.IS_SOME_DEF THEN SOLVE_F_ASM_TAC
 ]
 ,
 RLTAC THEN
 PTAC bbb_usb_schedulerTheory.is_rx_bd_popped THENL
 [
  ETAC optionTheory.SOME_11 THEN EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN RECORD_TAC THEN REWRITE_TAC [bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ_REFL_LEMMA]
  ,
  HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
 ]
 ,
 AIRTAC THEN AIRTAC THEN STAC
 ,
 HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
]
QED

Theorem IS_RX_WRITE_BACK_PRESERVES_REGISTERS_QHP_LEMMA:
!queue_id internal_state1 channels internal_state2 dma_operation channel_id.
  SOME (internal_state2, channel_id, dma_operation) = is_rx_write_back internal_state1 channels queue_id
  ==>
  internal_state2.registers = internal_state1.registers /\
  internal_state2.qhp = internal_state1.qhp
Proof
REWRITE_TAC [BETA_RULE IS_RX_WRITE_BACK_PRESERVES_REGISTERS_QHP_IND_LEMMA]
QED

Theorem IS_RX_WRITE_BACK_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA:
!queue_id internal_state1 channels internal_state2 dma_operation channel_id.
  SOME (internal_state2, channel_id, dma_operation) = is_rx_write_back internal_state1 channels queue_id
  ==>
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
REWRITE_TAC [BETA_RULE IS_RX_WRITE_BACK_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_IND_LEMMA]
QED

Theorem QMEM_LRAM_EQ_QHP_EQ_IMPLIEX_RX_BDS_TO_FETCH_REC_EQ_IND_LEMMA:
!memory registers1 visited_bds bd_address.
  (\memory registers1 visited_bds bd_address.
   !registers2.
     QMEM_LRAM_EQ registers1 registers2
     ==>
     rx_bds_to_fetch_rec memory registers2 visited_bds bd_address =
     rx_bds_to_fetch_rec memory registers1 visited_bds bd_address) memory registers1 visited_bds bd_address
Proof
MATCH_MP_TAC bbb_usb_queue_rxTheory.rx_bds_to_fetch_rec_ind THEN
APP_SCALAR_TAC THEN
INTRO_TAC THEN
INTRO_TAC THEN
PTAC bbb_usb_queue_rxTheory.rx_bds_to_fetch_rec THENL
[
 PTAC bbb_usb_queue_rxTheory.rx_bds_to_fetch_rec THEN STAC
 ,
 PTAC bbb_usb_queue_rxTheory.rx_bds_to_fetch_rec THEN
 IRTAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ_IMPLIES_GET_BD_RAS_EQ_LEMMA THEN
 QLRTAC THEN
 PAT_X_ASSUM “bd_ras' = get_bd_ras registers bd_address” (fn thm => ASSUME_TAC thm) THEN
 RLTAC THEN
 RLTAC THEN
 RLTAC THEN
 RLTAC THEN
 LRTAC THEN
 STAC
 ,
 PTAC bbb_usb_queue_rxTheory.rx_bds_to_fetch_rec THENL
 [
  IRTAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ_IMPLIES_GET_BD_RAS_EQ_LEMMA THEN
  QLRTAC THEN
  PAT_X_ASSUM “bd_ras' = get_bd_ras registers bd_address” (fn thm => ASSUME_TAC thm) THEN
  RLTAC THEN
  RLTAC THEN
  RLTAC THEN
  RLTAC THEN
  LRTAC THEN
  STAC
  ,
  IRTAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ_IMPLIES_GET_BD_RAS_EQ_LEMMA THEN
  QLRTAC THEN
  PAT_X_ASSUM “bd_ras' = get_bd_ras registers bd_address” (fn thm => ASSUME_TAC thm) THEN
  RLTAC THEN
  RLTAC THEN
  RLTAC THEN
  RLTAC THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 2 THEN
  CONTR_ASMS_TAC
 ]
 ,
 ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
 PTAC bbb_usb_queue_rxTheory.rx_bds_to_fetch_rec THENL
 [
  IRTAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ_IMPLIES_GET_BD_RAS_EQ_LEMMA THEN
  QLRTAC THEN
  PAT_X_ASSUM “bd_ras' = get_bd_ras registers bd_address” (fn thm => ASSUME_TAC thm) THEN
  RLTAC THEN
  RLTAC THEN
  RLTAC THEN
  RLTAC THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 2 THEN
  CONTR_ASMS_TAC
  ,
  AITAC THEN
  AITAC THEN
  ITAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ_IMPLIES_GET_BD_RAS_EQ_LEMMA THEN
  IRTAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ_IMPLIES_LI_TO_NEXT_BD_ADDRESS_EQ_LEMMA THEN
  QLRTAC THEN
  QLRTAC THEN
  PAT_X_ASSUM “bd_ras' = get_bd_ras registers bd_address” (fn thm => ASSUME_TAC thm) THEN
  RLTAC THEN
  RLTAC THEN
  RLTAC THEN
  RLTAC THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 2 THEN
  REWRITE_TAC [listTheory.CONS_11] THEN
  RLTAC THEN
  RLTAC THEN
  STAC
 ]
]
QED

Theorem QMEM_LRAM_EQ_QHP_EQ_IMPLIES_RX_BDS_TO_FETCH_REC_EQ_IND_LEMMA:
!registers1 registers2.
  QMEM_LRAM_EQ registers1 registers2
  ==>
  !memory visited_bds bd_address.
    rx_bds_to_fetch_rec memory registers2 visited_bds bd_address = rx_bds_to_fetch_rec memory registers1 visited_bds bd_address
Proof
INTRO_TAC THEN
IRTAC (BETA_RULE QMEM_LRAM_EQ_QHP_EQ_IMPLIEX_RX_BDS_TO_FETCH_REC_EQ_IND_LEMMA) THEN
STAC
QED

Theorem QMEM_LRAM_EQ_QHP_EQ_IMPLIES_RX_BDS_TO_FETCH_EQ_LEMMA:
!internal_state1 internal_state2 memory channel_id.
  QMEM_LRAM_EQ internal_state1.registers internal_state2.registers /\
  internal_state2.qhp = internal_state1.qhp
  ==>
  rx_bds_to_fetch channel_id memory internal_state2 = rx_bds_to_fetch channel_id memory internal_state1
Proof
INTRO_TAC THEN
ETAC bbb_usb_queue_rxTheory.rx_bds_to_fetch THEN
IRTAC QMEM_LRAM_EQ_QHP_EQ_IMPLIES_RX_BDS_TO_FETCH_REC_EQ_IND_LEMMA THEN
STAC
QED

Theorem RX_FETCH_BD_RESULT_LEMMA:
!internal_state1 internal_state2 channel_id fetched_bd_ras_was fetched_bd_update bytes tag.
  (internal_state2, SOME (fetched_bd_ras_was, fetched_bd_update)) = rx_fetch_bd channel_id internal_state1 (SOME (bytes, tag))
  ==>
  fetched_bd_ras_was = (form_bd_li bytes, get_bd_ras internal_state1.registers (internal_state1.qhp channel_id), get_bd_ras internal_state1.registers (internal_state1.qhp channel_id)) /\
  fetched_bd_update = no_update
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.rx_fetch_bd THEN TRY (EQ_PAIR_ASM_TAC THEN IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC) THEN
EQ_PAIR_ASM_TAC THEN
ETAC optionTheory.SOME_11 THEN
EQ_PAIR_ASM_TAC THEN
ALL_LRTAC THEN
STAC
QED

Theorem RX_FETCH_BD_ADDRESSES_RESULT_LEMMA:
!channel_id internal_state addresses tag.
  internal_state.qhp channel_id <> 0w /\
  (addresses, tag) = rx_fetch_bd_addresses channel_id internal_state
  ==>
  addresses = get_bd_ras internal_state.registers (internal_state.qhp channel_id)
Proof
INTRO_TAC THEN
ETAC bbb_usb_rxTheory.rx_fetch_bd_addresses THEN
IF_SPLIT_TAC THEN TRY CONTR_ASMS_TAC THEN
EQ_PAIR_ASM_TAC THEN
STAC
QED

Theorem RX_BDS_TO_FETCH_RESULT_LEMMA:
!channel_id memory internal_state bd bd_ras bd_was first_bd_update bds.
  ((bd, bd_ras, bd_was), first_bd_update)::bds = rx_bds_to_fetch channel_id memory internal_state
  ==>
  bd_ras = get_bd_ras internal_state.registers (internal_state.qhp channel_id) /\
  bd_was = get_bd_ras internal_state.registers (internal_state.qhp channel_id) /\
  first_bd_update = no_update /\
  ?bytes.
    bytes = MAP memory bd_ras /\
    bd = form_bd_li bytes
Proof
INTRO_TAC THEN
ETAC bbb_usb_queue_rxTheory.rx_bds_to_fetch THEN
PTAC bbb_usb_queue_rxTheory.rx_bds_to_fetch_rec THEN TRY (HYP_CONTR_NEQ_LEMMA_TAC listTheory.NOT_CONS_NIL) THEN
 ETAC listTheory.CONS_11 THEN EQ_PAIR_ASM_TAC THEN NRLTAC 3 THEN ASM_REWRITE_TAC [] THEN PAXTAC THEN STAC
QED

Theorem NOT_EMPTY_RX_BDS_TO_FETCH_IMPLIES_QHP_NEQ_ZERO_LEMMA:
!channel_id memory internal_state bd bds.
  bd::bds = rx_bds_to_fetch channel_id memory internal_state
  ==>
  internal_state.qhp channel_id <> 0w
Proof
INTRO_TAC THEN
PTAC bbb_usb_queue_rxTheory.rx_bds_to_fetch THEN
PTAC bbb_usb_queue_rxTheory.rx_bds_to_fetch_rec THEN TRY STAC THEN
IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
QED

Theorem FETCHED_BD_IS_FIRST_RX_LEMMA:
!channel_id internal_state1 internal_state2 addresses tag bytes memory
 fetched_bd_ras_was fetched_bd_update bd bd_ras bd_was first_bd_update bds.
  (addresses, tag) = rx_fetch_bd_addresses channel_id internal_state1 /\
  bytes = MAP memory addresses /\
  (internal_state2, SOME (fetched_bd_ras_was, fetched_bd_update)) = rx_fetch_bd channel_id internal_state1 (SOME (bytes, tag)) /\
  ((bd, bd_ras, bd_was), first_bd_update)::bds = rx_bds_to_fetch channel_id memory internal_state1
  ==>
  (bd, bd_ras, bd_was) = fetched_bd_ras_was /\
  first_bd_update = fetched_bd_update
Proof
INTRO_TAC THEN
ITAC NOT_EMPTY_RX_BDS_TO_FETCH_IMPLIES_QHP_NEQ_ZERO_LEMMA THEN
IRTAC RX_FETCH_BD_RESULT_LEMMA THEN
LRTAC THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
LRTAC THEN
IRTAC RX_FETCH_BD_ADDRESSES_RESULT_LEMMA THEN
IRTAC RX_BDS_TO_FETCH_RESULT_LEMMA THEN
AXTAC THEN
STAC
QED

Theorem QHP_EQ_ZERO_IMPLIES_RX_FETCH_BD_ADDRESSES_EMPTY_LEMMA:
!channel_id internal_state addresses tag.
  internal_state.qhp channel_id = 0w /\
  (addresses, tag) = rx_fetch_bd_addresses channel_id internal_state
  ==>
  addresses = []
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.rx_fetch_bd_addresses THEN
EQ_PAIR_ASM_TAC THEN
STAC
QED

Theorem RX_BDS_TO_FETCH_EMPTY_IMPLIES_QHP_EQ_ZERO_LEMMA:
!channel_id memory internal_state.
  rx_bds_to_fetch channel_id memory internal_state = []
  ==>
  internal_state.qhp channel_id = 0w
Proof
INTRO_TAC THEN
PTAC bbb_usb_queue_rxTheory.rx_bds_to_fetch THEN
PTAC bbb_usb_queue_rxTheory.rx_bds_to_fetch_rec THEN
(STAC ORELSE ITAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC)
QED

Theorem RX_BDS_TO_FETCH_EMPTY_IMPLIES_RX_FETCH_BD_ADDRESSES_EMPTY_LEMMA:
!channel_id memory internal_state addresses tag.
  rx_bds_to_fetch channel_id memory internal_state = [] /\
  rx_fetch_bd_addresses channel_id internal_state = (addresses, tag)
  ==>
  addresses = []
Proof
INTRO_TAC THEN
IRTAC RX_BDS_TO_FETCH_EMPTY_IMPLIES_QHP_EQ_ZERO_LEMMA THEN
IRTAC QHP_EQ_ZERO_IMPLIES_RX_FETCH_BD_ADDRESSES_EMPTY_LEMMA THEN
STAC
QED

Theorem RX_FETCH_BD_PRESERVES_REGISTERS_LEMMA:
!channel_id internal_state1 internal_state2 reply fetch_result.
  (internal_state2, fetch_result) = rx_fetch_bd channel_id internal_state1 reply
  ==>
  internal_state2.registers = internal_state1.registers
Proof
INTRO_TAC THEN PTAC bbb_usb_rxTheory.rx_fetch_bd THEN EQ_PAIR_ASM_TAC THEN TRY STAC THEN
RLTAC THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [combinTheory.UPDATE_def] THEN
APP_SCALAR_TAC THEN
ASM_REWRITE_TAC []
QED

Theorem RX_FETCH_BD_PRESERVES_OTHER_CHANNELS_QHP_LEMMA:
!channel_id channel_id' internal_state1 internal_state2 reply fetch_result.
  channel_id' <> channel_id /\
  (internal_state2, fetch_result) = rx_fetch_bd channel_id internal_state1 reply
  ==>
  internal_state2.qhp channel_id' = internal_state1.qhp channel_id'
Proof
INTRO_TAC THEN PTAC bbb_usb_rxTheory.rx_fetch_bd THEN EQ_PAIR_ASM_TAC THEN TRY ((IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC) ORELSE STAC) THEN
RLTAC THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [combinTheory.UPDATE_def] THEN
APP_SCALAR_TAC THEN
PAT_X_ASSUM “x <> x' : 8 word” (fn thm => ASSUME_TAC (GSYM thm)) THEN
ASM_REWRITE_TAC []
QED

Theorem RX_FETCH_BD_PRESERVES_ENDPOINTS_TX_LEMMA:
!channel_id internal_state1 internal_state2 reply fetch_result.
  (internal_state2, fetch_result) = rx_fetch_bd channel_id internal_state1 reply
  ==>
  internal_state2.endpoints_tx = internal_state1.endpoints_tx
Proof
INTRO_TAC THEN PTAC bbb_usb_rxTheory.rx_fetch_bd THEN EQ_PAIR_ASM_TAC THEN TRY STAC THEN RLTAC THEN LRTAC THEN RECORD_TAC THEN STAC
QED

Theorem EQ_REGISTERS_QHP_PRESERVES_RX_FETCH_BD_ADDRESSES_LEMMA:
!channel_id internal_state1 internal_state2.
  internal_state2.registers = internal_state1.registers /\
  internal_state2.qhp channel_id = internal_state1.qhp channel_id
  ==>
  rx_fetch_bd_addresses channel_id internal_state2 = rx_fetch_bd_addresses channel_id internal_state1
Proof
INTRO_TAC THEN ETAC bbb_usb_rxTheory.rx_fetch_bd_addresses THEN STAC
QED

Theorem RX_BDS_TO_FETCH_REC_MEMORY_DEPENDENCE_LEMMA:
!memory1 registers visited_bds bd_address.
  (\memory1 registers visited_bds bd_address.
   !memory2 bds_to_fetch1 ras1.
    bds_to_fetch1 = rx_bds_to_fetch_rec memory1 registers visited_bds bd_address /\
    ras1 = bds_to_fetch_ras bds_to_fetch1 /\
    MEMORY_EQ ras1 memory1 memory2
    ==>
    rx_bds_to_fetch_rec memory2 registers visited_bds bd_address = bds_to_fetch1) memory1 registers visited_bds bd_address
Proof
MATCH_MP_TAC bbb_usb_queue_rxTheory.rx_bds_to_fetch_rec_ind THEN
BETA_TAC THEN
INTRO_TAC THEN
INTRO_TAC THEN
PTAC bbb_usb_queue_rxTheory.rx_bds_to_fetch_rec THENL
[
 ETAC bbb_usb_queue_rxTheory.RX_BDS_TO_FETCH_REC_BD_ADDRESS_ZERO_EQ_EMPTY_LEMMA THEN STAC
 ,
 PTAC bbb_usb_queue_rxTheory.rx_bds_to_fetch_rec THEN
 LRTAC THEN
 ETAC bd_queuesTheory.bds_to_fetch_ras THEN
 ETAC listTheory.APPEND_NIL THEN
 LRTAC THEN
 WEAKEN_TAC is_forall THEN
 IRTAC bbb_usb_lemmasTheory.MEMORY_EQ_IMPLIES_MAP_MEMORY_EQ_LEMMA THEN
 LRTAC THEN
 RLTAC THEN
 RLTAC THEN
 LRTAC THEN
 STAC
 ,
 WEAKEN_TAC is_forall THEN
 PTAC bbb_usb_queue_rxTheory.rx_bds_to_fetch_rec THENL
 [
  LRTAC THEN
  ETAC bd_queuesTheory.bds_to_fetch_ras THEN
  ETAC listTheory.APPEND_NIL THEN
  LRTAC THEN
  IRTAC bbb_usb_lemmasTheory.MEMORY_EQ_IMPLIES_MAP_MEMORY_EQ_LEMMA THEN
  LRTAC THEN
  RLTAC THEN
  RLTAC THEN
  LRTAC THEN
  STAC
  ,
  LRTAC THEN
  ETAC bd_queuesTheory.bds_to_fetch_ras THEN
  LRTAC THEN
  IRTAC bbb_usb_lemmasTheory.MEMORY_EQ_APPEND_LEMMA THEN
  IRTAC bbb_usb_lemmasTheory.MEMORY_EQ_IMPLIES_MAP_MEMORY_EQ_LEMMA THEN
  LRTAC THEN
  RLTAC THEN
  RLTAC THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  NRLTAC 2 THEN
  CONTR_ASMS_TAC
 ]
 ,
 RW_HYP_LEMMA_TAC bbb_usb_queue_rxTheory.rx_bds_to_fetch_rec THEN
 IF_SPLIT_TAC THEN TRY CONTR_ASMS_TAC THEN
 LETS_TAC THEN
 IF_SPLIT_TAC THEN1 (LRTAC THEN ETAC bd_queuesTheory.bds_to_fetch_ras THEN ETAC listTheory.APPEND_NIL THEN LRTAC THEN IRTAC bbb_usb_lemmasTheory.MEMORY_EQ_IMPLIES_MAP_MEMORY_EQ_LEMMA THEN LRTAC THEN RLTAC THEN RLTAC THEN LRTAC THEN EQ_PAIR_ASM_TAC THEN NRLTAC 2 THEN CONTR_ASMS_TAC) THEN
 AITAC THEN
 LRTAC THEN
 ETAC bd_queuesTheory.bds_to_fetch_ras THEN
 LRTAC THEN
 IRTAC bbb_usb_lemmasTheory.MEMORY_EQ_APPEND_LEMMA THEN
 IRTAC bbb_usb_lemmasTheory.MEMORY_EQ_IMPLIES_MAP_MEMORY_EQ_LEMMA THEN
 LRTAC THEN RLTAC THEN RLTAC THEN LRTAC THEN EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN REWRITE_TAC [listTheory.CONS_11] THEN
 RLTAC THEN
 RLTAC THEN
 AIRTAC THEN
 STAC
]
QED

Theorem RX_BDS_TO_FETCH_MEMORY_DEPENDENCE_LEMMA:
!channel_id memory1 memory2 internal_state bds_to_fetch1 ras1.
  bds_to_fetch1 = rx_bds_to_fetch channel_id memory1 internal_state /\
  ras1 = bds_to_fetch_ras bds_to_fetch1 /\
  MEMORY_EQ ras1 memory1 memory2
  ==>
  rx_bds_to_fetch channel_id memory2 internal_state = bds_to_fetch1
Proof
REWRITE_TAC [bbb_usb_queue_rxTheory.rx_bds_to_fetch, BETA_RULE RX_BDS_TO_FETCH_REC_MEMORY_DEPENDENCE_LEMMA]
QED

Theorem RX_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_REGISTERS_LEMMA:
!internal_state1 internal_state2 bd replies new_requests complete.
  (internal_state2, new_requests, complete) = rx_process_replies_generate_requests internal_state1 bd replies
  ==>
  internal_state2.registers = internal_state1.registers
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.rx_process_replies_generate_requests THEN
EQ_PAIR_ASM_TAC THEN
RLTAC THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem RX_PROCESS_REPLIES_GENERATE_REQUESTS_IMPLIES_QMEM_LRAM_EQ_LEMMA:
!internal_state1 internal_state2 bd replies new_requests complete.
  (internal_state2, new_requests, complete) = rx_process_replies_generate_requests internal_state1 bd replies
  ==>
  QMEM_LRAM_EQ internal_state2.registers internal_state1.registers
Proof
INTRO_TAC THEN ETAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ THEN IRTAC RX_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_REGISTERS_LEMMA THEN STAC
QED

Theorem RX_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_QHP_LEMMA:
!internal_state1 internal_state2 bd replies new_requests complete.
  (internal_state2, new_requests, complete) = rx_process_replies_generate_requests internal_state1 bd replies
  ==>
  internal_state1.qhp = internal_state2.qhp
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.rx_process_replies_generate_requests THEN
EQ_PAIR_ASM_TAC THEN
RLTAC THEN
LRTAC THEN
REPEAT (WEAKEN_TAC (fn _ => true)) THEN
RECORD_TAC THEN
STAC
QED

Theorem RX_PROCESS_REPLIES_GENERATE_REQUESTS_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA:
!internal_state1 internal_state2 bd replies new_requests complete.
  (internal_state2, new_requests, complete) = rx_process_replies_generate_requests internal_state1 bd replies
  ==>
  ENDPOINTS_TX_SOP_LI_EQ internal_state2.endpoints_tx internal_state1.endpoints_tx
Proof
INTRO_TAC THEN
ETAC bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ THEN
PTAC bbb_usb_rxTheory.rx_process_replies_generate_requests THEN
EQ_PAIR_ASM_TAC THEN
RLTAC THEN
LRTAC THEN
REPEAT (WEAKEN_TAC (fn _ => true)) THEN
RECORD_TAC THEN
STAC
QED

Theorem RX_PROCESS_REPLIES_GENERATE_REQUESTS_IMPLIES_WRITE_REQUEST_LEMMA:
!internal_state1 internal_state2 new_requests complete bd replies.
  (internal_state2, new_requests, complete) = rx_process_replies_generate_requests internal_state1 bd replies
  ==>
  new_requests = [] \/
  ?address_bytes. new_requests = [request_write address_bytes tag]
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.rx_process_replies_generate_requests THENL
[
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 EQ_PAIR_ASM_TAC THEN
 NLRTAC 2 THEN
 PAT_X_ASSUM “write_request = request_write address_bytes tag” (fn thm => ASSUME_TAC thm) THEN
 LRTAC THEN
 EXISTS_EQ_TAC
 ,
 EQ_PAIR_ASM_TAC THEN
 STAC
]
QED

Theorem RX_WRITE_BACK_CURRENT_BD_WRITE_ADDRESS_IS_BD_WAS_LEMMA:
!internal_state2 address_bytes tag released_bds channel_id internal_state endpoint_id bds_to_write_back write_address.
  (internal_state2, address_bytes, tag, released_bds) = rx_write_back_current_bd channel_id internal_state endpoint_id bds_to_write_back /\
  MEM write_address (MAP FST address_bytes)
  ==>
  ?bd bd_ras bd_was.
    MEM (bd, bd_ras, bd_was) bds_to_write_back /\
    MEM write_address bd_was
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.rx_write_back_current_bd THEN1 (EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN ETAC listTheory.MAP THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC) THEN
EQ_PAIR_ASM_TAC THEN
WEAKEN_TAC is_eq THEN
PAT_X_ASSUM “x' = x with endpoints_rx := y” (fn _ => ALL_TAC) THEN
PAT_X_ASSUM “x' = x with <|current_queue_id := a; bd_index := b; previous_queue_id := c; state := d|>” (fn _ => ALL_TAC) THEN
PAT_X_ASSUM “tag' = tag” (fn _ => ALL_TAC) THEN
PAT_X_ASSUM “x = []” (fn _ => ALL_TAC) THEN
PAT_X_ASSUM “s = if c then rx_fetch_bd else rx_write_back_sop_bd1” (fn _ => ALL_TAC) THEN
PAT_X_ASSUM “q = if c then id else endpoint.previous_queue_id” (fn _ => ALL_TAC) THEN
PAT_X_ASSUM “q = find_next_queue_id a b c d” (fn _ => ALL_TAC) THEN
PAT_X_ASSUM “i = find_next_bd_index e” (fn _ => ALL_TAC) THEN
PAT_X_ASSUM “e = internal_state.endpoints_rx eid” (fn _ => ALL_TAC) THEN
LRTAC THEN
ETAC listTheory.MAP_APPEND THEN
ETAC listTheory.MEM_APPEND THEN
PAT_X_ASSUM “l = h::t” (fn thm => ASSUME_TAC thm) THEN
LRTAC THEN
IRTAC lists_lemmasTheory.LAST_IS_MEM_LEMMA THEN
PAXTAC THEN
ASM_REWRITE_TAC [] THEN
WEAKEN_TAC (fn _ => true) THEN
SPLIT_ASM_DISJS_TAC THENL
[
 PAT_X_ASSUM “x = if c then y else z” (fn _ => ALL_TAC) THEN
 PAT_X_ASSUM “x = merge_lists (y, z)” (fn _ => ALL_TAC) THEN
 IRTAC bbb_usb_lemmasTheory.MEM_MAP_FST_MERGE_LISTS_WORD32ALIGNED_LEMMA THEN
 STAC
 ,
 PAT_X_ASSUM “x = if c then y else z” (fn _ => ALL_TAC) THEN
 IRTAC bbb_usb_lemmasTheory.MEM_MAP_FST_MERGE_LISTS_WORD32ALIGNED_LEMMA THEN
 STAC
 ,
 IF_SPLIT_TAC THEN1 (LRTAC THEN ETAC listTheory.MAP THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC) THEN
 IRTAC bbb_usb_lemmasTheory.MEM_MAP_FST_MERGE_LISTS_WORD32ALIGNED_LEMMA THEN STAC
]
QED

Theorem RX_WRITE_BACK_PREVIOUS_BD_WRITE_ADDRESS_IS_BD_WAS_LEMMA:
!internal_state2 address_bytes tag released_bds internal_state endpoint_id bds_to_write_back write_address.
  (internal_state2, address_bytes, tag, released_bds) = rx_write_back_previous_bd internal_state endpoint_id bds_to_write_back /\
  MEM write_address (MAP FST address_bytes)
  ==>
  ?bd bd_ras bd_was.
    MEM (bd, bd_ras, bd_was) bds_to_write_back /\
    MEM write_address bd_was
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.rx_write_back_previous_bd THEN1 (EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN ETAC listTheory.MAP THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC) THEN
EQ_PAIR_ASM_TAC THEN
WEAKEN_TAC is_eq THEN
RLTAC THEN
IRTAC lists_lemmasTheory.LAST_IS_MEM_LEMMA THEN
RLTAC THEN
PAXTAC THEN
IRTAC bbb_usb_lemmasTheory.MEM_MAP_FST_MERGE_LISTS_WORD32ALIGNED_LEMMA THEN
STAC
QED

Theorem RX_WRITE_BACK_SOP_BD1_WRITE_ADDRESS_IS_BD_WAS_LEMMA:
!internal_state2 address_bytes tag released_bds internal_state endpoint_id bds_to_write_back write_address environment.
  (internal_state2, address_bytes, tag, released_bds) = rx_write_back_sop_bd1 environment internal_state endpoint_id bds_to_write_back /\
  MEM write_address (MAP FST address_bytes)
  ==>
  ?bd bd_ras bd_was.
    MEM (bd, bd_ras, bd_was) bds_to_write_back /\
    MEM write_address bd_was
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.rx_write_back_sop_bd1 THENL
[
 EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN ETAC listTheory.MAP THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
 ,
 EQ_PAIR_ASM_TAC THEN
 WEAKEN_TAC is_eq THEN
 LRTAC THEN
 ETAC listTheory.MAP_APPEND THEN
 ETAC listTheory.MEM_APPEND THEN
 PAT_X_ASSUM “x = word32aligned y n” (fn thm => ASSUME_TAC thm THEN LRTAC THEN LRTAC) THEN
 PAT_X_ASSUM “x = word32aligned y n” (fn thm => ASSUME_TAC thm THEN LRTAC THEN LRTAC) THEN
 PAT_X_ASSUM “x = word32aligned y n” (fn thm => ASSUME_TAC thm THEN LRTAC THEN LRTAC) THEN
 IRTAC bbb_usb_lemmasTheory.FIND_SOME_IS_MEMBER_LEMMA THEN
 SPLIT_ASM_DISJS_TAC THEN
  IRTAC bbb_usb_lemmasTheory.MEM_MAP_FST_MERGE_LISTS_WORD32ALIGNED_LEMMA THEN PAXTAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN ETAC listTheory.MAP THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
]
QED

Theorem RX_WRITE_BACK_SOP_BD2_WRITE_ADDRESS_IS_BD_WAS_LEMMA:
!internal_state2 address_bytes tag released_bds internal_state endpoint_id bds_to_write_back write_address.
  (internal_state2, address_bytes, tag, released_bds) = rx_write_back_sop_bd2 internal_state endpoint_id bds_to_write_back /\
  MEM write_address (MAP FST address_bytes)
  ==>
  ?bd bd_ras bd_was.
    MEM (bd, bd_ras, bd_was) bds_to_write_back /\
    MEM write_address bd_was
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.rx_write_back_sop_bd2 THENL
[
 EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN ETAC listTheory.MAP THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
 ,
 EQ_PAIR_ASM_TAC THEN
 WEAKEN_TAC is_eq THEN
 LRTAC THEN
 IRTAC bbb_usb_lemmasTheory.FIND_SOME_IS_MEMBER_LEMMA THEN
 RLTAC THEN
 WEAKEN_TAC (fn _ => true) THEN
 RLTAC THEN
 WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN
 LRTAC THEN
 IRTAC bbb_usb_lemmasTheory.MEM_MAP_FST_MERGE_LISTS_LEMMA THEN
 PAXTAC THEN
 LRTAC THEN
 IRTAC rich_listTheory.MEM_DROP_IMP THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN ETAC listTheory.MAP THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
]
QED

Theorem RX_WRITE_BACK_SOP_BD3_WRITE_ADDRESS_IS_BD_WAS_LEMMA:
!internal_state2 address_bytes tag released_bds internal_state endpoint_id bds_to_write_back write_address.
  (internal_state2, address_bytes, tag, released_bds) = rx_write_back_sop_bd3 internal_state endpoint_id bds_to_write_back /\
  MEM write_address (MAP FST address_bytes)
  ==>
  ?bd bd_ras bd_was.
    MEM (bd, bd_ras, bd_was) bds_to_write_back /\
    MEM write_address bd_was
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.rx_write_back_sop_bd3 THEN
 EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN ETAC listTheory.MAP THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
QED

Theorem RX_WRITE_BACK_SOP_BD4_WRITE_ADDRESS_IS_BD_WAS_LEMMA:
!internal_state2 address_bytes tag released_bds internal_state endpoint_id bds_to_write_back write_address.
  (internal_state2, address_bytes, tag, released_bds) = rx_write_back_sop_bd4 internal_state endpoint_id bds_to_write_back /\
  MEM write_address (MAP FST address_bytes)
  ==>
  ?bd bd_ras bd_was.
    MEM (bd, bd_ras, bd_was) bds_to_write_back /\
    MEM write_address bd_was
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.rx_write_back_sop_bd4 THENL
[
 EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN ETAC listTheory.MAP THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
 ,
 EQ_PAIR_ASM_TAC THEN
 WEAKEN_TAC is_eq THEN
 LRTAC THEN
 WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN
 IRTAC bbb_usb_lemmasTheory.MEM_MAP_FST_MERGE_LISTS_LEMMA THEN
 LRTAC THEN
 IRTAC rich_listTheory.MEM_DROP_IMP THEN
 RLTAC THEN
 IRTAC bbb_usb_lemmasTheory.FIND_SOME_IS_MEMBER_LEMMA THEN
 PAXTAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN ETAC listTheory.MAP THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
 ,
 EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN ETAC listTheory.MAP THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
]
QED

Theorem RX_WRITE_BACK_SOP_BD5_WRITE_ADDRESS_IS_BD_WAS_LEMMA:
!internal_state2 address_bytes tag released_bds internal_state endpoint_id bds_to_write_back write_address.
  (internal_state2, address_bytes, tag, released_bds) = rx_write_back_sop_bd5 internal_state endpoint_id bds_to_write_back /\
  MEM write_address (MAP FST address_bytes)
  ==>
  ?bd bd_ras bd_was.
    MEM (bd, bd_ras, bd_was) bds_to_write_back /\
    MEM write_address bd_was
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.rx_write_back_sop_bd5 THEN
 EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN ETAC listTheory.MAP THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
QED

Theorem RX_WRITE_BACK_BD_WRITE_ADDRESS_IS_BD_WAS_LEMMA:
!internal_state2 address_bytes tag released_bds channel_id environment internal_state bds_to_write_back write_address.
  (internal_state2, address_bytes, tag, released_bds) = rx_write_back_bd channel_id environment internal_state bds_to_write_back /\
  MEM write_address (MAP FST address_bytes)
  ==>
  ?bd bd_ras bd_was.
    MEM (bd, bd_ras, bd_was) bds_to_write_back /\
    MEM write_address bd_was
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.rx_write_back_bd THENL
[
 IRTAC RX_WRITE_BACK_CURRENT_BD_WRITE_ADDRESS_IS_BD_WAS_LEMMA THEN STAC
 ,
 IRTAC RX_WRITE_BACK_PREVIOUS_BD_WRITE_ADDRESS_IS_BD_WAS_LEMMA THEN STAC
 ,
 IRTAC RX_WRITE_BACK_SOP_BD1_WRITE_ADDRESS_IS_BD_WAS_LEMMA THEN STAC
 ,
 IRTAC RX_WRITE_BACK_SOP_BD2_WRITE_ADDRESS_IS_BD_WAS_LEMMA THEN STAC
 ,
 IRTAC RX_WRITE_BACK_SOP_BD3_WRITE_ADDRESS_IS_BD_WAS_LEMMA THEN STAC
 ,
 IRTAC RX_WRITE_BACK_SOP_BD4_WRITE_ADDRESS_IS_BD_WAS_LEMMA THEN STAC
 ,
 IRTAC RX_WRITE_BACK_SOP_BD5_WRITE_ADDRESS_IS_BD_WAS_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN ETAC listTheory.MAP THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
]
QED

Theorem RX_WRITE_BACK_CURRENT_BD_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINT_TX_SOP_LI_EQ_LEMMA:
!internal_state2 address_bytes tag released_bds channel_id internal_state1 endpoint_id bds_to_write_back.
  (internal_state2, address_bytes, tag, released_bds) = rx_write_back_current_bd channel_id internal_state1 endpoint_id bds_to_write_back
  ==>
  QMEM_LRAM_EQ internal_state1.registers internal_state2.registers /\
  internal_state2.qhp = internal_state1.qhp /\
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
ETAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ THEN
ETAC bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ THEN
PTAC bbb_usb_rxTheory.rx_write_back_current_bd THEN1 (EQ_PAIR_ASM_TAC THEN STAC) THEN
EQ_PAIR_ASM_TAC THEN RLTAC THEN LRTAC THEN RECORD_TAC THEN STAC
QED

Theorem RX_WRITE_BACK_PREVIOUS_BD_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINT_TX_SOP_LI_EQ_LEMMA:
!internal_state2 address_bytes tag released_bds internal_state1 endpoint_id bds_to_write_back.
  (internal_state2, address_bytes, tag, released_bds) = rx_write_back_previous_bd internal_state1 endpoint_id bds_to_write_back
  ==>
  QMEM_LRAM_EQ internal_state1.registers internal_state2.registers /\
  internal_state2.qhp = internal_state1.qhp /\
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
ETAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ THEN
ETAC bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ THEN
PTAC bbb_usb_rxTheory.rx_write_back_previous_bd THEN1 (EQ_PAIR_ASM_TAC THEN STAC) THEN
EQ_PAIR_ASM_TAC THEN RLTAC THEN LRTAC THEN RECORD_TAC THEN STAC
QED

Theorem RX_WRITE_BACK_SOP_BD1_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINT_TX_SOP_LI_EQ_LEMMA:
!internal_state2 address_bytes tag released_bds environment internal_state1 endpoint_id bds_to_write_back.
  (internal_state2, address_bytes, tag, released_bds) = rx_write_back_sop_bd1 environment internal_state1 endpoint_id bds_to_write_back
  ==>
  QMEM_LRAM_EQ internal_state1.registers internal_state2.registers /\
  internal_state2.qhp = internal_state1.qhp /\
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
ETAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ THEN
ETAC bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ THEN
PTAC bbb_usb_rxTheory.rx_write_back_sop_bd1 THEN TRY (EQ_PAIR_ASM_TAC THEN STAC) THEN
EQ_PAIR_ASM_TAC THEN RLTAC THEN LRTAC THEN RECORD_TAC THEN STAC
QED

Theorem RX_WRITE_BACK_SOP_BD2_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINT_TX_SOP_LI_EQ_LEMMA:
!internal_state2 address_bytes tag released_bds internal_state1 endpoint_id bds_to_write_back.
  (internal_state2, address_bytes, tag, released_bds) = rx_write_back_sop_bd2 internal_state1 endpoint_id bds_to_write_back
  ==>
  QMEM_LRAM_EQ internal_state1.registers internal_state2.registers /\
  internal_state2.qhp = internal_state1.qhp /\
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
ETAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ THEN
ETAC bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ THEN
PTAC bbb_usb_rxTheory.rx_write_back_sop_bd2 THEN TRY (EQ_PAIR_ASM_TAC THEN STAC) THEN
EQ_PAIR_ASM_TAC THEN RLTAC THEN LRTAC THEN RECORD_TAC THEN STAC
QED

Theorem RX_WRITE_BACK_SOP_BD3_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINT_TX_SOP_LI_EQ_LEMMA:
!internal_state2 address_bytes tag released_bds internal_state1 endpoint_id bds_to_write_back.
  (internal_state2, address_bytes, tag, released_bds) = rx_write_back_sop_bd3 internal_state1 endpoint_id bds_to_write_back
  ==>
  QMEM_LRAM_EQ internal_state1.registers internal_state2.registers /\
  internal_state2.qhp = internal_state1.qhp /\
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
ETAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ THEN
ETAC bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ THEN
PTAC bbb_usb_rxTheory.rx_write_back_sop_bd3 THEN TRY (EQ_PAIR_ASM_TAC THEN STAC) THEN
EQ_PAIR_ASM_TAC THEN RLTAC THEN LRTAC THEN RECORD_TAC THEN STAC
QED

Theorem RX_WRITE_BACK_SOP_BD4_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINT_TX_SOP_LI_EQ_LEMMA:
!internal_state2 address_bytes tag released_bds internal_state1 endpoint_id bds_to_write_back.
  (internal_state2, address_bytes, tag, released_bds) = rx_write_back_sop_bd4 internal_state1 endpoint_id bds_to_write_back
  ==>
  QMEM_LRAM_EQ internal_state1.registers internal_state2.registers /\
  internal_state2.qhp = internal_state1.qhp /\
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
ETAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ THEN
ETAC bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ THEN
PTAC bbb_usb_rxTheory.rx_write_back_sop_bd4 THEN TRY (EQ_PAIR_ASM_TAC THEN STAC) THEN
EQ_PAIR_ASM_TAC THEN RLTAC THEN LRTAC THEN RECORD_TAC THEN STAC
QED

Theorem RX_WRITE_BACK_SOP_BD5_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINT_TX_SOP_LI_EQ_LEMMA:
!internal_state2 address_bytes tag released_bds internal_state1 endpoint_id bds_to_write_back.
  (internal_state2, address_bytes, tag, released_bds) = rx_write_back_sop_bd5 internal_state1 endpoint_id bds_to_write_back
  ==>
  QMEM_LRAM_EQ internal_state1.registers internal_state2.registers /\
  internal_state2.qhp = internal_state1.qhp /\
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
ETAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ THEN
ETAC bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ THEN
PTAC bbb_usb_rxTheory.rx_write_back_sop_bd5 THEN TRY (EQ_PAIR_ASM_TAC THEN STAC) THEN
EQ_PAIR_ASM_TAC THEN RLTAC THEN LRTAC THEN RECORD_TAC THEN STAC
QED

Theorem RX_WRITE_BACK_BD_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINTS_TX_SOP_LI_EQ_LEMMA:
!internal_state2 address_bytes tag released_bds channel_id environment internal_state1 bds_to_write_back.
  (internal_state2, address_bytes, tag, released_bds) = rx_write_back_bd channel_id environment internal_state1 bds_to_write_back
  ==>
  QMEM_LRAM_EQ internal_state1.registers internal_state2.registers /\
  internal_state2.qhp = internal_state1.qhp /\
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.rx_write_back_bd THENL
[
 IRTAC RX_WRITE_BACK_CURRENT_BD_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINT_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 IRTAC RX_WRITE_BACK_PREVIOUS_BD_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINT_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 IRTAC RX_WRITE_BACK_SOP_BD1_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINT_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 IRTAC RX_WRITE_BACK_SOP_BD2_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINT_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 IRTAC RX_WRITE_BACK_SOP_BD3_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINT_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 IRTAC RX_WRITE_BACK_SOP_BD4_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINT_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 IRTAC RX_WRITE_BACK_SOP_BD5_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINT_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 ETAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ THEN ETAC bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ THEN EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem RX_WRITE_BACK_BD_ADDRESSES_ARE_DECLARED_LEMMA:
!write_addresses channel_id environment internal_state1 internal_state2 bds_to_write_back address_bytes tag released_bds.
  write_addresses = rx_write_back_bd_addresses channel_id environment internal_state1 bds_to_write_back /\
  (internal_state2, address_bytes, tag, released_bds) = rx_write_back_bd channel_id environment internal_state1 bds_to_write_back
  ==>
  LIST1_IN_LIST2 (MAP FST address_bytes) write_addresses
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.rx_write_back_bd_addresses THEN
LRTAC THEN
REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
QED

Theorem RX_BD_TRANSFER_RAS_WAS_INTERNAL_STATE_INDEPENDENT_LEMMA:
!(internal_state1 : 'a) (internal_state2 : 'a) bd.
  rx_bd_transfer_ras_was internal_state1 bd = rx_bd_transfer_ras_was internal_state2 bd
Proof
REPEAT GEN_TAC THEN
PTAC bbb_usb_rxTheory.rx_bd_transfer_ras_was THEN
PTAC bbb_usb_rxTheory.rx_bd_transfer_ras_was THEN
STAC
QED

Theorem QHP_QMEM_LRAM_EQ_IMPLIES_RX_FETCH_BD_ADDRESSES_EQ_LEMMA:
!internal_state1 internal_state2 channel_id.
  internal_state2.qhp = internal_state1.qhp /\
  QMEM_LRAM_EQ internal_state1.registers internal_state2.registers
  ==>
  rx_fetch_bd_addresses channel_id internal_state2 = rx_fetch_bd_addresses channel_id internal_state1
Proof
INTRO_TAC THEN
ETAC bbb_usb_rxTheory.rx_fetch_bd_addresses THEN
LRTAC THEN
IF_SPLIT_TAC THEN TRY STAC THEN
IRTAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ_IMPLIES_GET_BD_RAS_EQ_LEMMA THEN
STAC
QED

val _ = export_theory();

