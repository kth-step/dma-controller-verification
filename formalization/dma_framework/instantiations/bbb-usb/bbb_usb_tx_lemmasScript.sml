open HolKernel Parse boolLib bossLib helper_tactics;
open bbb_usb_txTheory;

val _ = new_theory "bbb_usb_tx_lemmas";

Theorem TX_BD_TRANSFER_RAS_WAS_DEPENDS_ON_BD_LEMMA:
!(internal_state1 : internal_state_type) (internal_state2 : internal_state_type) bd.
  tx_bd_transfer_ras_was internal_state1 bd =  tx_bd_transfer_ras_was internal_state2 bd
Proof
REPEAT GEN_TAC THEN
REPEAT (PTAC bbb_usb_txTheory.tx_bd_transfer_ras_was) THEN
STAC
QED

Theorem ENDPOINT_SCHEDULABLE_TX_IMPLIES_SOME_QUEUE_ID_LEQ_91_LEMMA:
!environment internal_state1 internal_state2 channels endpoint_id queue_id.
  SOME (internal_state2, queue_id) = endpoint_schedulable_tx environment internal_state1 channels endpoint_id
  ==>
  queue_id <=+ 91w
Proof
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.endpoint_schedulable_tx THEN
PTAC bbb_usb_schedulerTheory.validate_queue_id THENL
[
 HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
 ,
 ETAC optionTheory.SOME_11 THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
]
QED

Theorem IS_TX_SOP_WRITTEN_BACK_IMPLIES_CHANNEL_ID_LEQ_91_LEMMA:
!internal_state1 internal_state2 bds_to_write_back channel_id channel_id' dma_operation.
  ~(channel_id <+ 32w \/ 91w <+ channel_id) /\
  SOME (internal_state2, channel_id', dma_operation) = is_tx_sop_written_back internal_state1 bds_to_write_back channel_id
  ==>
  channel_id' <=+ 91w
Proof
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.is_tx_sop_written_back THEN TRY (HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE) THEN
ETAC optionTheory.SOME_11 THEN
EQ_PAIR_ASM_TAC THEN
ETAC boolTheory.DE_MORGAN_THM THEN
ETAC wordsTheory.WORD_NOT_LOWER THEN
STAC
QED

Theorem IS_TX_BD_POPPED_IMPLIES_CHANNEL_ID_LEQ_91_LEMMA:
!internal_state1 internal_state2 bds_to_write_back channel_id channel_id' dma_operation.
  ~(channel_id <+ 32w \/ 91w <+ channel_id) /\
  SOME (internal_state2, channel_id', dma_operation) = is_tx_bd_popped internal_state1 bds_to_write_back channel_id
  ==>
  channel_id' <=+ 91w
Proof
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.is_tx_bd_popped THEN TRY (HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE) THEN
ETAC optionTheory.SOME_11 THEN
EQ_PAIR_ASM_TAC THEN
ETAC boolTheory.DE_MORGAN_THM THEN
ETAC wordsTheory.WORD_NOT_LOWER THEN
STAC
QED

Theorem IS_TX_WRITE_BACK_IMPLIES_CHANNEL_ID_LEQ_91_IND_LEMMA:
!queue_id internal_state1 channels.
  (\internal_state1 channels queue_id.
   !internal_state2 dma_operation channel_id.
    SOME (internal_state2, channel_id, dma_operation) = is_tx_write_back internal_state1 channels queue_id
    ==>
    channel_id <=+ 91w) internal_state1 channels queue_id
Proof
MATCH_MP_TAC bbb_usb_schedulerTheory.is_tx_write_back_ind THEN
BETA_TAC THEN
INTRO_TAC THEN
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.is_tx_write_back THENL
[
 HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
 ,
 PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
 LRTAC THEN
 ETAC optionTheory.SOME_11 THEN
 RLTAC THEN
 IRTAC IS_TX_SOP_WRITTEN_BACK_IMPLIES_CHANNEL_ID_LEQ_91_LEMMA THEN
 STAC
 ,
 PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
 LRTAC THEN
 LRTAC THEN
 IRTAC IS_TX_BD_POPPED_IMPLIES_CHANNEL_ID_LEQ_91_LEMMA THEN
 STAC
 ,
 AIRTAC THEN AIRTAC THEN STAC
]
QED

Theorem IS_TX_WRITE_BACK_IMPLIES_CHANNEL_ID_LEQ_91_LEMMA:
!queue_id internal_state1 internal_state2 channels dma_operation channel_id.
  SOME (internal_state2, channel_id, dma_operation) = is_tx_write_back internal_state1 channels queue_id
  ==>
  channel_id <=+ 91w
Proof
REWRITE_TAC [BETA_RULE IS_TX_WRITE_BACK_IMPLIES_CHANNEL_ID_LEQ_91_IND_LEMMA]
QED

Theorem INCREMENT_SCHEDULER_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA:
!internal_state1 internal_state2.
  internal_state2 = increment_scheduler internal_state1
  ==>
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.increment_scheduler THEN
 ALL_LRTAC THEN RECORD_TAC THEN REWRITE_TAC [bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ_REFL_LEMMA]
QED

Theorem IS_TX_WRITE_BACK_PRESERVES_REGISTERS_QHP_IND_LEMMA:
!queue_id internal_state1 channels.
  (\internal_state1 channels queue_id.
   !internal_state2 dma_operation channel_id.
    SOME (internal_state2, channel_id, dma_operation) = is_tx_write_back internal_state1 channels queue_id
    ==>
    internal_state2.registers = internal_state1.registers /\
    internal_state2.qhp = internal_state1.qhp) queue_id internal_state1 channels
Proof
MATCH_MP_TAC bbb_usb_schedulerTheory.is_tx_write_back_ind THEN
BETA_TAC THEN
INTRO_TAC THEN
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.is_tx_write_back THENL
[
 HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
 ,
 PTAC bbb_usb_schedulerTheory.is_tx_sop_written_back THENL
 [
  WEAKEN_TAC is_forall THEN NLRTAC 2 THEN ETAC optionTheory.SOME_11 THEN EQ_PAIR_ASM_TAC THEN LRTAC THEN RECORD_TAC THEN STAC
  ,
  LRTAC THEN PTAC optionTheory.IS_SOME_DEF THEN SOLVE_F_ASM_TAC
 ]
 ,
 RLTAC THEN
 PTAC bbb_usb_schedulerTheory.is_tx_bd_popped THENL
 [
  ETAC optionTheory.SOME_11 THEN EQ_PAIR_ASM_TAC THEN RLTAC THEN LRTAC THEN RECORD_TAC THEN STAC
  ,
  HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
 ]
 ,
 AIRTAC THEN AIRTAC THEN STAC
]
QED

Theorem IS_TX_WRITE_BACK_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_IND_LEMMA:
!queue_id internal_state1 channels.
  (\internal_state1 channels queue_id.
   !internal_state2 dma_operation channel_id.
    SOME (internal_state2, channel_id, dma_operation) = is_tx_write_back internal_state1 channels queue_id
    ==>
    ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx) queue_id internal_state1 channels
Proof
MATCH_MP_TAC bbb_usb_schedulerTheory.is_tx_write_back_ind THEN
BETA_TAC THEN
INTRO_TAC THEN
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.is_tx_write_back THENL
[
 HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
 ,
 PTAC bbb_usb_schedulerTheory.is_tx_sop_written_back THENL
 [
  WEAKEN_TAC is_forall THEN
  NLRTAC 2 THEN
  ETAC optionTheory.SOME_11 THEN
  EQ_PAIR_ASM_TAC THEN
  LRTAC THEN
  RECORD_TAC THEN
  ETAC bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ THEN
  GEN_TAC THEN
  REWRITE_TAC [combinTheory.UPDATE_def] THEN
  BETA_TAC THEN
  IF_SPLIT_TAC THEN TRY STAC THEN
   RLTAC THEN LRTAC THEN LRTAC THEN LRTAC THEN RECORD_TAC THEN STAC
  ,
  LRTAC THEN PTAC optionTheory.IS_SOME_DEF THEN SOLVE_F_ASM_TAC
 ]
 ,
 RLTAC THEN
 PTAC bbb_usb_schedulerTheory.is_tx_bd_popped THENL
 [
  ETAC optionTheory.SOME_11 THEN
  EQ_PAIR_ASM_TAC THEN
  RLTAC THEN
  LRTAC THEN
  WEAKEN_TAC is_forall THEN
  RECORD_TAC THEN
  ETAC bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ THEN
  GEN_TAC THEN
  REWRITE_TAC [combinTheory.UPDATE_def] THEN
  BETA_TAC THEN
  IF_SPLIT_TAC THEN TRY STAC THEN
   RLTAC THEN LRTAC THEN LRTAC THEN LRTAC THEN LRTAC THEN RECORD_TAC THEN STAC
  ,
  HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
 ]
 ,
 AIRTAC THEN AIRTAC THEN STAC
]
QED

Theorem IS_TX_WRITE_BACK_PRESERVES_REGISTERS_QHP_LEMMA:
!queue_id internal_state1 channels internal_state2 dma_operation channel_id.
  SOME (internal_state2, channel_id, dma_operation) = is_tx_write_back internal_state1 channels queue_id
  ==>
  internal_state2.registers = internal_state1.registers /\
  internal_state2.qhp = internal_state1.qhp
Proof
REWRITE_TAC [BETA_RULE IS_TX_WRITE_BACK_PRESERVES_REGISTERS_QHP_IND_LEMMA]
QED

Theorem IS_TX_WRITE_BACK_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA:
!queue_id internal_state1 channels internal_state2 dma_operation channel_id.
  SOME (internal_state2, channel_id, dma_operation) = is_tx_write_back internal_state1 channels queue_id
  ==>
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
REWRITE_TAC [BETA_RULE IS_TX_WRITE_BACK_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_IND_LEMMA]
QED

Theorem NEW_QUEUE_ID_PRESERVES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA:
!internal_state1 internal_state internal_state2 endpoint endpoint' endpoint_id new_queue_id.
  endpoint = internal_state1.endpoints_tx endpoint_id /\
  endpoint' = endpoint with current_queue_id := new_queue_id /\
  internal_state = internal_state1 with endpoints_tx := (endpoint_id =+ endpoint') internal_state1.endpoints_tx /\
  ENDPOINTS_TX_SOP_LI_EQ internal_state.endpoints_tx internal_state2.endpoints_tx
  ==>
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
ETAC bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ THEN
GEN_TAC THEN
LRTAC THEN
LRTAC THEN
LRTAC THEN
RECORD_TAC THEN
RW_HYPS_TAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (Q.SPEC ‘endpoint_id'’ thm)) THEN
IF_SPLIT_TAC THENL
[
 RLTAC THEN RECORD_TAC THEN STAC
 ,
 ALL_LRTAC THEN STAC
]
QED

Theorem ENDPOINTS_TX_SOP_LI_EQ_TRANS_LEMMA:
!endpoints_tx1 endpoints_tx2 endpoints_tx3.
  ENDPOINTS_TX_SOP_LI_EQ endpoints_tx1 endpoints_tx2 /\
  ENDPOINTS_TX_SOP_LI_EQ endpoints_tx2 endpoints_tx3
  ==>
  ENDPOINTS_TX_SOP_LI_EQ endpoints_tx1 endpoints_tx3
Proof
INTRO_TAC THEN
ETAC bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ THEN
STAC
QED

Theorem ENDPOINTS_TX_SOP_LI_EQ_LEMMA:
!endpoint_id endpoints_tx1 endpoints_tx2 endpoint1 endpoint2.
  ENDPOINTS_TX_SOP_LI_EQ endpoints_tx1 endpoints_tx2 /\
  endpoint1 = endpoints_tx1 endpoint_id /\
  endpoint2 = endpoints_tx2 endpoint_id
  ==>
  endpoint2.sop = endpoint1.sop /\
  endpoint2.sop_li = endpoint1.sop_li
Proof
INTRO_TAC THEN
ETAC bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC_ALL thm)) THEN
STAC
QED

Theorem QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_LEMMA:
!bds registers1 registers2 memory visited_bds visited_bds_option bd_address.
  QMEM_LRAM_EQ registers1 registers2 /\
  (bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers1 visited_bds bd_address
  ==>
  (bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers2 visited_bds bd_address
Proof
Induct THENL
[
 INTRO_TAC THEN
 PTAC bbb_usb_queue_txTheory.tx_bds_of_transfer_rec THEN PTAC bbb_usb_queue_txTheory.tx_bds_of_transfer_rec THEN EQ_PAIR_ASM_TAC THENL
 [
  STAC
  ,
  IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
  ,
  IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
  ,
  IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
  ,
  ETAC bbb_usb_functionsTheory.next_bd_pointer THEN WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN LRTAC THEN ETAC bbb_usb_functionsTheory.eop_bd THEN LRTAC THEN CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
  ,
  FIRTAC bbb_usb_queue_txTheory.NO_BDS_TO_FETCH_NON_ZERO_START_BD_ADDRESS_IMPLIES_F_LEMMA THEN SOLVE_F_ASM_TAC
  ,
  FIRTAC bbb_usb_queue_txTheory.NO_BDS_TO_FETCH_NON_ZERO_START_BD_ADDRESS_IMPLIES_F_LEMMA THEN SOLVE_F_ASM_TAC
  ,
  FIRTAC bbb_usb_queue_txTheory.NO_BDS_TO_FETCH_NON_ZERO_START_BD_ADDRESS_IMPLIES_F_LEMMA THEN SOLVE_F_ASM_TAC
 ]
 ,
 INTRO_TAC THEN
 PTAC bbb_usb_queue_txTheory.tx_bds_of_transfer_rec THENL
 [
  PTAC bbb_usb_queue_txTheory.tx_bds_of_transfer_rec THEN STAC
  ,
  PTAC bbb_usb_queue_txTheory.tx_bds_of_transfer_rec THEN
  IRTAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ_IMPLIES_GET_BD_RAS_EQ_LEMMA THEN
  QLRTAC THEN
  PAT_X_ASSUM “bd_ras' = get_bd_ras registers1 bd_address” (fn thm => ASSUME_TAC thm) THEN
  RLTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN LRTAC THEN EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN STAC
  ,
  PTAC bbb_usb_queue_txTheory.tx_bds_of_transfer_rec THENL
  [
   IRTAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ_IMPLIES_GET_BD_RAS_EQ_LEMMA THEN
   QLRTAC THEN
   PAT_X_ASSUM “bd_ras' = get_bd_ras registers1 bd_address” (fn thm => ASSUME_TAC thm) THEN
   RLTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN LRTAC THEN EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN STAC
   ,
   IRTAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ_IMPLIES_GET_BD_RAS_EQ_LEMMA THEN
   QLRTAC THEN
   PAT_X_ASSUM “bd_ras' = get_bd_ras registers1 bd_address” (fn thm => ASSUME_TAC thm) THEN
   RLTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN LRTAC THEN EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN CONTR_ASMS_TAC
  ]
  ,
  PAT_X_ASSUM “(h::bds, visited_bds_option) = tx_bds_of_transfer_rec m r v a” (fn thm => ASSUME_TAC thm) THEN
  PTAC bbb_usb_queue_txTheory.tx_bds_of_transfer_rec THENL
  [
   IRTAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ_IMPLIES_GET_BD_RAS_EQ_LEMMA THEN
   QLRTAC THEN
   PAT_X_ASSUM “bd_ras' = get_bd_ras registers1 bd_address” (fn thm => ASSUME_TAC thm) THEN
   RLTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN LRTAC THEN EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN CONTR_ASMS_TAC
   ,
   EQ_PAIR_ASM_TAC THEN
   ETAC listTheory.CONS_11 THEN
   LRTAC THEN
   NRLTAC 2 THEN
   ITAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ_IMPLIES_GET_BD_RAS_EQ_LEMMA THEN
   QLRTAC THEN
   PAT_X_ASSUM “bd_ras' = get_bd_ras registers1 bd_address” (fn thm => ASSUME_TAC thm) THEN
   RLTAC THEN
   RLTAC THEN
   RLTAC THEN
   RLTAC THEN
   LRTAC THEN
   EQ_PAIR_ASM_TAC THEN
   NLRTAC 2 THEN
   RLTAC THEN
   RLTAC THEN
   AIRTAC THEN
   RLTAC THEN
   EQ_PAIR_ASM_TAC THEN
   STAC
  ]
 ]
]
QED

Theorem QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_PAIR_LEMMA:
!registers1 registers2 memory visited_bds bds_visited_bds_option bd_address.
  QMEM_LRAM_EQ registers1 registers2 /\
  bds_visited_bds_option = tx_bds_of_transfer_rec memory registers1 visited_bds bd_address
  ==>
  bds_visited_bds_option = tx_bds_of_transfer_rec memory registers2 visited_bds bd_address
Proof
INTRO_TAC THEN
Cases_on ‘bds_visited_bds_option’ THEN
IRTAC QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_LEMMA THEN
STAC
QED

Theorem QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_EQ_LEMMA:
!registers1 registers2.
  QMEM_LRAM_EQ registers1 registers2
  ==>
  !bds memory visited_bds visited_bds_option bd_address.
    tx_bds_of_transfer_rec memory registers2 visited_bds bd_address = tx_bds_of_transfer_rec memory registers1 visited_bds bd_address
Proof
INTRO_TAC THEN
REPEAT GEN_TAC THEN
IRTAC QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_PAIR_LEMMA THEN
STAC
QED

Theorem QMEM_LRAM_EQ_ENDPOINTS_TX_SOP_LI_EQ_IMPLIES_TX_BDS_OF_TRANSFERS_EQ_IND_LEMMA:
!memory registers1 visited_bds bd_address.
  (\memory registers1 visited_bds bd_address.
   !registers2.
     QMEM_LRAM_EQ registers1 registers2
     ==>
     tx_bds_of_transfers_rec memory registers2 visited_bds bd_address =
     tx_bds_of_transfers_rec memory registers1 visited_bds bd_address) memory registers1 visited_bds bd_address
Proof
MATCH_MP_TAC bbb_usb_queue_txTheory.tx_bds_of_transfers_rec_ind THEN
APP_SCALAR_TAC THEN
INTRO_TAC THEN
INTRO_TAC THEN
PTAC bbb_usb_queue_txTheory.tx_bds_of_transfers_rec THENL
[
 PTAC bbb_usb_queue_txTheory.tx_bds_of_transfers_rec THEN STAC
 ,
 WEAKEN_TAC is_forall THEN
 PTAC bbb_usb_queue_txTheory.tx_bds_of_transfers_rec THEN TRY STAC THENL
 [
  ASSUME_TAC (Q.SPECL [‘registers’, ‘registers2’] QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_EQ_LEMMA) THEN
  AITAC THEN
  QLRTAC THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 2 THEN
  CONTR_ASMS_TAC
  ,
  ASSUME_TAC (Q.SPECL [‘registers’, ‘registers2’] QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_EQ_LEMMA) THEN
  AITAC THEN
  QLRTAC THEN
  WEAKEN_TAC is_eq THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 2 THEN
  CONTR_ASMS_TAC
  ,
  ASSUME_TAC (Q.SPECL [‘registers’, ‘registers2’] QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_EQ_LEMMA) THEN
  AITAC THEN
  QLRTAC THEN
  WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 2 THEN
  CONTR_ASMS_TAC
 ]
 ,
 WEAKEN_TAC is_forall THEN
 PTAC bbb_usb_queue_txTheory.tx_bds_of_transfers_rec THEN TRY STAC THENL
 [
  ASSUME_TAC (Q.SPECL [‘registers’, ‘registers2’] QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_EQ_LEMMA) THEN
  AITAC THEN
  QLRTAC THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 2 THEN
  CONTR_ASMS_TAC
  ,
  ASSUME_TAC (Q.SPECL [‘registers’, ‘registers2’] QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_EQ_LEMMA) THEN
  AITAC THEN
  QLRTAC THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  STAC
  ,
  ASSUME_TAC (Q.SPECL [‘registers’, ‘registers2’] QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_EQ_LEMMA) THEN
  AITAC THEN
  QLRTAC THEN
  WEAKEN_TAC is_eq THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  STAC
  ,
  ASSUME_TAC (Q.SPECL [‘registers’, ‘registers2’] QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_EQ_LEMMA) THEN
  AITAC THEN
  QLRTAC THEN
  WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 2 THEN
  CONTR_ASMS_TAC
 ]
 ,
 WEAKEN_TAC is_forall THEN
 PTAC bbb_usb_queue_txTheory.tx_bds_of_transfers_rec THEN TRY STAC THENL
 [
  ASSUME_TAC (Q.SPECL [‘registers’, ‘registers2’] QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_EQ_LEMMA) THEN
  AITAC THEN
  QLRTAC THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 2 THEN
  CONTR_ASMS_TAC
  ,
  ASSUME_TAC (Q.SPECL [‘registers’, ‘registers2’] QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_EQ_LEMMA) THEN
  AITAC THEN
  QLRTAC THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  STAC
  ,
  ASSUME_TAC (Q.SPECL [‘registers’, ‘registers2’] QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_EQ_LEMMA) THEN
  AITAC THEN
  QLRTAC THEN
  WEAKEN_TAC is_eq THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  STAC
  ,
  ASSUME_TAC (Q.SPECL [‘registers’, ‘registers2’] QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_EQ_LEMMA) THEN
  AITAC THEN
  QLRTAC THEN
  WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN
  PAT_X_ASSUM “tx_bds_of_transfer_rec memory registers visited_bds sop_bd_address = (bds_of_transfer',visited_bds_option')” (fn thm => ASSUME_TAC thm) THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 2 THEN
  RLTAC THEN
  RLTAC THEN
  CONTR_ASMS_TAC
 ]
 ,
 ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
 PTAC bbb_usb_queue_txTheory.tx_bds_of_transfers_rec THEN TRY STAC THENL
 [
  WEAKEN_TAC is_forall THEN
  ASSUME_TAC (Q.SPECL [‘registers’, ‘registers2’] QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_EQ_LEMMA) THEN
  AITAC THEN
  QLRTAC THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 2 THEN
  CONTR_ASMS_TAC
  ,
  WEAKEN_TAC is_forall THEN
  ASSUME_TAC (Q.SPECL [‘registers’, ‘registers2’] QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_EQ_LEMMA) THEN
  AITAC THEN
  QLRTAC THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 2 THEN
  CONTR_ASMS_TAC
  ,
  WEAKEN_TAC is_forall THEN
  ASSUME_TAC (Q.SPECL [‘registers’, ‘registers2’] QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_EQ_LEMMA) THEN
  AITAC THEN
  QLRTAC THEN
  PAT_X_ASSUM “tx_bds_of_transfer_rec memory registers visited_bds sop_bd_address = (bds_of_transfer',visited_bds_option')” (fn thm => ASSUME_TAC thm) THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 2 THEN
  RLTAC THEN
  RLTAC THEN
  CONTR_ASMS_TAC
  ,
  ASSUME_TAC (Q.SPECL [‘registers’, ‘registers2’] QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_EQ_LEMMA) THEN
  PAT_X_ASSUM “QMEM_LRAM_EQ registers registers2” (fn thm1 =>
  PAT_X_ASSUM “P ==> Q” (fn thm2 => ASSUME_TAC thm1 THEN ASSUME_TAC (REWRITE_RULE [thm1] thm2))) THEN
  QLRTAC THEN
  PAT_X_ASSUM “tx_bds_of_transfer_rec memory registers visited_bds sop_bd_address = (bds_of_transfer',visited_bds_option')” (fn thm => ASSUME_TAC thm) THEN
  LRTAC THEN
  EQ_PAIR_ASM_TAC THEN
  LRTAC THEN
  REWRITE_TAC [listTheory.APPEND_11] THEN
  AITAC THEN
  AITAC THEN
  ALL_RLTAC THEN
  IRTAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ_IMPLIES_LI_TO_NEXT_BD_ADDRESS_EQ_LEMMA THEN
  QLRTAC THEN
  STAC
 ]
]
QED

Theorem QMEM_LRAM_EQ_ENDPOINTS_TX_SOP_LI_EQ_IMPLIES_TX_BDS_OF_TRANSFERS_EQ_LEMMA:
!memory registers1 registers2 bd_address visited_bds.
  QMEM_LRAM_EQ registers1 registers2
  ==>
  tx_bds_of_transfers_rec memory registers2 visited_bds bd_address = tx_bds_of_transfers_rec memory registers1 visited_bds bd_address
Proof
REWRITE_TAC [BETA_RULE QMEM_LRAM_EQ_ENDPOINTS_TX_SOP_LI_EQ_IMPLIES_TX_BDS_OF_TRANSFERS_EQ_IND_LEMMA]
QED

Theorem QMEM_LRAM_EQ_QHP_ENDPOINTS_TX_SOP_LI_EQ_IMPLIES_TX_BDS_TO_FETCH_EQ_LEMMA:
!internal_state1 internal_state2 memory channel_id.
  QMEM_LRAM_EQ internal_state1.registers internal_state2.registers /\
  internal_state2.qhp = internal_state1.qhp /\
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
  ==>
  tx_bds_to_fetch channel_id memory internal_state2 = tx_bds_to_fetch channel_id memory internal_state1
Proof
INTRO_TAC THEN
ETAC bbb_usb_queue_txTheory.tx_bds_to_fetch THEN
LRTAC THEN
LETS_TAC THEN
ITAC QMEM_LRAM_EQ_IMPLIES_TX_BDS_OF_TRANSFER_EQ_LEMMA THEN
RLTAC THEN
EQ_PAIR_ASM_TAC THEN
NLRTAC 2 THEN
IF_SPLIT_TAC THEN TRY (REWRITE_TAC []) THEN
IF_SPLIT_TAC THEN TRY (REWRITE_TAC []) THEN
ITAC ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN
NRLTAC 2 THEN
RLTAC THEN
RLTAC THEN
IF_SPLIT_TAC THEN TRY (REWRITE_TAC []) THEN
REWRITE_TAC [listTheory.APPEND_11] THEN
ITAC QMEM_LRAM_EQ_ENDPOINTS_TX_SOP_LI_EQ_IMPLIES_TX_BDS_OF_TRANSFERS_EQ_LEMMA THEN
RLTAC THEN
RLTAC THEN
IRTAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ_IMPLIES_LI_TO_NEXT_BD_ADDRESS_EQ_LEMMA THEN
QRLTAC THEN
RLTAC THEN
RLTAC THEN
STAC
QED

Theorem TX_FETCH_BD_RESULT_LEMMA:
!internal_state1 internal_state2 channel_id fetched_bd_ras_was fetched_bd_update bytes tag.
  (internal_state2, SOME (fetched_bd_ras_was, fetched_bd_update)) = tx_fetch_bd channel_id internal_state1 (SOME (bytes, tag))
  ==>
  fetched_bd_ras_was = (form_bd_li bytes, get_bd_ras internal_state1.registers (internal_state1.qhp channel_id), get_bd_ras internal_state1.registers (internal_state1.qhp channel_id)) /\
  fetched_bd_update = no_update
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_fetch_bd THEN TRY (EQ_PAIR_ASM_TAC THEN IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC) THEN
EQ_PAIR_ASM_TAC THEN
ETAC optionTheory.SOME_11 THEN
EQ_PAIR_ASM_TAC THEN
ALL_LRTAC THEN
STAC
QED

Theorem TX_FETCH_BD_ADDRESSES_RESULT_LEMMA:
!channel_id internal_state addresses tag.
  internal_state.qhp channel_id <> 0w /\
  (addresses, tag) = tx_fetch_bd_addresses channel_id internal_state
  ==>
  addresses = get_bd_ras internal_state.registers (internal_state.qhp channel_id)
Proof
INTRO_TAC THEN
ETAC bbb_usb_txTheory.tx_fetch_bd_addresses THEN
IF_SPLIT_TAC THEN TRY CONTR_ASMS_TAC THEN
EQ_PAIR_ASM_TAC THEN
STAC
QED

Theorem TX_BDS_OF_TRANSFER_REC_RESULT_LEMMA:
!registers memory start_bd_address bd ras was update bds visited_bds visited_bds_option.
  (((bd, ras, was), update)::bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds start_bd_address
  ==>
  ras = get_bd_ras registers start_bd_address /\
  was = get_bd_ras registers start_bd_address /\
  update = no_update /\
  ?bytes.
    bytes = MAP memory ras /\
    bd = form_bd_li bytes
Proof
INTRO_TAC THEN
PTAC bbb_usb_queue_txTheory.tx_bds_of_transfer_rec THEN EQ_PAIR_ASM_TAC THENL
[
 IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
 ,
 ETAC listTheory.CONS_11 THEN EQ_PAIR_ASM_TAC THEN CONJS_TAC THEN TRY STAC THEN PAXTAC THEN STAC
 ,
 ETAC listTheory.CONS_11 THEN EQ_PAIR_ASM_TAC THEN CONJS_TAC THEN TRY STAC THEN PAXTAC THEN STAC
 ,
 ETAC listTheory.CONS_11 THEN EQ_PAIR_ASM_TAC THEN CONJS_TAC THEN TRY STAC THEN PAXTAC THEN STAC
]
QED

Theorem TX_BDS_TO_FETCH_RESULT_LEMMA:
!channel_id memory internal_state bd bd_ras bd_was first_bd_update bds.
  ((bd, bd_ras, bd_was), first_bd_update)::bds = tx_bds_to_fetch channel_id memory internal_state
  ==>
  bd_ras = get_bd_ras internal_state.registers (internal_state.qhp channel_id) /\
  bd_was = get_bd_ras internal_state.registers (internal_state.qhp channel_id) /\
  first_bd_update = no_update /\
  ?bytes.
    bytes = MAP memory bd_ras /\
    bd = form_bd_li bytes
Proof
INTRO_TAC THEN
PTAC bbb_usb_queue_txTheory.tx_bds_to_fetch THENL
[
 IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
 ,
 RLTAC THEN IRTAC TX_BDS_OF_TRANSFER_REC_RESULT_LEMMA THEN STAC
 ,
 RLTAC THEN IRTAC TX_BDS_OF_TRANSFER_REC_RESULT_LEMMA THEN STAC
 ,
 PTAC listTheory.NULL_DEF THEN TRY (ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC) THEN
 LRTAC THEN
 ETAC listTheory.APPEND THEN
 ETAC listTheory.CONS_11 THEN
 RLTAC THEN
 IRTAC TX_BDS_OF_TRANSFER_REC_RESULT_LEMMA THEN
 STAC
]
QED

Theorem NOT_EMPTY_TX_BDS_TO_FETCH_IMPLIES_QHP_NEQ_ZERO_LEMMA:
!channel_id memory internal_state bd bds.
  bd::bds = tx_bds_to_fetch channel_id memory internal_state
  ==>
  internal_state.qhp channel_id <> 0w
Proof
INTRO_TAC THEN
CCONTR_TAC THEN
ETAC boolTheory.NOT_CLAUSES THEN
IRTAC bbb_usb_queue_txTheory.QHP_EQ_ZERO_IMPLIES_TX_BDS_TO_FETCH_EQ_NULL THEN
QLRTAC THEN
IRTAC listTheory.NOT_CONS_NIL THEN
SOLVE_F_ASM_TAC
QED

Theorem FETCHED_BD_IS_FIRST_TX_LEMMA:
!channel_id internal_state1 internal_state2 addresses tag bytes memory
 fetched_bd_ras_was fetched_bd_update bd bd_ras bd_was first_bd_update bds.
  (addresses, tag) = tx_fetch_bd_addresses channel_id internal_state1 /\
  bytes = MAP memory addresses /\
  (internal_state2, SOME (fetched_bd_ras_was, fetched_bd_update)) = tx_fetch_bd channel_id internal_state1 (SOME (bytes, tag)) /\
  ((bd, bd_ras, bd_was), first_bd_update)::bds = tx_bds_to_fetch channel_id memory internal_state1
  ==>
  (bd, bd_ras, bd_was) = fetched_bd_ras_was /\
  first_bd_update = fetched_bd_update
Proof
INTRO_TAC THEN
ITAC NOT_EMPTY_TX_BDS_TO_FETCH_IMPLIES_QHP_NEQ_ZERO_LEMMA THEN
IRTAC TX_FETCH_BD_RESULT_LEMMA THEN
LRTAC THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
LRTAC THEN
IRTAC TX_FETCH_BD_ADDRESSES_RESULT_LEMMA THEN
IRTAC TX_BDS_TO_FETCH_RESULT_LEMMA THEN
AXTAC THEN
STAC
QED

Theorem TX_BDS_OF_TRANSFER_REC_EMPTY_IMPLIES_START_BD_ADDRESS_EQ_ZERO_LEMMA:
!memory registers visited_bds visited_bds_option start_bd_address.
  ([], visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds start_bd_address
  ==>
  start_bd_address = 0w
Proof
INTRO_TAC THEN PTAC bbb_usb_queue_txTheory.tx_bds_of_transfer_rec THEN EQ_PAIR_ASM_TAC THEN TRY STAC THEN
 IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC
QED

Theorem TX_BDS_TO_FETCH_EMPTY_IMPLIES_QHP_EQ_ZERO_LEMMA:
!channel_id memory internal_state.
  tx_bds_to_fetch channel_id memory internal_state = []
  ==>
  internal_state.qhp channel_id = 0w
Proof
INTRO_TAC THEN
PTAC bbb_usb_queue_txTheory.tx_bds_to_fetch THENL
[
 ETAC listTheory.NULL_EQ THEN IRTAC TX_BDS_OF_TRANSFER_REC_EMPTY_IMPLIES_START_BD_ADDRESS_EQ_ZERO_LEMMA THEN STAC
 ,
 ETAC listTheory.NULL_EQ THEN IRTAC TX_BDS_OF_TRANSFER_REC_EMPTY_IMPLIES_START_BD_ADDRESS_EQ_ZERO_LEMMA THEN STAC
 ,
 ETAC listTheory.NULL_EQ THEN IRTAC TX_BDS_OF_TRANSFER_REC_EMPTY_IMPLIES_START_BD_ADDRESS_EQ_ZERO_LEMMA THEN STAC
 ,
 PTAC listTheory.NULL_DEF THEN TRY (ETAC boolTheory.NOT_CLAUSES THEN SOLVE_F_ASM_TAC) THEN
 LRTAC THEN
 ETAC listTheory.APPEND THEN
 IRTAC listTheory.NOT_CONS_NIL THEN
 SOLVE_F_ASM_TAC
]
QED

Theorem QHP_EQ_ZERO_IMPLIES_TX_FETCH_BD_ADDRESSES_EMPTY_LEMMA:
!channel_id internal_state addresses tag.
  internal_state.qhp channel_id = 0w /\
  (addresses, tag) = tx_fetch_bd_addresses channel_id internal_state
  ==>
  addresses = []
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_fetch_bd_addresses THEN
EQ_PAIR_ASM_TAC THEN
STAC
QED

Theorem TX_BDS_TO_FETCH_EMPTY_IMPLIES_TX_FETCH_BD_ADDRESSES_EMPTY_LEMMA:
!channel_id memory internal_state addresses tag.
  tx_bds_to_fetch channel_id memory internal_state = [] /\
  tx_fetch_bd_addresses channel_id internal_state = (addresses, tag)
  ==>
  addresses = []
Proof
INTRO_TAC THEN
IRTAC TX_BDS_TO_FETCH_EMPTY_IMPLIES_QHP_EQ_ZERO_LEMMA THEN
IRTAC QHP_EQ_ZERO_IMPLIES_TX_FETCH_BD_ADDRESSES_EMPTY_LEMMA THEN
STAC
QED

Theorem TX_FETCH_BD_PRESERVES_REGISTERS_LEMMA:
!channel_id internal_state1 internal_state2 reply fetch_result.
  (internal_state2, fetch_result) = tx_fetch_bd channel_id internal_state1 reply
  ==>
  internal_state2.registers = internal_state1.registers
Proof
INTRO_TAC THEN PTAC bbb_usb_txTheory.tx_fetch_bd THEN EQ_PAIR_ASM_TAC THEN TRY STAC THEN
RLTAC THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [combinTheory.UPDATE_def] THEN
APP_SCALAR_TAC THEN
ASM_REWRITE_TAC []
QED

Theorem TX_FETCH_BD_PRESERVES_OTHER_CHANNELS_QHP_LEMMA:
!channel_id channel_id' internal_state1 internal_state2 reply fetch_result.
  channel_id' <> channel_id /\
  (internal_state2, fetch_result) = tx_fetch_bd channel_id internal_state1 reply
  ==>
  internal_state2.qhp channel_id' = internal_state1.qhp channel_id'
Proof
INTRO_TAC THEN PTAC bbb_usb_txTheory.tx_fetch_bd THEN EQ_PAIR_ASM_TAC THEN TRY STAC THEN
RLTAC THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [combinTheory.UPDATE_def] THEN
APP_SCALAR_TAC THEN
PAT_X_ASSUM “x <> x' : 8 word” (fn thm => ASSUME_TAC (GSYM thm)) THEN
ASM_REWRITE_TAC []
QED

Theorem TX_FETCH_BD_PRESERVES_OTHER_ENDPOINTS_TX_LEMMA:
!channel_id channel_id' endpoint_id' offset' internal_state1 internal_state2 endpoint1 endpoint2 reply fetch_result.
  32w <=+ channel_id /\ channel_id <=+ 91w /\
  32w <=+ channel_id' /\ channel_id' <=+ 91w /\
  channel_id' <> channel_id /\
  (internal_state2, fetch_result) = tx_fetch_bd channel_id internal_state1 reply /\
  endpoint_id' = w2w ((channel_id' - 32w) >>> 1) /\
  offset' = word_bit 0 channel_id' /\
  endpoint1 = internal_state1.endpoints_tx endpoint_id' /\
  endpoint2 = internal_state2.endpoints_tx endpoint_id'
  ==>
  endpoint2.sop offset' = endpoint1.sop offset' /\
  endpoint2.sop_li offset' = endpoint1.sop_li offset'
Proof
INTRO_TAC THEN PTAC bbb_usb_txTheory.tx_fetch_bd THEN EQ_PAIR_ASM_TAC THEN TRY STAC THEN
RLTAC THEN
LRTAC THEN
RECORD_TAC THEN
LRTAC THEN
PAT_X_ASSUM “endpoints_tx = (endpoint_id =+ endpoint') endpoints_tx'” (fn thm => ASSUME_TAC thm) THEN
LRTAC THEN
LRTAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
FIRTAC bbb_usb_lemmasTheory.DISTINCT_CHANNEL_IDS_IMPLIES_DISTINCT_ENDPOINT_IDS_OR_OFFSETS_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 IF_SPLIT_TAC THEN TRY (LRTAC THEN CONTR_NEG_ASM_TAC boolTheory.EQ_REFL) THEN STAC
 ,
 LRTAC THEN REWRITE_TAC [] THEN RLTAC THEN WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN
 LRTAC THEN RECORD_TAC THEN APP_SCALAR_TAC THEN PAT_X_ASSUM “x' <> x” (fn thm => ASSUME_TAC (GSYM thm)) THEN STAC 
]
QED

Theorem TX_FETCH_BD_PRESERVES_OTHER_CHANNEL_TX_BDS_TO_FETCH_LEMMA:
!channel_id channel_id' internal_state1 internal_state2 reply fetch_result memory.
  32w <=+ channel_id /\ channel_id <=+ 91w /\
  32w <=+ channel_id' /\ channel_id' <=+ 91w /\
  channel_id' <> channel_id /\
  (internal_state2, fetch_result) = tx_fetch_bd channel_id internal_state1 reply
  ==>
  tx_bds_to_fetch channel_id' memory internal_state2 = tx_bds_to_fetch channel_id' memory internal_state1
Proof
INTRO_TAC THEN
ETAC bbb_usb_queue_txTheory.tx_bds_to_fetch THEN
ITAC TX_FETCH_BD_PRESERVES_OTHER_CHANNELS_QHP_LEMMA THEN LRTAC THEN
ITAC TX_FETCH_BD_PRESERVES_REGISTERS_LEMMA THEN LRTAC THEN
ONCE_LETS_TAC THEN RLTAC THEN
ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
ONCE_LETS_TAC THEN
ONCE_LETS_TAC THEN LRTAC THEN
ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
ONCE_LETS_TAC THEN
IF_SPLIT_TAC THEN TRY STAC THEN
IF_SPLIT_TAC THEN TRY STAC THEN
ONCE_LETS_TAC THEN
ONCE_LETS_TAC THEN
ONCE_LETS_TAC THEN
ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
ONCE_LETS_TAC THEN
ONCE_LETS_TAC THEN
ONCE_LETS_TAC THEN
FIRTAC TX_FETCH_BD_PRESERVES_OTHER_ENDPOINTS_TX_LEMMA THEN
RLTAC THEN
ONCE_LETS_TAC THEN
ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
ONCE_LETS_TAC THEN
RLTAC THEN
RLTAC THEN
STAC
QED

Theorem EQ_REGISTERS_QHP_PRESERVES_TX_FETCH_BD_ADDRESSES_LEMMA:
!channel_id internal_state1 internal_state2.
  internal_state2.registers = internal_state1.registers /\
  internal_state2.qhp channel_id = internal_state1.qhp channel_id
  ==>
  tx_fetch_bd_addresses channel_id internal_state2 = tx_fetch_bd_addresses channel_id internal_state1
Proof
INTRO_TAC THEN ETAC bbb_usb_txTheory.tx_fetch_bd_addresses THEN STAC
QED



Theorem TX_BDS_OF_TRANSFER_REC_ZERO_BD_ADDRESS_IMPLIES_SOME_VISITED_BDS_LEMMA:
!memory registers visited_bds bds_to_fetch visited_bds_option.
  (bds_to_fetch, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds 0w
  ==>
  visited_bds_option = SOME visited_bds
Proof
INTRO_TAC THEN PTAC bbb_usb_queue_txTheory.tx_bds_of_transfer_rec THEN TRY (CONTR_NEG_ASM_TAC boolTheory.EQ_REFL) THEN EQ_PAIR_ASM_TAC THEN STAC
QED

Theorem TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_IND_LEMMA:
!memory1 registers visited_bds bd_address.
  (\memory1 registers visited_bds bd_address.
   !memory2 bds_to_fetch1 ras1 visited_bds_option.
    (bds_to_fetch1, visited_bds_option) = tx_bds_of_transfer_rec memory1 registers visited_bds bd_address /\
    ras1 = bds_to_fetch_ras bds_to_fetch1 /\
    MEMORY_EQ ras1 memory1 memory2
    ==>
    (bds_to_fetch1, visited_bds_option) = tx_bds_of_transfer_rec memory2 registers visited_bds bd_address) memory1 registers visited_bds bd_address
Proof
MATCH_MP_TAC bbb_usb_queue_txTheory.tx_bds_of_transfer_rec_ind THEN
BETA_TAC THEN
INTRO_TAC THEN
INTRO_TAC THEN
PTAC bbb_usb_queue_txTheory.tx_bds_of_transfer_rec THENL
[
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN
 ITAC bbb_usb_queue_txTheory.TX_BDS_OF_TRANSFER_REC_ZERO_START_IMPLIES_EMPTY_BDS_LEMMA THEN
 IRTAC TX_BDS_OF_TRANSFER_REC_ZERO_BD_ADDRESS_IMPLIES_SOME_VISITED_BDS_LEMMA THEN
 STAC
 ,
 WEAKEN_TAC is_forall THEN
 PTAC bbb_usb_queue_txTheory.tx_bds_of_transfer_rec THEN
 EQ_PAIR_ASM_TAC THEN
 NLRTAC 2 THEN
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
 PTAC bbb_usb_queue_txTheory.tx_bds_of_transfer_rec THENL
 [
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 2 THEN
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
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 2 THEN
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
 PAT_X_ASSUM “(bds, visited_bds_option) = tx_bds_of_transfer_rec memory registers visited_bds a” (fn thm => ASSUME_TAC thm) THEN
 RW_HYP_LEMMA_TAC bbb_usb_queue_txTheory.tx_bds_of_transfer_rec THEN
 IF_SPLIT_TAC THEN TRY CONTR_ASMS_TAC THEN
 LETS_TAC THEN
 IF_SPLIT_TAC THEN1
 (EQ_PAIR_ASM_TAC THEN LRTAC THEN ETAC bd_queuesTheory.bds_to_fetch_ras THEN ETAC listTheory.APPEND_NIL THEN LRTAC THEN IRTAC bbb_usb_lemmasTheory.MEMORY_EQ_IMPLIES_MAP_MEMORY_EQ_LEMMA THEN LRTAC THEN RLTAC THEN RLTAC THEN LRTAC THEN EQ_PAIR_ASM_TAC THEN NRLTAC 2 THEN CONTR_ASMS_TAC) THEN
 AITAC THEN
 EQ_PAIR_ASM_TAC THEN
 LRTAC THEN
 ETAC bd_queuesTheory.bds_to_fetch_ras THEN
 LRTAC THEN
 IRTAC bbb_usb_lemmasTheory.MEMORY_EQ_APPEND_LEMMA THEN
 IRTAC bbb_usb_lemmasTheory.MEMORY_EQ_IMPLIES_MAP_MEMORY_EQ_LEMMA THEN
 LRTAC THEN RLTAC THEN RLTAC THEN LRTAC THEN EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN REWRITE_TAC [listTheory.CONS_11] THEN
 RLTAC THEN
 RLTAC THEN
 AIRTAC THEN
 RLTAC THEN
 EQ_PAIR_ASM_TAC THEN
 STAC
]
QED

Theorem TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA:
!memory1 memory2 registers bds_to_fetch1 visited_bds visited_bds_option ras1 bd_address.
  (bds_to_fetch1, visited_bds_option) = tx_bds_of_transfer_rec memory1 registers visited_bds bd_address /\
  ras1 = bds_to_fetch_ras bds_to_fetch1 /\
  MEMORY_EQ ras1 memory1 memory2
  ==>
  (bds_to_fetch1, visited_bds_option) = tx_bds_of_transfer_rec memory2 registers visited_bds bd_address
Proof
REWRITE_TAC [BETA_RULE TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_IND_LEMMA]
QED

Theorem BDS_TO_FETCH_RAS_APPEND_LEMMA:
!bds1 bds2 ras12.
  ras12 = bds_to_fetch_ras (bds1 ++ bds2)
  ==>
  ?ras1 ras2.
    ras1 = bds_to_fetch_ras bds1 /\
    ras2 = bds_to_fetch_ras bds2 /\
    ras12 = ras1 ++ ras2
Proof
Induct THENL
[
 REWRITE_TAC [listTheory.APPEND, bd_queuesTheory.bds_to_fetch_ras] THEN
 INTRO_TAC THEN
 EXISTS_EQ_TAC THEN
 ASM_REWRITE_TAC [listTheory.APPEND]
 ,
 INTRO_TAC THEN
 ETAC listTheory.APPEND THEN
 PTAC bd_queuesTheory.bds_to_fetch_ras THEN
 NLRTAC 2 THEN
 NLRTAC 2 THEN
 ETAC bd_queuesTheory.bds_to_fetch_ras THEN
 AITAC THEN
 PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (Q.SPEC ‘bds2’ thm)) THEN
 AXTAC THEN
 PAT_X_ASSUM “bds_to_fetch_ras (bds1 ++ bds2) = ras1 ++ ras2” (fn thm => ASSUME_TAC thm) THEN
 ALL_LRTAC THEN
 EXISTS_EQ_TAC THEN
 REWRITE_TAC [listTheory.APPEND_ASSOC]
]
QED

Theorem TX_BDS_OF_TRANSFERS_REC_MEMORY_DEPENDENCE_IND_LEMMA:
!memory1 registers visited_bds bd_address.
  (\memory1 registers visited_bds bd_address.
   !memory2 bds_to_fetch1 ras1 visited_bds_option.
    bds_to_fetch1 = tx_bds_of_transfers_rec memory1 registers visited_bds bd_address /\
    ras1 = bds_to_fetch_ras bds_to_fetch1 /\
    MEMORY_EQ ras1 memory1 memory2
    ==>
    bds_to_fetch1 = tx_bds_of_transfers_rec memory2 registers visited_bds bd_address) memory1 registers visited_bds bd_address
Proof
MATCH_MP_TAC bbb_usb_queue_txTheory.tx_bds_of_transfers_rec_ind THEN
APP_SCALAR_TAC THEN
INTRO_TAC THEN
INTRO_TAC THEN
PTAC bbb_usb_queue_txTheory.tx_bds_of_transfers_rec THENL
[
 PTAC bbb_usb_queue_txTheory.tx_bds_of_transfers_rec THEN STAC
 ,
 PTAC bbb_usb_queue_txTheory.tx_bds_of_transfers_rec THEN TRY STAC THENL
 [
  IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN LRTAC THEN CONTR_ASMS_TAC
  ,
  IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN LRTAC THEN CONTR_ASMS_TAC
  ,
  LRTAC THEN IRTAC BDS_TO_FETCH_RAS_APPEND_LEMMA THEN AXTAC THEN IRTAC bbb_usb_lemmasTheory.MEMORY_EQ_APPEND_LEMMA THEN
  IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN LRTAC THEN CONTR_ASMS_TAC
 ]
 ,
 PTAC bbb_usb_queue_txTheory.tx_bds_of_transfers_rec THENL
 [
  LRTAC THEN ETAC listTheory.NULL_EQ THEN NLRTAC 2 THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN STAC
  ,
  LRTAC THEN LRTAC THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN STAC
  ,
  LRTAC THEN LRTAC THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN STAC
  ,
  LRTAC THEN IRTAC BDS_TO_FETCH_RAS_APPEND_LEMMA THEN AXTAC THEN PAT_X_ASSUM “x = x1 ++ x2” (fn thm => ASSUME_TAC thm) THEN LRTAC THEN
  IRTAC bbb_usb_lemmasTheory.MEMORY_EQ_APPEND_LEMMA THEN 
  IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN NRLTAC 2 THEN CONTR_ASMS_TAC
 ]
 ,
 PTAC bbb_usb_queue_txTheory.tx_bds_of_transfers_rec THENL
 [
  LRTAC THEN ETAC listTheory.NULL_EQ THEN NLRTAC 2 THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN STAC
  ,
  LRTAC THEN LRTAC THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN STAC
  ,
  LRTAC THEN LRTAC THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN STAC
  ,
  LRTAC THEN IRTAC BDS_TO_FETCH_RAS_APPEND_LEMMA THEN AXTAC THEN PAT_X_ASSUM “x = x1 ++ x2” (fn thm => ASSUME_TAC thm) THEN LRTAC THEN
  IRTAC bbb_usb_lemmasTheory.MEMORY_EQ_APPEND_LEMMA THEN 
  IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN NRLTAC 2 THEN RLTAC THEN LRTAC THEN CONTR_ASMS_TAC
 ]
 ,
 RW_HYP_LEMMA_TAC bbb_usb_queue_txTheory.tx_bds_of_transfers_rec THEN
 IF_SPLIT_TAC THEN TRY CONTR_ASMS_TAC THEN
 LETS_TAC THEN
 IF_SPLIT_TAC THEN1
 (LRTAC THEN LRTAC THEN ETAC listTheory.NULL_EQ THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN CONTR_ASMS_TAC) THEN
 IF_SPLIT_TAC THEN1
 (LRTAC THEN LRTAC THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN CONTR_ASMS_TAC) THEN
 IF_SPLIT_TAC THEN1
 (LRTAC THEN LRTAC THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN RLTAC THEN RLTAC THEN RLTAC THEN CONTR_ASMS_TAC) THEN
 AITAC THEN
 REPEAT (WEAKEN_TAC is_neg) THEN
 LRTAC THEN
 IRTAC BDS_TO_FETCH_RAS_APPEND_LEMMA THEN AXTAC THEN NLRTAC 2 THEN LRTAC THEN IRTAC bbb_usb_lemmasTheory.MEMORY_EQ_APPEND_LEMMA THEN AITAC THEN
 IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN RLTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN STAC
]
QED

Theorem TX_BDS_OF_TRANSFERS_REC_MEMORY_DEPENDENCE_LEMMA:
!memory1 memory2 registers visited_bds bds_to_fetch1 ras1 bd_address.
  bds_to_fetch1 = tx_bds_of_transfers_rec memory1 registers visited_bds bd_address /\
  ras1 = bds_to_fetch_ras bds_to_fetch1 /\
  MEMORY_EQ ras1 memory1 memory2
  ==>
  bds_to_fetch1 = tx_bds_of_transfers_rec memory2 registers visited_bds bd_address
Proof
REWRITE_TAC [BETA_RULE TX_BDS_OF_TRANSFERS_REC_MEMORY_DEPENDENCE_IND_LEMMA]
QED

Theorem TX_BDS_TO_FETCH_MEMORY_DEPENDENCE_LEMMA:
!channel_id memory1 memory2 internal_state bds_to_fetch1 ras1.
  bds_to_fetch1 = tx_bds_to_fetch channel_id memory1 internal_state /\
  ras1 = bds_to_fetch_ras bds_to_fetch1 /\
  MEMORY_EQ ras1 memory1 memory2
  ==>
  tx_bds_to_fetch channel_id memory2 internal_state = bds_to_fetch1
Proof
INTRO_TAC THEN
ETAC bbb_usb_queue_txTheory.tx_bds_to_fetch THEN
LETS_TAC THEN
IF_SPLIT_TAC THENL
[
 IF_SPLIT_TAC THEN1 (LRTAC THEN LRTAC THEN ETAC listTheory.NULL_EQ THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN STAC) THEN
 IF_SPLIT_TAC THEN1 (LRTAC THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN CONTR_ASMS_TAC) THEN
 IF_SPLIT_TAC THEN1 (LRTAC THEN LRTAC THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN CONTR_ASMS_TAC) THEN
 LRTAC THEN
 IRTAC BDS_TO_FETCH_RAS_APPEND_LEMMA THEN AXTAC THEN NLRTAC 2 THEN LRTAC THEN IRTAC bbb_usb_lemmasTheory.MEMORY_EQ_APPEND_LEMMA THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN LRTAC THEN CONTR_ASMS_TAC
 ,
 IF_SPLIT_TAC THENL
 [
  IF_SPLIT_TAC THEN1 (LRTAC THEN LRTAC THEN ETAC listTheory.NULL_EQ THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN LRTAC THEN CONTR_ASMS_TAC) THEN
  IF_SPLIT_TAC THEN1 (LRTAC THEN LRTAC THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN STAC) THEN
  IF_SPLIT_TAC THEN1 (LRTAC THEN LRTAC THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN CONTR_ASMS_TAC) THEN LRTAC THEN
  IRTAC BDS_TO_FETCH_RAS_APPEND_LEMMA THEN AXTAC THEN NLRTAC 2 THEN LRTAC THEN IRTAC bbb_usb_lemmasTheory.MEMORY_EQ_APPEND_LEMMA THEN
  IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN CONTR_ASMS_TAC
  ,
  IF_SPLIT_TAC THENL
  [
   IF_SPLIT_TAC THEN1 (LRTAC THEN LRTAC THEN ETAC listTheory.NULL_EQ THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN LRTAC THEN CONTR_ASMS_TAC) THEN
   IF_SPLIT_TAC THEN1 (LRTAC THEN LRTAC THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN STAC) THEN
   IF_SPLIT_TAC THEN1 (LRTAC THEN LRTAC THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN STAC) THEN
   LRTAC THEN IRTAC BDS_TO_FETCH_RAS_APPEND_LEMMA THEN AXTAC THEN NLRTAC 2 THEN LRTAC THEN IRTAC bbb_usb_lemmasTheory.MEMORY_EQ_APPEND_LEMMA THEN
   IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN RLTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN CONTR_ASMS_TAC
   ,
   IF_SPLIT_TAC THEN1 (LRTAC THEN LRTAC THEN ETAC listTheory.NULL_EQ THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN LRTAC THEN CONTR_ASMS_TAC) THEN
   IF_SPLIT_TAC THEN1 (LRTAC THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN CONTR_ASMS_TAC) THEN
   IF_SPLIT_TAC THEN1 (LRTAC THEN LRTAC THEN IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN RLTAC THEN RLTAC THEN RLTAC THEN CONTR_ASMS_TAC) THEN
   LRTAC THEN
   IRTAC BDS_TO_FETCH_RAS_APPEND_LEMMA THEN AXTAC THEN NLRTAC 2 THEN LRTAC THEN IRTAC bbb_usb_lemmasTheory.MEMORY_EQ_APPEND_LEMMA THEN
   IRTAC TX_BDS_OF_TRANSFER_REC_MEMORY_DEPENDENCE_LEMMA THEN RLTAC THEN EQ_PAIR_ASM_TAC THEN
   NLRTAC 2 THEN
   REPEAT (WEAKEN_TAC is_neg) THEN
   NRLTAC 2 THEN
   NRLTAC 2 THEN
   RLTAC THEN
   RLTAC THEN
   REPEAT (WEAKEN_TAC is_eq) THEN
   IRTAC TX_BDS_OF_TRANSFERS_REC_MEMORY_DEPENDENCE_LEMMA THEN
   STAC
  ]
 ]
]
QED

Theorem TX_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_REGISTERS_LEMMA:
!internal_state1 internal_state2 bd replies new_requests complete channel_id.
  (internal_state2, new_requests, complete) = tx_process_replies_generate_requests channel_id internal_state1 bd replies
  ==>
  internal_state2.registers = internal_state1.registers
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_process_replies_generate_requests THEN
EQ_PAIR_ASM_TAC THEN
RLTAC THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem TX_PROCESS_REPLIES_GENERATE_REQUESTS_IMPLIES_QMEM_LRAM_EQ_LEMMA:
!internal_state1 internal_state2 bd replies new_requests complete channel_id.
  (internal_state2, new_requests, complete) = tx_process_replies_generate_requests channel_id internal_state1 bd replies
  ==>
  QMEM_LRAM_EQ internal_state2.registers internal_state1.registers
Proof
INTRO_TAC THEN ETAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ THEN IRTAC TX_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_REGISTERS_LEMMA THEN STAC
QED

Theorem TX_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_QHP_LEMMA:
!internal_state1 internal_state2 bd replies new_requests complete channel_id.
  (internal_state2, new_requests, complete) = tx_process_replies_generate_requests channel_id internal_state1 bd replies
  ==>
  internal_state1.qhp = internal_state2.qhp
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_process_replies_generate_requests THEN
EQ_PAIR_ASM_TAC THEN
RLTAC THEN
LRTAC THEN
REPEAT (WEAKEN_TAC (fn _ => true)) THEN
RECORD_TAC THEN
STAC
QED

Theorem TX_PROCESS_REPLIES_GENERATE_REQUESTS_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA:
!internal_state1 internal_state2 bd replies new_requests complete channel_id.
  (internal_state2, new_requests, complete) = tx_process_replies_generate_requests channel_id internal_state1 bd replies
  ==>
  ENDPOINTS_TX_SOP_LI_EQ internal_state2.endpoints_tx internal_state1.endpoints_tx
Proof
INTRO_TAC THEN
ETAC bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ THEN
GEN_TAC THEN
PTAC bbb_usb_txTheory.tx_process_replies_generate_requests THEN
EQ_PAIR_ASM_TAC THEN
RLTAC THEN
LRTAC THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN APP_SCALAR_TAC THEN IF_SPLIT_TAC THEN TRY STAC THEN
 LRTAC THEN RLTAC THEN ALL_LRTAC THEN RECORD_TAC THEN STAC
QED

Theorem TX_PROCESS_REPLIES_GENERATE_REQUESTS_IMPLIES_READ_REQUEST_LEMMA:
!internal_state1 internal_state2 new_requests complete bd replies queue_id.
  (internal_state2, new_requests, complete) = tx_process_replies_generate_requests queue_id internal_state1 bd replies
  ==>
  new_requests = [] \/
  ?addresses. new_requests = [request_read addresses tag]
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_process_replies_generate_requests THENL
[
 EQ_PAIR_ASM_TAC THEN
 NLRTAC 3 THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 NLRTAC 3 THEN
 EXISTS_EQ_TAC
 ,
 EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN STAC
]
QED

Theorem TX_PROCESS_REPLIES_GENERATE_REQUESTS_READ_ADDRESSES_LEMMA:
!channel_id internal_state1 internal_state2 new_requests complete bd li replies.
  (internal_state2, new_requests, complete) = tx_process_replies_generate_requests channel_id internal_state1 (bd, li) replies
  ==>
  new_requests = [] \/
  ?read_addresses number_of_read_bytes request_size start_address endpoint_id endpoint.
    endpoint_id = w2w ((channel_id − 32w) >>> 1) /\
    endpoint = internal_state1.endpoints_tx endpoint_id /\
    new_requests = [request_read read_addresses tag] /\
    start_address = buffer_pointer bd + number_of_read_bytes /\
    request_size = get_request_size number_of_read_bytes (buffer_length bd) /\
    read_addresses = generate_consecutive_addresses start_address request_size /\
    number_of_read_bytes <+ buffer_length bd
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_process_replies_generate_requests THEN EQ_PAIR_ASM_TAC THEN TRY STAC THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN PAXTAC THEN CONJS_TAC THEN TRY STAC THEN STAC
QED

Theorem TX_PROCESS_REPLIES_GENERATE_REQUESTS_IMPLIES_READ_ADDRESSES_IN_BUFFER_READ_ADDRESSES_LEMMA:
!channel_id internal_state1 internal_state2 bd li replies new_requests complete addresses tag
 buffer_start_address buffer_byte_size buffer_read_addresses.
  (internal_state2, new_requests, complete) = tx_process_replies_generate_requests channel_id internal_state1 (bd, li) replies /\
  MEM (request_read addresses tag) new_requests /\
  buffer_start_address = buffer_pointer bd /\
  buffer_byte_size = w2n (buffer_length bd) /\
  buffer_read_addresses = generate_consecutive_addresses buffer_start_address buffer_byte_size
  ==>
  LIST1_IN_LIST2 addresses buffer_read_addresses
Proof
INTRO_TAC THEN
IRTAC TX_PROCESS_REPLIES_GENERATE_REQUESTS_READ_ADDRESSES_LEMMA THEN
SPLIT_ASM_DISJS_TAC THEN1 (LRTAC THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC) THEN
AXTAC THEN
WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN
LRTAC THEN
ETAC listTheory.MEM THEN
REMOVE_F_DISJUNCTS_TAC THEN
ETAC stateTheory.interconnect_request_type_11 THEN
NLRTAC 2 THEN
RLTAC THEN
IRTAC bbb_usb_lemmasTheory.READ_ADDRESSES_IN_BUFFER_ADDRESSES_N_LEMMA THEN
STAC
QED

Theorem TX_WRITE_BACK_SOP_BD1_WRITE_ADDRESS_IS_BD_WAS_LEMMA:
!internal_state2 address_bytes tag released_bds internal_state endpoint endpoint_id bds_to_write_back write_address
 bd_li ras was remaining_packet_bds.
  SOME ((bd_li, ras, was)::remaining_packet_bds) = get_dma_packet_bds_to_release internal_state endpoint bds_to_write_back /\
  (internal_state2, address_bytes, tag, released_bds) = tx_write_back_sop_bd1 internal_state endpoint_id bd_li was /\
  MEM write_address (MAP FST address_bytes)
  ==>
  ?bd bd_ras bd_was.
    MEM (bd, bd_ras, bd_was) bds_to_write_back /\
    MEM write_address bd_was
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_write_back_sop_bd1 THEN
EQ_PAIR_ASM_TAC THEN
NLRTAC 4 THEN
IRTAC bbb_usb_lemmasTheory.MEM_MAP_FST_MERGE_LISTS_LEMMA THEN
LRTAC THEN
WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN
WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN
WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN
IRTAC rich_listTheory.MEM_DROP_IMP THEN
PAXTAC THEN
ASM_REWRITE_TAC [] THEN
MATCH_MP_TAC bbb_usb_lemmasTheory.MEM_DMA_PACKET_BDS_TO_RELEASE_IMPLIES_MEM_BDS_TO_WRITE_BACK_LEMMA THEN
PAXTAC THEN
ASM_REWRITE_TAC [listTheory.MEM]
QED

Theorem TX_WRITE_BACK_SOP_BD2_WRITE_ADDRESS_IS_BD_WAS_LEMMA:
!internal_state2 address_bytes tag released_bds internal_state endpoint endpoint_id bds_to_write_back write_address
 bd_li ras was remaining_packet_bds.
  SOME ((bd_li, ras, was)::remaining_packet_bds) = get_dma_packet_bds_to_release internal_state endpoint bds_to_write_back /\
  (internal_state2, address_bytes, tag, released_bds) = tx_write_back_sop_bd2 internal_state endpoint_id bd_li was /\
  MEM write_address (MAP FST address_bytes)
  ==>
  ?bd bd_ras bd_was.
    MEM (bd, bd_ras, bd_was) bds_to_write_back /\
    MEM write_address bd_was
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_write_back_sop_bd2 THEN
EQ_PAIR_ASM_TAC THEN
NLRTAC 2 THEN
ETAC listTheory.MAP THEN
ETAC listTheory.MEM THEN
SOLVE_F_ASM_TAC
QED

Theorem TX_WRITE_BACK_SOP_BD3_WRITE_ADDRESS_IS_BD_WAS_LEMMA:
!internal_state2 address_bytes tag released_bds internal_state endpoint endpoint_id bds_to_write_back write_address
 bd remaining_packet_bds.
  SOME (bd::remaining_packet_bds) = get_dma_packet_bds_to_release internal_state endpoint bds_to_write_back /\
  (internal_state2, address_bytes, tag, released_bds) = tx_write_back_sop_bd3 internal_state endpoint_id bd remaining_packet_bds /\
  MEM write_address (MAP FST address_bytes)
  ==>
  ?bd bd_ras bd_was.
    MEM (bd, bd_ras, bd_was) bds_to_write_back /\
    MEM write_address bd_was
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_write_back_sop_bd3 THENL
[
 EQ_PAIR_ASM_TAC THEN
 NLRTAC 4 THEN
 IRTAC bbb_usb_lemmasTheory.MEM_MAP_FST_MERGE_LISTS_LEMMA THEN
 WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN WEAKEN_TAC is_eq THEN
 LRTAC THEN
 IRTAC rich_listTheory.MEM_DROP_IMP THEN
 WEAKEN_TAC is_eq THEN
 LRTAC THEN
 LRTAC THEN
 PAXTAC THEN
 ASM_REWRITE_TAC [] THEN
 MATCH_MP_TAC bbb_usb_lemmasTheory.MEM_DMA_PACKET_BDS_TO_RELEASE_IMPLIES_MEM_BDS_TO_WRITE_BACK_LEMMA THEN
 PAXTAC THEN
 ASM_REWRITE_TAC [listTheory.MEM]
 ,
 EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN ETAC listTheory.MAP THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
]
QED

Theorem TX_WRITE_BACK_SOP_BD4_WRITE_ADDRESS_IS_BD_WAS_LEMMA:
!internal_state2 address_bytes tag released_bds internal_state endpoint endpoint_id bds_to_write_back write_address
 bd remaining_packet_bds.
  SOME (bd::remaining_packet_bds) = get_dma_packet_bds_to_release internal_state endpoint bds_to_write_back /\
  (internal_state2, address_bytes, tag, released_bds) = tx_write_back_sop_bd4 internal_state endpoint_id bd remaining_packet_bds /\
  MEM write_address (MAP FST address_bytes)
  ==>
  ?bd bd_ras bd_was.
    MEM (bd, bd_ras, bd_was) bds_to_write_back /\
    MEM write_address bd_was
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_write_back_sop_bd4 THEN
EQ_PAIR_ASM_TAC THEN
NLRTAC 2 THEN ETAC listTheory.MAP THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
QED

Theorem TX_WRITE_BACK_BD_WRITE_ADDRESS_IS_BD_WAS_LEMMA:
!internal_state2 address_bytes tag released_bds channel_id environment internal_state bds_to_write_back write_address.
  (internal_state2, address_bytes, tag, released_bds) = tx_write_back_bd channel_id environment internal_state bds_to_write_back /\
  MEM write_address (MAP FST address_bytes)
  ==>
  ?bd bd_ras bd_was.
    MEM (bd, bd_ras, bd_was) bds_to_write_back /\
    MEM write_address bd_was
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_write_back_bd THENL
[
 IRTAC TX_WRITE_BACK_SOP_BD1_WRITE_ADDRESS_IS_BD_WAS_LEMMA THEN STAC
 ,
 IRTAC TX_WRITE_BACK_SOP_BD2_WRITE_ADDRESS_IS_BD_WAS_LEMMA THEN STAC
 ,
 IRTAC TX_WRITE_BACK_SOP_BD3_WRITE_ADDRESS_IS_BD_WAS_LEMMA THEN STAC
 ,
 IRTAC TX_WRITE_BACK_SOP_BD4_WRITE_ADDRESS_IS_BD_WAS_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN ETAC listTheory.MAP THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
 ,
 EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN ETAC listTheory.MAP THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
 ,
 EQ_PAIR_ASM_TAC THEN ALL_LRTAC THEN ETAC listTheory.MAP THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
]
QED

Theorem TX_WRITE_BACK_SOP_BD1_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINTS_TX_SOP_LI_EQ_LEMMA:
!internal_state2 address_bytes tag released_bds endpoint_id internal_state1 bd was.
  (internal_state2, address_bytes, tag, released_bds) = tx_write_back_sop_bd1 internal_state1 endpoint_id bd was
  ==>
  QMEM_LRAM_EQ internal_state1.registers internal_state2.registers /\
  internal_state2.qhp = internal_state1.qhp /\
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
ETAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ THEN
ETAC bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ THEN
PTAC bbb_usb_txTheory.tx_write_back_sop_bd1 THEN
EQ_PAIR_ASM_TAC THEN RLTAC THEN LRTAC THEN RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN APP_SCALAR_TAC THEN
LRTAC THEN
LRTAC THEN
REWRITE_TAC [] THEN
GEN_TAC THEN
IF_SPLIT_TAC THEN TRY IF_SPLIT_TAC THEN REWRITE_TAC [] THENL
[
 NLRTAC 2 THEN RECORD_TAC THEN STAC
 ,
 LRTAC THEN RECORD_TAC THEN STAC
]
QED

Theorem TX_WRITE_BACK_SOP_BD2_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINTS_TX_SOP_LI_EQ_LEMMA:
!internal_state2 address_bytes tag released_bds endpoint_id internal_state1 bd was.
  (internal_state2, address_bytes, tag, released_bds) = tx_write_back_sop_bd2 internal_state1 endpoint_id bd was
  ==>
  QMEM_LRAM_EQ internal_state1.registers internal_state2.registers /\
  internal_state2.qhp = internal_state1.qhp /\
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
ETAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ THEN
ETAC bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ THEN
PTAC bbb_usb_txTheory.tx_write_back_sop_bd2 THEN
EQ_PAIR_ASM_TAC THEN RLTAC THEN LRTAC THEN RECORD_TAC THEN
REWRITE_TAC [] THEN
GEN_TAC THEN
ALL_LRTAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THEN TRY IF_SPLIT_TAC THEN TRY STAC THEN
 LRTAC THEN RECORD_TAC THEN STAC
QED

Theorem TX_WRITE_BACK_SOP_BD3_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINTS_TX_SOP_LI_EQ_LEMMA:
!internal_state2 address_bytes tag released_bds endpoint_id internal_state1 bd packet_bds.
  (internal_state2, address_bytes, tag, released_bds) = tx_write_back_sop_bd3 internal_state1 endpoint_id bd packet_bds
  ==>
  QMEM_LRAM_EQ internal_state1.registers internal_state2.registers /\
  internal_state2.qhp = internal_state1.qhp /\
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
ETAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ THEN
ETAC bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ THEN
PTAC bbb_usb_txTheory.tx_write_back_sop_bd3 THENL
[
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 LRTAC THEN
 RECORD_TAC THEN
 REWRITE_TAC [] THEN
 GEN_TAC THEN
 ALL_LRTAC THEN
 ETAC combinTheory.UPDATE_def THEN
 APP_SCALAR_TAC THEN
 IF_SPLIT_TAC THEN TRY IF_SPLIT_TAC THEN TRY STAC THEN
 LRTAC THEN RECORD_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 STAC
]
QED

Theorem TX_WRITE_BACK_SOP_BD4_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINTS_TX_SOP_LI_EQ_LEMMA:
!internal_state2 address_bytes tag released_bds endpoint_id internal_state1 bds packet_bds.
  (internal_state2, address_bytes, tag, released_bds) = tx_write_back_sop_bd4 internal_state1 endpoint_id bds packet_bds
  ==>
  QMEM_LRAM_EQ internal_state1.registers internal_state2.registers /\
  internal_state2.qhp = internal_state1.qhp /\
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
ETAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ THEN
ETAC bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ THEN
PTAC bbb_usb_txTheory.tx_write_back_sop_bd4 THEN
EQ_PAIR_ASM_TAC THEN
ALL_LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [] THEN
GEN_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THEN TRY IF_SPLIT_TAC THEN TRY STAC THEN
LRTAC THEN RECORD_TAC THEN STAC
QED

Theorem TX_WRITE_BACK_BD_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINTS_TX_SOP_LI_EQ_LEMMA:
!internal_state2 address_bytes tag released_bds channel_id environment internal_state1 bds_to_write_back.
  (internal_state2, address_bytes, tag, released_bds) = tx_write_back_bd channel_id environment internal_state1 bds_to_write_back
  ==>
  QMEM_LRAM_EQ internal_state1.registers internal_state2.registers /\
  internal_state2.qhp = internal_state1.qhp /\
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_write_back_bd THEN TRY (ETAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ THEN ETAC bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ THEN EQ_PAIR_ASM_TAC THEN STAC) THENL
[
 IRTAC TX_WRITE_BACK_SOP_BD1_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 IRTAC TX_WRITE_BACK_SOP_BD2_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 IRTAC TX_WRITE_BACK_SOP_BD3_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 IRTAC TX_WRITE_BACK_SOP_BD4_PRESERVES_QMEM_LRAM_EQ_QHP_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN STAC
]
QED

Theorem TX_WRITE_BACK_BD_ADDRESSES_ARE_DECLARED_LEMMA:
!write_addresses channel_id environment internal_state1 internal_state2 bds_to_write_back address_bytes tag released_bds.
  write_addresses = tx_write_back_bd_addresses channel_id environment internal_state1 bds_to_write_back /\
  (internal_state2, address_bytes, tag, released_bds) = tx_write_back_bd channel_id environment internal_state1 bds_to_write_back
  ==>
  LIST1_IN_LIST2 (MAP FST address_bytes) write_addresses
Proof
INTRO_TAC THEN
PTAC bbb_usb_txTheory.tx_write_back_bd_addresses THEN
LRTAC THEN
REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
QED

Theorem TX_BD_TRANSFER_RAS_WAS_INTERNAL_STATE_INDEPENDENT_LEMMA:
!(internal_state1 : 'a) (internal_state2 : 'a) bd.
  tx_bd_transfer_ras_was internal_state1 bd = tx_bd_transfer_ras_was internal_state2 bd
Proof
REPEAT GEN_TAC THEN
PTAC bbb_usb_txTheory.tx_bd_transfer_ras_was THEN
PTAC bbb_usb_txTheory.tx_bd_transfer_ras_was THEN
STAC
QED

Theorem QHP_QMEM_LRAM_EQ_IMPLIES_TX_FETCH_BD_ADDRESSES_EQ_LEMMA:
!internal_state1 internal_state2 channel_id.
  internal_state2.qhp = internal_state1.qhp /\
  QMEM_LRAM_EQ internal_state1.registers internal_state2.registers
  ==>
  tx_fetch_bd_addresses channel_id internal_state2 = tx_fetch_bd_addresses channel_id internal_state1
Proof
INTRO_TAC THEN
ETAC bbb_usb_txTheory.tx_fetch_bd_addresses THEN
LRTAC THEN
IF_SPLIT_TAC THEN TRY STAC THEN
IRTAC bbb_usb_lemmasTheory.QMEM_LRAM_EQ_IMPLIES_GET_BD_RAS_EQ_LEMMA THEN
STAC
QED

val _ = export_theory();

