open HolKernel Parse boolLib bossLib helper_tactics;
open bbb_usb_schedulerTheory;

val _ = new_theory "bbb_usb_scheduler_lemmas";

Theorem FIND_TX_RX_SCHEDULABLE_ENDPOINT_IMPLIES_CHANNEL_ID_LEQ_91_LEMMA:
!number_of_queues environment internal_state1 internal_state2 channels channel_id dma_operation schedulable.
  ((internal_state2, channel_id, dma_operation), schedulable) = find_tx_rx_schedulable_endpoint environment internal_state1 channels number_of_queues
  ==>
  channel_id <=+ 91w
Proof
Induct THENL
[
 INTRO_TAC THEN
 PTAC bbb_usb_schedulerTheory.find_tx_rx_schedulable_endpoint THEN TRY (CONTR_NEG_ASM_TAC boolTheory.EQ_REFL) THEN EQ_PAIR_ASM_TAC THEN LRTAC THEN REWRITE_TAC [wordsTheory.WORD_0_LS]
 ,
 INTRO_TAC THEN
 PTAC bbb_usb_schedulerTheory.find_tx_rx_schedulable_endpoint THENL
 [
  EQ_PAIR_ASM_TAC THEN ASM_REWRITE_TAC [wordsTheory.WORD_0_LS]
  ,
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 3 THEN
  PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
  LRTAC THEN
  ETAC optionTheory.THE_DEF THEN
  LRTAC THEN
  IRTAC bbb_usb_rx_lemmasTheory.ENDPOINT_SCHEDULABLE_RX_IMPLIES_SOME_QUEUE_ID_LEQ_91_LEMMA THEN
  STAC
  ,
  ETAC arithmeticTheory.SUC_SUB1 THEN AIRTAC THEN STAC
  ,
  ETAC arithmeticTheory.SUC_SUB1 THEN AIRTAC THEN STAC
  ,
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 3 THEN
  PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
  LRTAC THEN
  ETAC optionTheory.THE_DEF THEN
  LRTAC THEN
  IRTAC bbb_usb_tx_lemmasTheory.ENDPOINT_SCHEDULABLE_TX_IMPLIES_SOME_QUEUE_ID_LEQ_91_LEMMA THEN
  STAC
  ,
  ETAC arithmeticTheory.SUC_SUB1 THEN AIRTAC THEN STAC
  ,
  ETAC arithmeticTheory.SUC_SUB1 THEN AIRTAC THEN STAC
 ]
]
QED

Theorem FIND_SCHEDULABLE_ENDPOINT_IMPLIES_CHANNEL_ID_LEQ_91_LEMMA:
!environment internal_state1 internal_state2 channels dma_operation channel_id schedulable.
  ((internal_state2, channel_id, dma_operation), schedulable) = find_schedulable_endpoint environment channels internal_state1
  ==>
  channel_id <=+ 91w
Proof
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.find_schedulable_endpoint THENL
[
 PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
 LRTAC THEN
 ETAC optionTheory.THE_DEF THEN
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 IRTAC bbb_usb_tx_lemmasTheory.IS_TX_WRITE_BACK_IMPLIES_CHANNEL_ID_LEQ_91_LEMMA THEN
 STAC
 ,
 PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
 LRTAC THEN
 ETAC optionTheory.THE_DEF THEN
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 IRTAC bbb_usb_rx_lemmasTheory.IS_RX_WRITE_BACK_IMPLIES_CHANNEL_ID_LEQ_91_LEMMA THEN
 STAC
 ,
 IRTAC FIND_TX_RX_SCHEDULABLE_ENDPOINT_IMPLIES_CHANNEL_ID_LEQ_91_LEMMA THEN STAC
]
QED

Theorem INCREMENT_SCHEDULER_PRESERVES_REGISTERS_HDP_LEMMA:
!internal_state1 internal_state2.
  internal_state2 = increment_scheduler internal_state1
  ==>
  internal_state2.qhp = internal_state1.qhp /\
  internal_state2.registers = internal_state1.registers
Proof
INTRO_TAC THEN PTAC bbb_usb_schedulerTheory.increment_scheduler THEN ALL_LRTAC THEN RECORD_TAC THEN STAC
QED

Theorem VALIDATE_QUEUE_ID_PRESERVES_REGISTERS_QHP_LEMMA:
!internal_state1 internal_state2 queue_id1 queue_id2.
  SOME (internal_state2, queue_id2) = validate_queue_id (SOME (internal_state1, queue_id1))
  ==>
  internal_state2.registers = internal_state1.registers /\
  internal_state2.qhp = internal_state1.qhp
Proof
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.validate_queue_id THEN TRY (HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE) THEN
ETAC optionTheory.SOME_11 THEN
EQ_PAIR_ASM_TAC THEN
STAC
QED

Theorem VALIDATE_QUEUE_ID_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA:
!internal_state1 internal_state2 queue_id1 queue_id2.
  SOME (internal_state2, queue_id2) = validate_queue_id (SOME (internal_state1, queue_id1))
  ==>
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.validate_queue_id THEN TRY (HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE) THEN
ETAC optionTheory.SOME_11 THEN
EQ_PAIR_ASM_TAC THEN
LRTAC THEN
REWRITE_TAC [bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ_REFL_LEMMA]
QED

Theorem ENDPOINT_SCHEDULABLE_TX_PRESERVES_REGISTERS_QHP_LEMMA:
!environment internal_state1 internal_state2 channels endpoint_id queue_id.
  SOME (internal_state2, queue_id) = endpoint_schedulable_tx environment internal_state1 channels endpoint_id
  ==>
  internal_state2.registers = internal_state1.registers /\
  internal_state2.qhp = internal_state1.qhp
Proof
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.endpoint_schedulable_tx THEN
REPEAT IF_SPLIT_TAC THENL
[
 LETS_TAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_PRESERVES_REGISTERS_QHP_LEMMA THEN NLRTAC 3 THEN RECORD_TAC THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_PRESERVES_REGISTERS_QHP_LEMMA THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_PRESERVES_REGISTERS_QHP_LEMMA THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_PRESERVES_REGISTERS_QHP_LEMMA THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_PRESERVES_REGISTERS_QHP_LEMMA THEN STAC
 ,
 LRTAC THEN PTAC bbb_usb_schedulerTheory.validate_queue_id THEN HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
]
QED

Theorem ENDPOINT_SCHEDULABLE_RX_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA:
!environment internal_state1 internal_state2 channels endpoint_id queue_id.
  SOME (internal_state2, queue_id) = endpoint_schedulable_rx environment internal_state1 channels endpoint_id
  ==>
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.endpoint_schedulable_rx THEN
REPEAT IF_SPLIT_TAC THENL
[
 LETS_TAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN ALL_LRTAC THEN RECORD_TAC THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 LRTAC THEN PTAC bbb_usb_schedulerTheory.validate_queue_id THEN HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
]
QED

Theorem ENDPOINT_SCHEDULABLE_TX_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA:
!environment internal_state1 internal_state2 channels endpoint_id queue_id.
  SOME (internal_state2, queue_id) = endpoint_schedulable_tx environment internal_state1 channels endpoint_id
  ==>
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.endpoint_schedulable_tx THEN
REPEAT IF_SPLIT_TAC THENL
[
 LETS_TAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN IRTAC bbb_usb_tx_lemmasTheory.NEW_QUEUE_ID_PRESERVES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN STAC
 ,
 LRTAC THEN PTAC bbb_usb_schedulerTheory.validate_queue_id THEN HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
]
QED

Theorem ENDPOINT_SCHEDULABLE_RX_PRESERVES_REGISTERS_QHP_LEMMA:
!environment internal_state1 internal_state2 channels endpoint_id queue_id.
  SOME (internal_state2, queue_id) = endpoint_schedulable_rx environment internal_state1 channels endpoint_id
  ==>
  internal_state2.registers = internal_state1.registers /\
  internal_state2.qhp = internal_state1.qhp
Proof
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.endpoint_schedulable_rx THEN
REPEAT IF_SPLIT_TAC THENL
[
 LETS_TAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_PRESERVES_REGISTERS_QHP_LEMMA THEN NLRTAC 3 THEN RECORD_TAC THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_PRESERVES_REGISTERS_QHP_LEMMA THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_PRESERVES_REGISTERS_QHP_LEMMA THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_PRESERVES_REGISTERS_QHP_LEMMA THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_PRESERVES_REGISTERS_QHP_LEMMA THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_PRESERVES_REGISTERS_QHP_LEMMA THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_PRESERVES_REGISTERS_QHP_LEMMA THEN STAC
 ,
 LRTAC THEN LRTAC THEN LRTAC THEN IRTAC VALIDATE_QUEUE_ID_PRESERVES_REGISTERS_QHP_LEMMA THEN STAC
 ,
 LRTAC THEN PTAC bbb_usb_schedulerTheory.validate_queue_id THEN HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
]
QED

Theorem FIND_TX_RX_SCHEDULABLE_ENDPOINT_PRESERVES_REGISTERS_QHP_LEMMA:
!number_of_queues environment internal_state1 channels internal_state2 channel_id dma_operation schedulable.
  ((internal_state2, channel_id, dma_operation), schedulable) = find_tx_rx_schedulable_endpoint environment internal_state1 channels number_of_queues
  ==>
  internal_state2.registers = internal_state1.registers /\
  internal_state2.qhp = internal_state1.qhp
Proof
Induct THENL
[
 INTRO_TAC THEN
 PTAC bbb_usb_schedulerTheory.find_tx_rx_schedulable_endpoint THEN TRY (CONTR_NEG_ASM_TAC boolTheory.EQ_REFL) THEN
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 INTRO_TAC THEN
 PTAC bbb_usb_schedulerTheory.find_tx_rx_schedulable_endpoint THENL
 [
  HYP_CONTR_NEQ_LEMMA_TAC numTheory.NOT_SUC
  ,
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 3 THEN
  PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
  LRTAC THEN
  ETAC optionTheory.THE_DEF THEN
  LRTAC THEN
  IRTAC ENDPOINT_SCHEDULABLE_RX_PRESERVES_REGISTERS_QHP_LEMMA THEN
  STAC
  ,
  ETAC arithmeticTheory.SUC_SUB1 THEN
  PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
  LRTAC THEN
  ETAC optionTheory.THE_DEF THEN
  LRTAC THEN
  IRTAC ENDPOINT_SCHEDULABLE_RX_PRESERVES_REGISTERS_QHP_LEMMA THEN
  IRTAC INCREMENT_SCHEDULER_PRESERVES_REGISTERS_HDP_LEMMA THEN
  AIRTAC THEN
  STAC
  ,
  ETAC arithmeticTheory.SUC_SUB1 THEN
  IRTAC INCREMENT_SCHEDULER_PRESERVES_REGISTERS_HDP_LEMMA THEN
  AIRTAC THEN
  STAC
  ,
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 3 THEN
  PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
  LRTAC THEN
  ETAC optionTheory.THE_DEF THEN
  LRTAC THEN
  IRTAC ENDPOINT_SCHEDULABLE_TX_PRESERVES_REGISTERS_QHP_LEMMA THEN
  STAC
  ,
  ETAC arithmeticTheory.SUC_SUB1 THEN
  PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
  LRTAC THEN
  ETAC optionTheory.THE_DEF THEN
  LRTAC THEN
  IRTAC ENDPOINT_SCHEDULABLE_TX_PRESERVES_REGISTERS_QHP_LEMMA THEN
  IRTAC INCREMENT_SCHEDULER_PRESERVES_REGISTERS_HDP_LEMMA THEN
  AIRTAC THEN
  STAC
  ,
  ETAC arithmeticTheory.SUC_SUB1 THEN
  IRTAC INCREMENT_SCHEDULER_PRESERVES_REGISTERS_HDP_LEMMA THEN
  AIRTAC THEN
  STAC
 ]
]
QED

Theorem FIND_TX_RX_SCHEDULABLE_ENDPOINT_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA:
!number_of_queues environment internal_state1 channels internal_state2 channel_id dma_operation schedulable.
  ((internal_state2, channel_id, dma_operation), schedulable) = find_tx_rx_schedulable_endpoint environment internal_state1 channels number_of_queues
  ==>
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
Induct THENL
[
 INTRO_TAC THEN
 PTAC bbb_usb_schedulerTheory.find_tx_rx_schedulable_endpoint THEN TRY (CONTR_NEG_ASM_TAC boolTheory.EQ_REFL) THEN
 EQ_PAIR_ASM_TAC THEN LRTAC THEN REWRITE_TAC [bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ_REFL_LEMMA]
 ,
 INTRO_TAC THEN
 PTAC bbb_usb_schedulerTheory.find_tx_rx_schedulable_endpoint THENL
 [
  HYP_CONTR_NEQ_LEMMA_TAC numTheory.NOT_SUC
  ,
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 3 THEN
  PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
  LRTAC THEN
  ETAC optionTheory.THE_DEF THEN
  LRTAC THEN
  IRTAC ENDPOINT_SCHEDULABLE_RX_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN
  STAC
  ,
  ETAC arithmeticTheory.SUC_SUB1 THEN
  PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
  LRTAC THEN
  ETAC optionTheory.THE_DEF THEN
  LRTAC THEN
  IRTAC ENDPOINT_SCHEDULABLE_RX_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN
  IRTAC bbb_usb_tx_lemmasTheory.INCREMENT_SCHEDULER_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN
  AIRTAC THEN
  FIRTAC bbb_usb_tx_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ_TRANS_LEMMA THEN
  FIRTAC bbb_usb_tx_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ_TRANS_LEMMA THEN
  STAC
  ,
  ETAC arithmeticTheory.SUC_SUB1 THEN
  IRTAC bbb_usb_tx_lemmasTheory.INCREMENT_SCHEDULER_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN
  AIRTAC THEN
  FIRTAC bbb_usb_tx_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ_TRANS_LEMMA THEN
  STAC
  ,
  EQ_PAIR_ASM_TAC THEN
  NLRTAC 3 THEN
  PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
  LRTAC THEN
  ETAC optionTheory.THE_DEF THEN
  LRTAC THEN
  FIRTAC ENDPOINT_SCHEDULABLE_TX_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN
  STAC
  ,
  ETAC arithmeticTheory.SUC_SUB1 THEN
  PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
  LRTAC THEN
  ETAC optionTheory.THE_DEF THEN
  LRTAC THEN
  IRTAC ENDPOINT_SCHEDULABLE_TX_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN
  IRTAC bbb_usb_tx_lemmasTheory.INCREMENT_SCHEDULER_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN
  AIRTAC THEN
  FIRTAC bbb_usb_tx_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ_TRANS_LEMMA THEN
  FIRTAC bbb_usb_tx_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ_TRANS_LEMMA THEN
  STAC
  ,
  ETAC arithmeticTheory.SUC_SUB1 THEN
  IRTAC bbb_usb_tx_lemmasTheory.INCREMENT_SCHEDULER_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN
  AIRTAC THEN
  FIRTAC bbb_usb_tx_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ_TRANS_LEMMA THEN
  STAC
 ]
]
QED

Theorem FIND_SCHEDULABLE_ENDPOINT_PRESERVES_REGISTERS_HDP_LEMMA:
!environment internal_state1 internal_state2 channels dma_operation channel_id schedulable.
  ((internal_state2, channel_id, dma_operation), schedulable) = find_schedulable_endpoint environment channels internal_state1
  ==>
  internal_state2.registers = internal_state1.registers /\
  internal_state2.qhp = internal_state1.qhp
Proof
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.find_schedulable_endpoint THENL
[
 PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
 LRTAC THEN
 ETAC optionTheory.THE_DEF THEN
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 IRTAC bbb_usb_tx_lemmasTheory.IS_TX_WRITE_BACK_PRESERVES_REGISTERS_QHP_LEMMA THEN
 STAC
 ,
 PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
 LRTAC THEN
 ETAC optionTheory.THE_DEF THEN
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 IRTAC bbb_usb_rx_lemmasTheory.IS_RX_WRITE_BACK_PRESERVES_REGISTERS_QHP_LEMMA THEN
 STAC
 ,
 IRTAC FIND_TX_RX_SCHEDULABLE_ENDPOINT_PRESERVES_REGISTERS_QHP_LEMMA THEN STAC
]
QED

Theorem FIND_SCHEDULABLE_ENDPOINT_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA:
!environment internal_state1 internal_state2 channels dma_operation channel_id schedulable.
  ((internal_state2, channel_id, dma_operation), schedulable) = find_schedulable_endpoint environment channels internal_state1
  ==>
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.find_schedulable_endpoint THENL
[
 PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
 LRTAC THEN
 ETAC optionTheory.THE_DEF THEN
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 IRTAC bbb_usb_tx_lemmasTheory.IS_TX_WRITE_BACK_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN
 STAC
 ,
 PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
 LRTAC THEN
 ETAC optionTheory.THE_DEF THEN
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 IRTAC bbb_usb_rx_lemmasTheory.IS_RX_WRITE_BACK_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN
 STAC
 ,
 IRTAC FIND_TX_RX_SCHEDULABLE_ENDPOINT_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN STAC
]
QED

Theorem BBB_USB_DMA_SCHEDULER_PRESERVES_REGISTERS_HDP_LEMMA:
!environment function_state internal_state1 internal_state2 channels channel_id dma_operation.
  (internal_state2, channel_id, dma_operation) = bbb_usb_dma_scheduler environment function_state internal_state1 channels
  ==>
  internal_state2.registers = internal_state1.registers /\
  internal_state2.qhp = internal_state1.qhp
Proof
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.bbb_usb_dma_scheduler THEN
MATCH_MP_TAC FIND_SCHEDULABLE_ENDPOINT_PRESERVES_REGISTERS_HDP_LEMMA THEN
PAXTAC THEN
LRTAC THEN
Q.EXISTS_TAC ‘SND (find_schedulable_endpoint environment q internal_state1)’ THEN
REWRITE_TAC [pairTheory.PAIR]
QED

Theorem BBB_USB_DMA_SCHEDULER_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA:
!environment function_state internal_state1 internal_state2 channels channel_id dma_operation.
  (internal_state2, channel_id, dma_operation) = bbb_usb_dma_scheduler environment function_state internal_state1 channels
  ==>
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
PTAC bbb_usb_schedulerTheory.bbb_usb_dma_scheduler THEN
MATCH_MP_TAC FIND_SCHEDULABLE_ENDPOINT_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN
PAXTAC THEN
LRTAC THEN
Q.EXISTS_TAC ‘SND (find_schedulable_endpoint environment q internal_state1)’ THEN
REWRITE_TAC [pairTheory.PAIR]
QED

Theorem QMEM_LRAM_EQ_QHP_EQ_ENDPOINTS_TX_SOP_LI_EQ_IMPLIES_BDS_TO_FETCH_EQ_LEMMA:
!internal_state1 internal_state2.
  QMEM_LRAM_EQ internal_state1.registers internal_state2.registers /\
  internal_state2.qhp = internal_state1.qhp /\
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
  ==>
  !channel_id memory.
    channel_id <=+ 91w
    ==>
    (THE (bbb_usb_verification channel_id)).bds_to_fetch memory internal_state2 =
    (THE (bbb_usb_verification channel_id)).bds_to_fetch memory internal_state1
Proof
INTRO_TAC THEN
INTRO_TAC THEN
REWRITE_TAC [bbb_usb_instantiationTheory.bbb_usb_verification] THEN
REPEAT IF_SPLIT_TAC THENL
[
 ETAC optionTheory.THE_DEF THEN
 ETAC bbb_usb_instantiationTheory.rx_verification THEN
 RECORD_TAC THEN
 IRTAC bbb_usb_rx_lemmasTheory.QMEM_LRAM_EQ_QHP_EQ_IMPLIES_RX_BDS_TO_FETCH_EQ_LEMMA THEN
 STAC
 ,
 ETAC optionTheory.THE_DEF THEN
 ETAC bbb_usb_instantiationTheory.tx_verification THEN
 RECORD_TAC THEN
 IRTAC bbb_usb_tx_lemmasTheory.QMEM_LRAM_EQ_QHP_ENDPOINTS_TX_SOP_LI_EQ_IMPLIES_TX_BDS_TO_FETCH_EQ_LEMMA THEN
 STAC
 ,
 ETAC boolTheory.DE_MORGAN_THM THEN
 ETAC wordsTheory.WORD_NOT_LOWER_EQUAL THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  IRTAC bbb_usb_lemmasTheory.NOT_BETWEEN_31_LEMMA THEN SOLVE_F_ASM_TAC
  ,
  IRTAC bbb_usb_lemmasTheory.NOT_BETWEEN_91_LEMMA THEN SOLVE_F_ASM_TAC
 ]
]
QED

Theorem BBB_USB_DMA_SCHEDULER_PRESERVES_BDS_TO_FETCH_LEMMA:
!environment function_state internal_state1 internal_state2 channels channel_id dma_operation.
  (internal_state2, channel_id, dma_operation) = bbb_usb_dma_scheduler environment function_state internal_state1 channels
  ==>
  !channel_id memory.
    channel_id <=+ 91w
    ==>
    (THE (bbb_usb_verification channel_id)).bds_to_fetch memory internal_state2 =
    (THE (bbb_usb_verification channel_id)).bds_to_fetch memory internal_state1
Proof
INTRO_TAC THEN
ITAC BBB_USB_DMA_SCHEDULER_PRESERVES_REGISTERS_HDP_LEMMA THEN
PAT_X_ASSUM “x = y” (fn thm => ASSUME_TAC (GSYM thm)) THEN
IRTAC BBB_USB_DMA_SCHEDULER_IMPLIES_ENDPOINTS_TX_SOP_LI_EQ_LEMMA THEN
IRTAC bbb_usb_lemmasTheory.REGISTERS_EQ_IMPLIES_QMEM_LRAM_EQ_LEMMA THEN
FIRTAC QMEM_LRAM_EQ_QHP_EQ_ENDPOINTS_TX_SOP_LI_EQ_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
STAC
QED

Theorem BBB_USB_DMA_SCHEDULER_PRESERVES_TX_FETCH_BD_ADDRESSES_LEMMA:
!environment function_state internal_state1 internal_state2 channels channel_id dma_operation.
  (internal_state2, channel_id, dma_operation) = bbb_usb_dma_scheduler environment function_state internal_state1 channels
  ==>
  !channel_id.
    tx_fetch_bd_addresses channel_id internal_state2 = tx_fetch_bd_addresses channel_id internal_state1
Proof
INTRO_TAC THEN
GEN_TAC THEN
REPEAT (PTAC bbb_usb_txTheory.tx_fetch_bd_addresses) THEN TRY STAC THEN IRTAC BBB_USB_DMA_SCHEDULER_PRESERVES_REGISTERS_HDP_LEMMA THENL
[
 LRTAC THEN CONTR_ASMS_TAC
 ,
 LRTAC THEN LRTAC THEN CONTR_ASMS_TAC
 ,
 STAC
]
QED

Theorem BBB_USB_DMA_SCHEDULER_PRESERVES_RX_FETCH_BD_ADDRESSES_LEMMA:
!environment function_state internal_state1 internal_state2 channels channel_id dma_operation.
  (internal_state2, channel_id, dma_operation) = bbb_usb_dma_scheduler environment function_state internal_state1 channels
  ==>
  !channel_id.
    rx_fetch_bd_addresses channel_id internal_state2 = rx_fetch_bd_addresses channel_id internal_state1
Proof
INTRO_TAC THEN
GEN_TAC THEN
REPEAT (PTAC bbb_usb_rxTheory.rx_fetch_bd_addresses) THEN TRY STAC THEN IRTAC BBB_USB_DMA_SCHEDULER_PRESERVES_REGISTERS_HDP_LEMMA THENL
[
 LRTAC THEN CONTR_ASMS_TAC
 ,
 LRTAC THEN LRTAC THEN CONTR_ASMS_TAC
 ,
 STAC
]
QED

Theorem BBB_USB_DMA_SCHEDULER_PRESERVES_FETCH_BD_ADDRESSES_LEMMA:
!environment function_state internal_state1 internal_state2 channels channel_id dma_operation.
  (internal_state2, channel_id, dma_operation) = bbb_usb_dma_scheduler environment function_state internal_state1 channels
  ==>
  !channel_id.
    channel_id <=+ 91w
    ==>
    (THE (bbb_usb_operation channel_id)).fetch_bd_addresses internal_state2 =
    (THE (bbb_usb_operation channel_id)).fetch_bd_addresses internal_state1
Proof
INTRO_TAC THEN
INTRO_TAC THEN
REWRITE_TAC [bbb_usb_instantiationTheory.bbb_usb_operation] THEN
IF_SPLIT_TAC THENL
[
 ETAC optionTheory.THE_DEF THEN
 ETAC bbb_usb_instantiationTheory.rx_operation THEN
 RECORD_TAC THEN
 IRTAC BBB_USB_DMA_SCHEDULER_PRESERVES_RX_FETCH_BD_ADDRESSES_LEMMA THEN
 STAC
 ,
 IF_SPLIT_TAC THENL 
 [
   ETAC optionTheory.THE_DEF THEN
   ETAC bbb_usb_instantiationTheory.tx_operation THEN
   RECORD_TAC THEN
   IRTAC BBB_USB_DMA_SCHEDULER_PRESERVES_TX_FETCH_BD_ADDRESSES_LEMMA THEN
   STAC
  ,
  ETAC boolTheory.DE_MORGAN_THM THEN
  ETAC wordsTheory.WORD_NOT_LOWER_EQUAL THEN
  SPLIT_ASM_DISJS_TAC THENL
  [
   IRTAC bbb_usb_lemmasTheory.NOT_BETWEEN_31_LEMMA THEN SOLVE_F_ASM_TAC
   ,
   IRTAC wordsTheory.WORD_LOWER_EQ_LOWER_TRANS THEN IRTAC wordsTheory.WORD_LOWER_REFL THEN SOLVE_F_ASM_TAC
  ]
 ]
]
QED

Theorem BBB_USB_DMA_SCHEDULER_PRESERVES_BD_TRANSFER_RAS_WAS_LEMMA:
!environment function_state internal_state1 internal_state2 channels channel_id dma_operation.
  (internal_state2, channel_id, dma_operation) = bbb_usb_dma_scheduler environment function_state internal_state1 channels
  ==>
  !channel_id.
    channel_id <=+ 91w
    ==>
    !bd.
      (THE (bbb_usb_verification channel_id)).bd_transfer_ras_was internal_state2 bd =
      (THE (bbb_usb_verification channel_id)).bd_transfer_ras_was internal_state1 bd
Proof
REWRITE_TAC [bbb_usb_instantiationTheory.bbb_usb_verification] THEN
INTRO_TAC THEN
INTRO_TAC THEN
GEN_TAC THEN
REWRITE_TAC [optionTheory.THE_DEF, bbb_usb_instantiationTheory.rx_verification, bbb_usb_instantiationTheory.tx_verification] THEN
REPEAT IF_SPLIT_TAC THEN RECORD_TAC THENL
[
 ETAC optionTheory.THE_DEF THEN
 RECORD_TAC THEN
 ONCE_REWRITE_TAC [bbb_usb_rx_lemmasTheory.RX_BD_TRANSFER_RAS_WAS_DEPENDS_ON_BD_LEMMA] THEN
 STAC
 ,
 ETAC optionTheory.THE_DEF THEN
 RECORD_TAC THEN
 ONCE_REWRITE_TAC [bbb_usb_tx_lemmasTheory.TX_BD_TRANSFER_RAS_WAS_DEPENDS_ON_BD_LEMMA] THEN
 STAC
 ,
 IRTAC bbb_usb_lemmasTheory.LEQ_91_NLEQ_31_NOT_GEQ_32_AND_LEQ_91_LEMMA THEN SOLVE_F_ASM_TAC
]
QED

Theorem BBB_USB_DMA_SCHEDULER_PRESERVES_SCRATCHPAD_ADDRESSES_LEMMA:
!environment function_state internal_state1 channels internal_state2 channel_id dma_operation.
  (internal_state2, channel_id, dma_operation) = bbb_usb_dma_scheduler environment function_state internal_state1 channels
  ==>
  bbb_usb_scratchpad_addresses internal_state2 = bbb_usb_scratchpad_addresses internal_state1
Proof
INTRO_TAC THEN
IRTAC BBB_USB_DMA_SCHEDULER_PRESERVES_REGISTERS_HDP_LEMMA THEN
MATCH_MP_TAC bbb_usb_lemmasTheory.LRAM_REGISTERS_PRESERVE_SCRATCHPAD_ADDRESSES_LEMMA THEN
STAC
QED

val _ = export_theory();

