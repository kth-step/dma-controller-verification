open HolKernel Parse boolLib bossLib helper_tactics;
open bbb_usb_stateTheory bbb_usb_registersTheory;

val _ = new_theory "bbb_usb_register_lemmas";

Theorem BBB_USB_PROCESS_REGISTER_RELATED_MEMORY_REPLY_PRESERVE_LRAM_REGISTERS_LEMMA:
!internal_state1 internal_state2 bytes tag.
  internal_state2 = bbb_usb_process_register_related_memory_reply internal_state1 bytes tag
  ==>
  internal_state2.registers = internal_state1.registers
Proof
INTRO_TAC THEN
PTAC bbb_usb_registersTheory.bbb_usb_process_register_related_memory_reply THEN
RLTAC THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem BBB_USB_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_REGISTERS_LEMMA:
!internal_state1 internal_state2 requests replies completed_replies.
  (internal_state2, completed_replies) = bbb_usb_process_register_related_memory_replies internal_state1 requests replies
  ==>
  internal_state2.registers = internal_state1.registers
Proof
INTRO_TAC THEN
PTAC bbb_usb_registersTheory.bbb_usb_process_register_related_memory_replies THEN TRY (EQ_PAIR_ASM_TAC THEN STAC) THEN
EQ_PAIR_ASM_TAC THEN
PTAC bbb_usb_registersTheory.bbb_usb_process_register_related_memory_reply THEN
RLTAC THEN LRTAC THEN RECORD_TAC THEN STAC
QED

Theorem BBB_USB_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_IMPLIES_QMEM_LRAM_EQ_QHP_EQ_ENDPOINTS_TX_SOP_LI_EQ_LEMMA:
!internal_state1 internal_state2 pending_requests replies processed_replies.
  (internal_state2, processed_replies) = bbb_usb_process_register_related_memory_replies internal_state1 pending_requests replies
  ==>
  QMEM_LRAM_EQ internal_state1.registers internal_state2.registers /\
  internal_state2.qhp = internal_state1.qhp /\
  ENDPOINTS_TX_SOP_LI_EQ internal_state1.endpoints_tx internal_state2.endpoints_tx
Proof
INTRO_TAC THEN
PTAC bbb_usb_registersTheory.bbb_usb_process_register_related_memory_replies THENL
[
 EQ_PAIR_ASM_TAC THEN
 ASM_REWRITE_TAC [bbb_usb_lemmasTheory.QMEM_LRAM_EQ_REFL_LEMMA, bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ_REFL_LEMMA]
 ,
 PTAC bbb_usb_registersTheory.bbb_usb_process_register_related_memory_reply THEN
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 LRTAC THEN
 RECORD_TAC THEN
 REWRITE_TAC [bbb_usb_lemmasTheory.QMEM_LRAM_EQ_REFL_LEMMA, bbb_usb_lemmasTheory.ENDPOINTS_TX_SOP_LI_EQ_REFL_LEMMA]
]
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_REGISTERS_QHP_ENDPOINTS_TX_TAC_LEMMA:
!internal_state1 internal_state2 requests replies processed_replies.
  (internal_state2, processed_replies) = bbb_usb_process_register_related_memory_replies internal_state1 requests replies
  ==>
  internal_state2.registers = internal_state1.registers /\
  (!channel_id. internal_state2.qhp channel_id = internal_state1.qhp channel_id) /\
  internal_state2.endpoints_tx = internal_state1.endpoints_tx
Proof
INTRO_TAC THEN PTAC bbb_usb_registersTheory.bbb_usb_process_register_related_memory_replies THEN TRY (EQ_PAIR_ASM_TAC THEN STAC) THEN
PTAC bbb_usb_registersTheory.bbb_usb_process_register_related_memory_reply THEN
EQ_PAIR_ASM_TAC THEN
RLTAC THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem REGISTERS_EQ_IMPLIES_SCRATCHPAD_ADDRESSES_EQ_LEMMA:
!internal_state1 internal_state2.
  internal_state2.registers = internal_state1.registers
  ==>
  bbb_usb_scratchpad_addresses internal_state2 = bbb_usb_scratchpad_addresses internal_state1
Proof
INTRO_TAC THEN
ETAC bbb_usb_registersTheory.bbb_usb_scratchpad_addresses THEN
STAC
QED

Theorem BBB_USB_READ_REGISTER_PRESERVES_INTERNAL_STATE_LEMMA:
!internal_state1 internal_state2 bytes memory_requests addresses.
  (internal_state2, bytes, memory_requests) = bbb_usb_read_register internal_state1 addresses
  ==>
  internal_state2 = internal_state1
Proof
INTRO_TAC THEN
ETAC bbb_usb_registersTheory.bbb_usb_read_register THEN
IF_SPLIT_TAC THEN1 (EQ_PAIR_ASM_TAC THEN STAC) THEN
LETS_TAC THEN
EQ_PAIR_ASM_TAC THEN
STAC
QED

Theorem BD_ADDRESS_TO_LI_ADDRESSES_ARE_SCRATCHPAD_ADDRESSES_LEMMA:
!internal_state bd_address scratchpad_addresses addresses.
  addresses = bd_address_to_li_addresses internal_state.registers bd_address /\
  scratchpad_addresses = bbb_usb_scratchpad_addresses internal_state
  ==>
  LIST1_IN_LIST2 addresses scratchpad_addresses
Proof
INTRO_TAC THEN
ETAC bbb_usb_registersTheory.bbb_usb_scratchpad_addresses THEN
PTAC bbb_usb_functionsTheory.linking_ram_addresses_approximate THEN
RLTAC THEN
LRTAC THEN
PTAC bbb_usb_functionsTheory.bd_address_to_li_addresses THEN
LRTAC THEN
PTAC bbb_usb_functionsTheory.bd_address_to_li_address THENL
[
 MATCH_MP_TAC lists_lemmasTheory.LIST1_IN_LIST2_IMPLIES_APPEND_LEMMA THEN
 PAT_X_ASSUM “linking_ram1_addresses = generate_consecutive_addresses linking_ram1_start linking_ram1_byte_size” (fn _ => ALL_TAC) THEN
 PAT_X_ASSUM “linking_ram1_byte_size = 2 * LRAM_TOTAL_NUMBER_OF_BDS * LRAM_BD_BYTE_SIZE” (fn _ => ALL_TAC) THEN
 PAT_X_ASSUM “linking_ram1_start = w2w internal_state.registers.LRAM1BASE @@ 0w” (fn _ => ALL_TAC) THEN
 MATCH_MP_TAC bbb_usb_lemmasTheory.GENERATE_SUBLIST_CONSECUTIVE_ADDRESSES_LEMMA THEN
 Q.EXISTS_TAC ‘((lr_bd_index : 30 word) @@ (0w : 2 word)) : 32 word’ THEN
 Q.EXISTS_TAC ‘((w2w internal_state.registers.LRAM0SIZE : 30 word) @@ (0w : 2 word)) : 32 word’ THEN
 Q.EXISTS_TAC ‘4’ THEN
 Q.EXISTS_TAC ‘li_address’ THEN
 Q.EXISTS_TAC ‘linking_ram0_start’ THEN
 REWRITE_TAC [DECIDE “0 < 4”] THEN
 CONJS_TAC THEN TRY STAC THENL
 [
  MATCH_MP_TAC bbb_usb_lemmasTheory.APPEND_2_ZEROS_PRESERVES_LT_LEMMA THEN STAC
  ,
  Cases_on ‘lr_bd_index = 0w’ THENL
  [
   LRTAC THEN
   ETAC (blastLib.BBLAST_PROVE “((0w : 30 word) @@ (0w : 2 word)) : 32 word = 0w”) THEN
   ETAC wordsTheory.word_0_n2w THEN
   ETAC (DECIDE “0 + 4 = 4”) THEN
   REPEAT (WEAKEN_TAC is_eq) THEN
   IRTAC (blastLib.BBLAST_PROVE “!(x : 30 word) y. x <+ y ==> x + 1w <=+ y”) THEN
   ETAC wordsTheory.WORD_ADD_0 THEN
   IRTAC bbb_usb_lemmasTheory.LEQ_IMPLIES_2BIT_EXTENSION_MULTIPLY_BY_4_LEQ_LEMMA THEN
   ETAC bbb_usb_lemmasTheory.W2W_30_W2W_32_EQ_W2W_32 THEN
   ETAC (blastLib.BBLAST_PROVE “(w2w (1w : 30 word) : 32 word) * 4w = 4w”) THEN
   ETAC bbb_usb_lemmasTheory.APPEND_2_ZEROS_EQ_MULTIPLY_BY_4_LEMMA THEN
   ETAC bbb_usb_lemmasTheory.W2W_30_W2W_32_EQ_W2W_32 THEN
   ETAC wordsTheory.WORD_LS THEN
   ETAC (blastLib.BBLAST_PROVE “w2n (4w : 32 word) = 4”) THEN
   STAC
   ,
   REPEAT (WEAKEN_TAC is_eq) THEN
   ITAC bbb_usb_lemmasTheory.LT_IMPLIES_APPEND_2_ZEROS_LEQ_4_LEMMA THEN
   IRTAC wordsTheory.word_sub_w2n THEN
   IRTAC bbb_usb_lemmasTheory.LT_IMPLIES_APPEND_2_ZEROS_MINUS_4_LEQ_LEMMA THEN
   ETAC wordsTheory.WORD_LS THEN
   LRTAC THEN
   ETAC arithmeticTheory.SUB_LEFT_LESS_EQ THEN
   ETAC (blastLib.BBLAST_PROVE “w2n (4w : 32 word) = 4”) THEN
   SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
   ETAC arithmeticTheory.LESS_EQ_0 THEN
   IRTAC (blastLib.BBLAST_PROVE “!x : 30 word. x <> 0w ==> 0w <+ (x @@ (0w : 2 word)) : 32 word”) THEN
   ETAC wordsTheory.WORD_LO THEN
   ETAC wordsTheory.word_0_n2w THEN
   LRTAC THEN
   IRTAC prim_recTheory.LESS_REFL THEN
   SOLVE_F_ASM_TAC
  ]
 ]
 ,
 MATCH_MP_TAC lists_lemmasTheory.LIST1_IN_LIST2_IMPLIES_PREPEND_LEMMA THEN
 PAT_X_ASSUM “linking_ram0_addresses = generate_consecutive_addresses linking_ram0_start linking_ram0_byte_size” (fn _ => ALL_TAC) THEN
 PAT_X_ASSUM “linking_ram0_byte_size = w2n (w2w internal_state.registers.LRAM0SIZE @@ 0w)” (fn _ => ALL_TAC) THEN
 PAT_X_ASSUM “linking_ram0_start = w2w internal_state.registers.LRAM0BASE @@ 0w” (fn _ => ALL_TAC) THEN
 MATCH_MP_TAC bbb_usb_lemmasTheory.GENERATE_SUBLIST_CONSECUTIVE_ADDRESSES_LEMMA THEN
 Q.EXISTS_TAC ‘((lr_bd_index : 30 word) @@ (0w : 2 word)) : 32 word’ THEN
 Q.EXISTS_TAC ‘n2w (2 * LRAM_TOTAL_NUMBER_OF_BDS * LRAM_BD_BYTE_SIZE)’ THEN
 Q.EXISTS_TAC ‘4’ THEN
 Q.EXISTS_TAC ‘li_address’ THEN
 Q.EXISTS_TAC ‘linking_ram1_start’ THEN
 REWRITE_TAC [DECIDE “0 < 4”] THEN
 CONJS_TAC THEN TRY STAC THENL
 [
  IRTAC bbb_usb_lemmasTheory.LR_BD_INDEX_LT_65535_PLUS_16383_LEMMA THEN
  IRTAC bbb_usb_lemmasTheory.LT_80000_IMPLIES_2BIT_EXTENSION_MULTIPLY_BY_4_LT_LEMMA THEN
  ETAC (EVAL “2 * LRAM_TOTAL_NUMBER_OF_BDS * LRAM_BD_BYTE_SIZE”) THEN
  ETAC (EVAL “4w * (0x10000w + 16384w) : 32 word”) THEN
  ASSUME_TAC (blastLib.BBLAST_PROVE “0x50000w <+ 0x80000w : 32 word”) THEN
  FIRTAC wordsTheory.WORD_LOWER_TRANS THEN
  STAC
  ,
  IRTAC bbb_usb_lemmasTheory.LR_BD_INDEX_LT_65535_PLUS_16383_LEMMA THEN
  IRTAC bbb_usb_lemmasTheory.LT_80000_IMPLIES_2BIT_EXTENSION_MULTIPLY_BY_4_LT_LEMMA THEN
  ETAC (EVAL “2 * LRAM_TOTAL_NUMBER_OF_BDS * LRAM_BD_BYTE_SIZE”) THEN
  ETAC (EVAL “4w * (0x10000w + 16384w) : 32 word”) THEN
  ETAC (EVAL “w2n (0x80000w : 32 word)”) THEN
  ETAC wordsTheory.WORD_LO THEN
  ETAC (EVAL “w2n (0x50000w : 32 word)”) THEN
  DECIDE_TAC
  ,
  ETAC (EVAL “2 * LRAM_TOTAL_NUMBER_OF_BDS * LRAM_BD_BYTE_SIZE”) THEN
  ETAC (EVAL “w2n (0x80000w : 32 word)”) THEN
  STAC
 ]
]
QED

Theorem BBB_USB_READ_REGISTER_IMPLIES_NO_MEMORY_REQUESTS_OR_READ_REQUEST_TO_LI_ADDRESSES_LEMMA:
!internal_state2 read_bytes requests internal_state1 register_addresses.
  (internal_state2, read_bytes, requests) = bbb_usb_read_register internal_state1 register_addresses
  ==>
  requests = [] \/
  ?addresses tag bd_address.
    requests = [request_read addresses tag] /\
    addresses = bd_address_to_li_addresses internal_state1.registers bd_address
Proof
INTRO_TAC THEN
PTAC bbb_usb_registersTheory.bbb_usb_read_register THEN EQ_PAIR_ASM_TAC THEN TRY STAC THEN
NRLTAC 3 THEN
REPEAT IF_SPLIT_TAC THENL
[
 PTAC bbb_usb_registersTheory.read_register_txgcr THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 PTAC bbb_usb_registersTheory.read_register_rxgcr THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 PTAC bbb_usb_registersTheory.read_registers_lram THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 PTAC bbb_usb_registersTheory.read_register_qmemctrl THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 PTAC bbb_usb_registersTheory.read_register_qmemrbase THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 PTAC bbb_usb_registersTheory.read_register_scheduler THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 PTAC bbb_usb_registersTheory.read_register_rxhpcra THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 PTAC bbb_usb_registersTheory.read_register_rxhpcrb THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 PTAC bbb_usb_registersTheory.read_register_d THEN EQ_PAIR_ASM_TAC THEN MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN PAXTAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem BD_ADDRESS_TO_LI_ADDRESSES_GENERATES_4_ADDRESSES_LEMMA:
!li_addresses registers pointer.
  li_addresses = bd_address_to_li_addresses registers pointer
  ==>
  LENGTH li_addresses = 4
Proof
INTRO_TAC THEN
PTAC bbb_usb_functionsTheory.bd_address_to_li_addresses THEN
RLTAC THEN
ASSUME_TAC (DECIDE “4 > 0”) THEN
IRTAC (INST_TYPE [alpha |-> “: 32”] bbb_usb_lemmasTheory.AT_LEAST_ONE_ELEMENT_IMPLIES_GENERATE_CONSECUTIVE_ADDRESSES_EQ_GENLIST_LEMMA) THEN
QLRTAC THEN
LRTAC THEN
REWRITE_TAC [listTheory.LENGTH_GENLIST]
QED

Theorem FORM_LI_BYTES_GENERATES_4_BYTES_LEMMA:
!li_bytes next_bd_mr next_bd_mr_index f b.
  li_bytes = form_li_bytes next_bd_mr next_bd_mr_index f b
  ==>
  LENGTH li_bytes = 4
Proof
INTRO_TAC THEN PTAC bbb_usb_functionsTheory.form_li_bytes THEN RLTAC THEN LRTAC THEN EVAL_TAC
QED

Theorem BBB_USB_WRITE_REGISTER_IMPLIES_NO_MEMORY_REQUESTS_OR_WRITE_REQUEST_TO_LI_ADDRESSES_LEMMA:
!internal_state2 requests internal_state1 register_address_bytes.
  (internal_state2, requests) = bbb_usb_write_register internal_state1 register_address_bytes
  ==>
  requests = [] \/
  ?address_bytes tag bd_address addresses.
    requests = [request_write address_bytes tag] /\
    addresses = bd_address_to_li_addresses internal_state1.registers bd_address /\
    MAP FST address_bytes = addresses
Proof
INTRO_TAC THEN
PTAC bbb_usb_registersTheory.bbb_usb_write_register THENL
[
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 PTAC bbb_usb_registersTheory.write_register_txgcr THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 PTAC bbb_usb_registersTheory.write_register_rxgcr THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 PTAC bbb_usb_registersTheory.write_registers_lram THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 PTAC bbb_usb_registersTheory.write_register_qmemctrl THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 PTAC bbb_usb_registersTheory.write_register_qmemrbase THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 PTAC bbb_usb_registersTheory.write_register_scheduler THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 PTAC bbb_usb_registersTheory.write_register_rxhpcra THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 PTAC bbb_usb_registersTheory.write_register_rxhpcrb THEN EQ_PAIR_ASM_TAC THEN STAC
 ,
 PTAC bbb_usb_registersTheory.write_register_d THEN EQ_PAIR_ASM_TAC THEN TRY STAC THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 NLRTAC 3 THEN
 EXISTS_EQ_TAC THEN
 PAXTAC THEN
 REPEAT (WEAKEN_TAC is_neg) THEN
 CONJS_TAC THEN TRY STAC THEN
 LRTAC THEN
 MATCH_MP_TAC ((GEN_ALL o (DISCH ((#1 o dest_imp o concl) listTheory.MAP_ZIP)) o CONJUNCT1 o UNDISCH) listTheory.MAP_ZIP) THEN
 IRTAC BD_ADDRESS_TO_LI_ADDRESSES_GENERATES_4_ADDRESSES_LEMMA THEN
 LRTAC THEN
 IRTAC FORM_LI_BYTES_GENERATES_4_BYTES_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

val _ = export_theory();
