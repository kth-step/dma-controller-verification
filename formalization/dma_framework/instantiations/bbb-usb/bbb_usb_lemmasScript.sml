open HolKernel Parse boolLib bossLib helper_tactics;
open bbb_usb_stateTheory;

val _ = new_theory "bbb_usb_lemmas";

Theorem LT_32_IMPLIES_LEQ_91_LEMMA:
!x : 8 word.
  x <+ 32w
  ==>
  x <=+ 91w
Proof
blastLib.BBLAST_TAC
QED

Theorem NOT_BETWEEN_31_LEMMA:
!x : 8 word.
  31w <+ x /\
  x <+ 32w
  ==>
  F
Proof
blastLib.BBLAST_TAC
QED

Theorem NOT_BETWEEN_91_LEMMA:
!x : 8 word.
  91w <+ x /\
  x <=+ 91w
  ==>
  F
Proof
blastLib.BBLAST_TAC
QED

Theorem NOT_LEQ_31_NOT_GEQ_32_IMPLIES_F_LEMMA:
!channel_id : 8 word.
  ~(channel_id <=+ 31w) /\
  ~(32w <=+ channel_id)
  ==>
  F
Proof
blastLib.BBLAST_TAC
QED

Theorem LEQ_91_NLEQ_31_NOT_GEQ_32_AND_LEQ_91_LEMMA:
!channel_id : 8 word.
  channel_id <=+ 91w /\
  ~(channel_id <=+ 31w) /\
  ~(32w <=+ channel_id /\ channel_id <=+ 91w)
  ==>
  F
Proof
GEN_TAC THEN
INTRO_TAC THEN
ETAC boolTheory.DE_MORGAN_THM THEN
SPLIT_ASM_DISJS_TAC THENL
[
 ETAC wordsTheory.WORD_NOT_LOWER_EQUAL THEN IRTAC NOT_BETWEEN_31_LEMMA THEN STAC
 ,
 ETAC wordsTheory.WORD_NOT_LOWER_EQUAL THEN IRTAC NOT_BETWEEN_91_LEMMA THEN STAC
]
QED

Definition QMEM_LRAM_EQ:
QMEM_LRAM_EQ registers1 registers2 = (
  registers1.QMEMCTRL = registers2.QMEMCTRL /\
  registers1.QMEMRBASE = registers2.QMEMRBASE /\
  registers1.LRAM0SIZE = registers2.LRAM0SIZE /\
  registers1.LRAM0BASE = registers2.LRAM0BASE /\
  registers1.LRAM1BASE = registers2.LRAM1BASE
)
End

Theorem QMEM_LRAM_EQ_PRESERVES_BBB_USB_SCRATCHPAD_ADDRESSES_LEMMA:
!internal_state1 internal_state2.
  QMEM_LRAM_EQ internal_state1.registers internal_state2.registers
  ==>
  bbb_usb_scratchpad_addresses internal_state2 = bbb_usb_scratchpad_addresses internal_state1
Proof
INTRO_TAC THEN
ETAC QMEM_LRAM_EQ THEN
ETAC bbb_usb_registersTheory.bbb_usb_scratchpad_addresses THEN
PTAC bbb_usb_functionsTheory.linking_ram_addresses_approximate THEN
PTAC bbb_usb_functionsTheory.linking_ram_addresses_approximate THEN
STAC
QED

Theorem QMEM_LRAM_EQ_IMPLIES_BD_MR_INFO_REC_EQ_LEMMA:
!r registers1 registers2 bd_address.
  QMEM_LRAM_EQ registers1 registers2
  ==>
  bd_mr_info_rec registers1 bd_address r = bd_mr_info_rec registers2 bd_address r
Proof
Induct THENL
[
 INTRO_TAC THEN
 PTAC bbb_usb_functionsTheory.bd_mr_info_rec THENL
 [
  PTAC bbb_usb_functionsTheory.bd_mr_info_rec THEN PTAC QMEM_LRAM_EQ THEN NLRTAC 2 THEN ALL_RLTAC THEN STAC
  ,
  PTAC bbb_usb_functionsTheory.bd_mr_info_rec THENL
  [
   PTAC QMEM_LRAM_EQ THEN NLRTAC 2 THEN ALL_RLTAC THEN STAC
   ,
   CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
  ]
  ,
  CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
 ]
 ,
 INTRO_TAC THEN
 ONCE_REWRITE_TAC [bbb_usb_functionsTheory.bd_mr_info_rec] THEN
 AITAC THEN
 PTAC QMEM_LRAM_EQ THEN
 NRLTAC 2 THEN
 LETS_TAC THEN
 IF_SPLIT_TAC THEN TRY STAC THEN
 IF_SPLIT_TAC THEN TRY STAC THEN
 REWRITE_TAC [arithmeticTheory.SUC_SUB1] THEN
 STAC
]
QED

Theorem QMEM_LRAM_EQ_IMPLIES_GET_BD_RAS_EQ_LEMMA:
!registers1 registers2 next_sop_bd_address.
  QMEM_LRAM_EQ registers1 registers2
  ==>
  get_bd_ras registers2 next_sop_bd_address = get_bd_ras registers1 next_sop_bd_address
Proof
INTRO_TAC THEN
ETAC bbb_usb_functionsTheory.get_bd_ras THEN
ETAC bbb_usb_functionsTheory.bd_address_to_li_addresses THEN
ETAC bbb_usb_functionsTheory.bd_address_to_li_address THEN
ETAC bbb_usb_functionsTheory.bd_mr_info THEN
ITAC QMEM_LRAM_EQ_IMPLIES_BD_MR_INFO_REC_EQ_LEMMA THEN
PTAC QMEM_LRAM_EQ THEN
ALL_LRTAC THEN
LETS_TAC THEN
ALL_LRTAC THEN
QRLTAC THEN
LRTAC THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 2 THEN
STAC
QED

Theorem QMEM_LRAM_EQ_IMPLIES_LI_TO_NEXT_BD_ADDRESS_EQ_LEMMA:
!registers1 registers2 li.
  QMEM_LRAM_EQ registers1 registers2
  ==>
  li_to_next_bd_address registers1 li = li_to_next_bd_address registers2 li
Proof
INTRO_TAC THEN
ETAC bbb_usb_functionsTheory.li_to_next_bd_address THEN
ETAC QMEM_LRAM_EQ THEN
STAC
QED

Theorem REGISTERS_EQ_IMPLIES_QMEM_LRAM_EQ_LEMMA:
!registers1 registers2.
  registers1 = registers2
  ==>
  QMEM_LRAM_EQ registers1 registers2
Proof
REWRITE_TAC [QMEM_LRAM_EQ] THEN
INTRO_TAC THEN
STAC
QED

Theorem LRAM_REGISTERS_PRESERVE_SCRATCHPAD_ADDRESSES_LEMMA:
!internal_state1 internal_state2.
  internal_state2.registers.LRAM0SIZE = internal_state1.registers.LRAM0SIZE /\
  internal_state2.registers.LRAM0BASE = internal_state1.registers.LRAM0BASE /\
  internal_state2.registers.LRAM1BASE = internal_state1.registers.LRAM1BASE
  ==>
  bbb_usb_scratchpad_addresses internal_state2 = bbb_usb_scratchpad_addresses internal_state1
Proof
INTRO_TAC THEN
ETAC bbb_usb_registersTheory.bbb_usb_scratchpad_addresses THEN
ETAC bbb_usb_functionsTheory.linking_ram_addresses_approximate THEN
NRLTAC 3 THEN
STAC
QED

Theorem QMEM_LRAM_EQ_REFL_LEMMA:
!registers.
  QMEM_LRAM_EQ registers registers
Proof
REWRITE_TAC [QMEM_LRAM_EQ]
QED

Theorem DISTINCT_CHANNEL_IDS_IMPLIES_DISTINCT_ENDPOINT_IDS_OR_OFFSETS_LEMMA:
!(channel_id : 8 word) channel_id' (endpoint_id : 5 word) endpoint_id' offset offset'.
  32w <=+ channel_id /\ channel_id <=+ 91w /\
  32w <=+ channel_id' /\ channel_id' <=+ 91w /\
  channel_id' <> channel_id /\
  endpoint_id = w2w ((channel_id - 32w) >>> 1) /\
  endpoint_id' = w2w ((channel_id' - 32w) >>> 1) /\
  offset = word_bit 0 channel_id /\
  offset' = word_bit 0 channel_id'
  ==>
  endpoint_id' <> endpoint_id \/
  endpoint_id' = endpoint_id /\ offset' <> offset
Proof
blastLib.BBLAST_TAC
QED

Definition MEMORY_EQ:
(MEMORY_EQ [] memory1 memory2 = T) /\
(MEMORY_EQ (address::addresses) memory1 memory2 = (
  (memory1 address = memory2 address) /\
  MEMORY_EQ addresses memory1 memory2)
)
End

Theorem MEM_MEMORY_EQ_EQ_MEMORY_EQ_LEMMA:
!addresses memory1 memory2.
  (!address. MEM address addresses ==> memory1 address = memory2 address) =
  MEMORY_EQ addresses memory1 memory2
Proof
Induct THEN (REWRITE_TAC [listTheory.MEM, MEMORY_EQ]) THEN
REPEAT GEN_TAC THEN
EQ_TAC THENL
[
 INTRO_TAC THEN
 CONJS_TAC THENL
 [
  PAT_X_ASSUM “!x. P ==> Q” (fn thm => ASSUME_TAC (REWRITE_RULE [] (Q.SPEC ‘h’ thm))) THEN STAC
  ,
  QRLTAC THEN
  INTRO_TAC THEN
  PAT_X_ASSUM “MEM a as” (fn thm1 =>
  PAT_X_ASSUM “!x. P ==> Q” (fn thm2 =>
    ASSUME_TAC (REWRITE_RULE [thm1] (Q.SPEC ‘address’ thm2)))) THEN
  STAC
 ]
 ,
 INTRO_TAC THEN
 INTRO_TAC THEN
 SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
 QRLTAC THEN
 AIRTAC THEN
 STAC
]
QED

Theorem MEMORY_EQ_IMPLIES_MAP_MEMORY_EQ_LEMMA:
!bd_ras memory1 memory2.
  MEMORY_EQ bd_ras memory1 memory2
  ==>
  MAP memory1 bd_ras = MAP memory2 bd_ras
Proof
Induct THEN TRY (REWRITE_TAC [listTheory.MAP]) THEN INTRO_TAC THEN ETAC listTheory.CONS_11 THEN ETAC MEMORY_EQ THEN AIRTAC THEN STAC
QED

Theorem MEMORY_EQ_APPEND_LEMMA:
!as1 as2 memory1 memory2.
  MEMORY_EQ (as1 ++ as2) memory1 memory2
  ==>
  MEMORY_EQ as1 memory1 memory2 /\
  MEMORY_EQ as2 memory1 memory2
Proof
Induct THEN TRY (REWRITE_TAC [MEMORY_EQ, listTheory.APPEND]) THEN INTRO_TAC THEN AIRTAC THEN STAC
QED

Theorem UPDATE_BD_PRESERVES_INTERNAL_STATE_LEMMA:
!internal_state1 internal_state2 bytes tag update_status bd_ras_was channel_id.
  channel_id <=+ 91w /\
  (internal_state2, bytes, tag, update_status) = (THE (bbb_usb_operation channel_id)).update_bd internal_state1 bd_ras_was
  ==>
  internal_state2 = internal_state1
Proof
INTRO_TAC THEN
ETAC bbb_usb_instantiationTheory.bbb_usb_operation THEN
REPEAT IF_SPLIT_TAC THENL
[
 ETAC optionTheory.THE_DEF THEN
 ETAC bbb_usb_instantiationTheory.rx_operation THEN
 RECORD_TAC THEN
 ETAC bbb_usb_rxTheory.rx_update_bd THEN
 EQ_PAIR_ASM_TAC THEN
 STAC
 ,
 ETAC optionTheory.THE_DEF THEN
 ETAC bbb_usb_instantiationTheory.tx_operation THEN
 RECORD_TAC THEN
 ETAC bbb_usb_txTheory.tx_update_bd THEN
 EQ_PAIR_ASM_TAC THEN
 STAC
 ,
 ETAC boolTheory.DE_MORGAN_THM THEN
 ETAC wordsTheory.WORD_NOT_LOWER_EQUAL THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  IRTAC NOT_BETWEEN_31_LEMMA THEN SOLVE_F_ASM_TAC
  ,
  IRTAC NOT_BETWEEN_91_LEMMA THEN SOLVE_F_ASM_TAC
 ]
]
QED

Theorem GT_ZERO_IMPLIES_SUC_ADD_PRE_LEMMA:
!x y.
  0 < y
  ==>
  x + y = SUC x + PRE y
Proof
INTRO_TAC THEN
IRTAC arithmeticTheory.PRE_SUC_EQ THEN
PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (SPEC “PRE y” thm)) THEN
ETAC boolTheory.REFL_CLAUSE THEN
ETAC boolTheory.EQ_CLAUSES THEN
RLTAC THEN
ETAC prim_recTheory.PRE THEN
ETAC arithmeticTheory.ADD_CLAUSES THEN
STAC
QED

Theorem GT_IMPLIES_GT_ZERO_LEMMA:
!x y.
  x < y
  ==>
  0 < y
Proof
INTRO_TAC THEN
CCONTR_TAC THEN
ETAC arithmeticTheory.NOT_LESS THEN
IRTAC arithmeticTheory.LESS_LESS_EQ_TRANS THEN
IRTAC prim_recTheory.NOT_LESS_0 THEN
STAC
QED

Theorem SUC_LT_IMPLIES_LT_PRE_LEMMA:
!x y.
  SUC x < y
  ==>
  x < PRE y
Proof
INTRO_TAC THEN
ASSUME_TAC (SPEC “x : num” prim_recTheory.LESS_0) THEN
IRTAC arithmeticTheory.INV_PRE_LESS THEN
PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (SPEC “y : num” thm)) THEN
ETAC prim_recTheory.PRE THEN
STAC
QED

Theorem LT_LEQ_IMPLIES_LT_LEMMA:
!w x y z.
  w < y /\
  x + y <= z : num
  ==>
  x + w < z
Proof
Induct THENL
[
 INTRO_TAC THEN DECIDE_TAC
 ,
 INTRO_TAC THEN
 REWRITE_TAC [arithmeticTheory.ADD_CLAUSES] THEN
 REWRITE_TAC [(GSYM o List.nth) (CONJUNCTS arithmeticTheory.ADD_CLAUSES, 2)] THEN
 ITAC GT_IMPLIES_GT_ZERO_LEMMA THEN
 IRTAC GT_ZERO_IMPLIES_SUC_ADD_PRE_LEMMA THEN
 PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (SPEC “x : num” thm)) THEN
 LRTAC THEN
 IRTAC SUC_LT_IMPLIES_LT_PRE_LEMMA THEN
 AIRTAC THEN
 STAC
]
QED

Theorem ADD_COMP_SUC_EQ_ADD_LEMMA:
!start_address.
  (\n. start_address + n2w n) o SUC = (\n. start_address + 1w + n2w n)
Proof
GEN_TAC THEN
ETAC boolTheory.FUN_EQ_THM THEN
GEN_TAC THEN
ETAC combinTheory.o_THM THEN
APP_SCALAR_TAC THEN
ETAC wordsTheory.n2w_SUC THEN
ONCE_REWRITE_TAC [SPECL [“n2w x : 'a word”, “1w : 'a word”] wordsTheory.WORD_ADD_COMM] THEN
REWRITE_TAC [wordsTheory.WORD_ADD_ASSOC]
QED

Theorem AT_LEAST_TWO_ELEMENTS_GENERATE_CONSECUTIVE_ADDRESSES_EQ_LEMMA:
!start_address number_of_bytes_to_read addresses.
  number_of_bytes_to_read > 0 /\
  addresses = generate_consecutive_addresses (start_address) (SUC number_of_bytes_to_read)
  ==>
  addresses = start_address::(generate_consecutive_addresses (start_address + 1w) number_of_bytes_to_read)
Proof
INTRO_TAC THEN
RW_HYPS_TAC bbb_usb_functionsTheory.generate_consecutive_addresses THEN
LEMMA_TAC bbb_usb_functionsTheory.generate_consecutive_addresses_rec THEN
IF_SPLIT_TAC THENL
[
 ETAC arithmeticTheory.SUC_SUB1 THEN
 LRTAC THEN
 ETAC arithmeticTheory.GREATER_DEF THEN
 IRTAC prim_recTheory.LESS_REFL THEN
 SOLVE_F_ASM_TAC
 ,
 ETAC bbb_usb_functionsTheory.generate_consecutive_addresses THEN
 ETAC arithmeticTheory.SUC_SUB1 THEN
 STAC
]
QED

Theorem AT_LEAST_ONE_ELEMENT_IMPLIES_GENERATE_CONSECUTIVE_ADDRESSES_EQ_GENLIST_LEMMA:
!number_of_bytes_to_read (start_address : 'a word).
  number_of_bytes_to_read > 0
  ==>
  generate_consecutive_addresses start_address number_of_bytes_to_read =
  GENLIST (\n. start_address + n2w n) number_of_bytes_to_read
Proof
Induct THENL
[
 REWRITE_TAC [arithmeticTheory.GREATER_DEF] THEN INTRO_TAC THEN IRTAC prim_recTheory.LESS_REFL THEN SOLVE_F_ASM_TAC
 ,
 INTRO_TAC THEN
 Cases_on ‘number_of_bytes_to_read > 0’ THENL
 [
  AITAC THEN
  PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (SPEC “start_address + 1w : 'a word” thm)) THEN
  IRTAC AT_LEAST_TWO_ELEMENTS_GENERATE_CONSECUTIVE_ADDRESSES_EQ_LEMMA THEN
  LRTAC THEN
  ETAC listTheory.GENLIST_CONS THEN
  APP_SCALAR_TAC THEN
  ETAC wordsTheory.WORD_ADD_0 THEN
  ETAC ADD_COMP_SUC_EQ_ADD_LEMMA THEN
  RLTAC THEN
  STAC
  ,
  WEAKEN_TAC is_forall THEN
  ETAC arithmeticTheory.NOT_GREATER THEN
  ETAC arithmeticTheory.LESS_EQ_0 THEN
  LRTAC THEN
  ETAC bbb_usb_functionsTheory.generate_consecutive_addresses THEN
  ETAC listTheory.GENLIST THEN
  APP_SCALAR_TAC THEN
  ETAC wordsTheory.WORD_ADD_0 THEN
  ETAC listTheory.SNOC THEN
  ETAC arithmeticTheory.SUC_SUB1 THEN
  ONCE_REWRITE_TAC [bbb_usb_functionsTheory.generate_consecutive_addresses_rec] THEN
  STAC
 ]
]
QED

Theorem READ_LT_SIZE_IMPLIES_REQUEST_SIZE_GT_ZERO_LEMMA:
!number_of_read_bytes buffer_size request_size.
  number_of_read_bytes <+ buffer_size /\
  request_size = get_request_size number_of_read_bytes buffer_size
  ==>
  request_size > 0
Proof
INTRO_TAC THEN
ETAC bbb_usb_txTheory.get_request_size THEN
IF_SPLIT_TAC THEN TRY DECIDE_TAC THEN
LRTAC THEN
ETAC arithmeticTheory.NOT_LESS_EQUAL THEN
ETAC wordsTheory.WORD_LO THEN
DECIDE_TAC
QED

Theorem WORD_GT_IMPLIES_GT_ZERO_LEMMA:
!number_of_read_bytes buffer_size.
  number_of_read_bytes <+ buffer_size
  ==>
  w2n buffer_size > 0
Proof
INTRO_TAC THEN
ETAC wordsTheory.WORD_LO THEN
DECIDE_TAC
QED

Theorem READ_ADDRESSES_IN_BUFFER_ADDRESSES_N_LEMMA:
!number_of_read_bytes buffer_size request_size start_address buffer_start_address buffer_read_addresses read_addresses.
  number_of_read_bytes <+ buffer_size /\
  request_size = get_request_size number_of_read_bytes buffer_size /\
  start_address = buffer_start_address + number_of_read_bytes /\
  buffer_read_addresses = generate_consecutive_addresses buffer_start_address (w2n buffer_size) /\
         read_addresses = generate_consecutive_addresses start_address request_size
  ==>
  LIST1_IN_LIST2 read_addresses buffer_read_addresses
Proof
INTRO_TAC THEN
ITAC ((GEN_ALL o #1 o EQ_IMP_RULE o SPEC_ALL) wordsTheory.WORD_LO) THEN
ITAC WORD_GT_IMPLIES_GT_ZERO_LEMMA THEN
ASSUME_TAC (SPECL [“w2n (buffer_size : 'a word)”, “buffer_start_address : 'a word”] AT_LEAST_ONE_ELEMENT_IMPLIES_GENERATE_CONSECUTIVE_ADDRESSES_EQ_GENLIST_LEMMA) THEN
AIRTAC THEN
LRTAC THEN
LRTAC THEN
ITAC READ_LT_SIZE_IMPLIES_REQUEST_SIZE_GT_ZERO_LEMMA THEN
ASSUME_TAC (SPECL [“(request_size : num)”, “start_address : 'a word”] AT_LEAST_ONE_ELEMENT_IMPLIES_GENERATE_CONSECUTIVE_ADDRESSES_EQ_GENLIST_LEMMA) THEN
AIRTAC THEN
LRTAC THEN
LRTAC THEN
ETAC listsTheory.LIST1_IN_LIST2 THEN
ETAC listTheory.EVERY_MEM THEN
APP_SCALAR_TAC THEN
INTRO_TAC THEN
ETAC listTheory.MEM_GENLIST THEN
AXTAC THEN
APP_SCALAR_TAC THEN
LRTAC THEN
LRTAC THEN
LRTAC THEN
Q.EXISTS_TAC ‘w2n number_of_read_bytes + m’ THEN
ETAC wordsTheory.word_add_n2w THEN
ETAC wordsTheory.n2w_w2n THEN
ETAC wordsTheory.WORD_ADD_ASSOC THEN
REWRITE_TAC [] THEN
ETAC wordsTheory.WORD_LO THEN
ETAC bbb_usb_txTheory.get_request_size THEN
IF_SPLIT_TAC THENL
[
 IRTAC LT_LEQ_IMPLIES_LT_LEMMA THEN STAC
 ,
 IRTAC arithmeticTheory.LESS_SUB_ADD_LESS THEN ONCE_REWRITE_TAC [arithmeticTheory.ADD_SYM] THEN STAC
]
QED

Theorem GENERATE_N_CONSECUTIVE_ADDRESSES_IMPLIES_LENGTH_EQ_N_LEMMA:
!n a as.
  n > 0 /\
  as = generate_consecutive_addresses a n
  ==>
  LENGTH as = n
Proof
INTRO_TAC THEN
ASSUME_TAC (SPECL [“n : num”, “a : 'a word”] AT_LEAST_ONE_ELEMENT_IMPLIES_GENERATE_CONSECUTIVE_ADDRESSES_EQ_GENLIST_LEMMA) THEN
AIRTAC THEN
LRTAC THEN
LRTAC THEN
REWRITE_TAC [listTheory.LENGTH_GENLIST]
QED

Theorem NUMBER_OF_BYTES_TO_WRITE_LEQ_USB_PACKET_LENGTH_LEMMA:
!number_of_bytes_to_write buffer_size offset usb_packet_length.
  number_of_bytes_to_write = get_number_of_bytes_to_write buffer_size offset usb_packet_length
  ==>
  number_of_bytes_to_write <= usb_packet_length
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.get_number_of_bytes_to_write THENL
[
 LRTAC THEN REWRITE_TAC [arithmeticTheory.ZERO_LESS_EQ]
 ,
 LRTAC THEN ETAC arithmeticTheory.GREATER_EQ THEN STAC
 ,
 LRTAC THEN ETAC arithmeticTheory.GREATER_EQ THEN STAC
 ,
 ETAC arithmeticTheory.LESS_OR_EQ THEN STAC
]
QED

Theorem LENGTH_WRITE_ADDRESSES_EQ_LENGTH_BYTES_TO_WRITE_LEMMA:
!number_of_bytes_to_write write_addresses start_address bytes_to_write usb_packet buffer_size offset.
  number_of_bytes_to_write = get_number_of_bytes_to_write buffer_size offset (LENGTH usb_packet) /\
  number_of_bytes_to_write <> 0 /\
  write_addresses = generate_consecutive_addresses start_address number_of_bytes_to_write /\
  bytes_to_write = TAKE number_of_bytes_to_write usb_packet
  ==>
  LENGTH write_addresses = LENGTH bytes_to_write
Proof
INTRO_TAC THEN
ETAC arithmeticTheory.NOT_ZERO_LT_ZERO THEN
ETAC arithmeticTheory.GREATER_DEF THEN
IRTAC GENERATE_N_CONSECUTIVE_ADDRESSES_IMPLIES_LENGTH_EQ_N_LEMMA THEN
LRTAC THEN
IRTAC NUMBER_OF_BYTES_TO_WRITE_LEQ_USB_PACKET_LENGTH_LEMMA THEN
ITAC listTheory.LENGTH_TAKE THEN
STAC
QED

Theorem GENERATE_SUBLIST_CONSECUTIVE_ADDRESSES_LEMMA:
!offset buffer_size request_size start_address buffer_start_address buffer_addresses request_addresses.
  offset <+ buffer_size /\
  0 < request_size /\
  w2n offset + request_size <= w2n buffer_size /\
  start_address = buffer_start_address + offset /\
  buffer_addresses = generate_consecutive_addresses buffer_start_address (w2n buffer_size) /\
  request_addresses = generate_consecutive_addresses start_address request_size
  ==>
  LIST1_IN_LIST2 request_addresses buffer_addresses
Proof
INTRO_TAC THEN
ITAC ((GEN_ALL o #1 o EQ_IMP_RULE o SPEC_ALL) wordsTheory.WORD_LO) THEN
ITAC WORD_GT_IMPLIES_GT_ZERO_LEMMA THEN
ASSUME_TAC (SPECL [“w2n (buffer_size : 'a word)”, “buffer_start_address : 'a word”] AT_LEAST_ONE_ELEMENT_IMPLIES_GENERATE_CONSECUTIVE_ADDRESSES_EQ_GENLIST_LEMMA) THEN
AIRTAC THEN
LRTAC THEN
LRTAC THEN
PAT_X_ASSUM “0 < request_size” (fn thm => ASSUME_TAC (REWRITE_RULE [wordsTheory.WORD_LO, wordsTheory.word_0_n2w] thm)) THEN
ETAC arithmeticTheory.GREATER_DEF THEN
ASSUME_TAC (SPECL [“request_size : num”, “start_address : 'a word”] AT_LEAST_ONE_ELEMENT_IMPLIES_GENERATE_CONSECUTIVE_ADDRESSES_EQ_GENLIST_LEMMA) THEN
AIRTAC THEN
LRTAC THEN
LRTAC THEN
ETAC listsTheory.LIST1_IN_LIST2 THEN
ETAC listTheory.EVERY_MEM THEN
APP_SCALAR_TAC THEN
INTRO_TAC THEN
ETAC listTheory.MEM_GENLIST THEN
AXTAC THEN
APP_SCALAR_TAC THEN
LRTAC THEN
LRTAC THEN
Q.EXISTS_TAC ‘w2n offset + m’ THEN
ETAC wordsTheory.word_add_n2w THEN
ETAC wordsTheory.n2w_w2n THEN
ETAC wordsTheory.WORD_ADD_ASSOC THEN
REWRITE_TAC [] THEN
DECIDE_TAC
QED

Theorem NUMBER_OF_BYTES_TO_WRITE_IMPLIES_OFFSET_LT_BUFFER_SIZE_AND_OFFSET_PLUS_REQUEST_SIZE_LEQ_BUFFER_SIZE_LEMMA:
!request_size buffer_size offset usb_packet_length.
  request_size = get_number_of_bytes_to_write (w2n buffer_size) (w2n offset) usb_packet_length /\
  request_size > 0
  ==>
  offset <+ buffer_size /\
  w2n offset + request_size <= w2n buffer_size
Proof
INTRO_TAC THEN
PTAC bbb_usb_rxTheory.get_number_of_bytes_to_write THENL
[
 DECIDE_TAC
 ,
 LRTAC THEN
 ETAC arithmeticTheory.NOT_GREATER_EQ THEN
 ETAC arithmeticTheory.LESS_EQ THEN
 ETAC wordsTheory.WORD_LO THEN
 STAC
 ,
 LRTAC THEN
 ETAC arithmeticTheory.NOT_GREATER_EQ THEN
 ETAC arithmeticTheory.LESS_EQ THEN
 ETAC wordsTheory.WORD_LO THEN
 ASM_REWRITE_TAC [] THEN
 ETAC arithmeticTheory.GREATER_DEF THEN
 PAT_X_ASSUM “x < y : num” (fn thm => ASSUME_TAC (ONCE_REWRITE_RULE [GSYM arithmeticTheory.SUB_LESS_0] thm)) THEN
 IRTAC arithmeticTheory.LESS_IMP_LESS_OR_EQ THEN
 IRTAC arithmeticTheory.LESS_EQ_ADD_SUB THEN
 QRLTAC THEN
 DECIDE_TAC
 ,
 RLTAC THEN
 ETAC arithmeticTheory.NOT_GREATER_EQ THEN
 ETAC arithmeticTheory.LESS_EQ THEN
 ETAC wordsTheory.WORD_LO THEN
 ASM_REWRITE_TAC [] THEN
 WEAKEN_TAC is_neg THEN
 PAT_X_ASSUM “x > 0” (fn _ => ALL_TAC) THEN
 DECIDE_TAC
]
QED

Theorem GEQ_AND_LT_SUB_IMPLIES_LT_ADD_LEMMA:
!x y (z : 32 word).
  y >=+ z /\
  x <+ y - z
  ==>
  z + x <+ y
Proof
blastLib.BBLAST_TAC
QED

Theorem MEM_WORD32ALIGNED_ADDRESSES_IMPLIES_MEM_ADDRESSES_LEMMA:
!address addresses n.
  MEM address (word32aligned addresses n)
  ==>
  MEM address addresses
Proof
INTRO_TAC THEN
PTAC bbb_usb_functionsTheory.word32aligned THEN
IRTAC rich_listTheory.MEM_TAKE THEN
IRTAC rich_listTheory.MEM_DROP_IMP THEN
STAC
QED

Theorem MEM_MAP_FST_MERGE_LISTS_LEMMA:
!addresses address bytes.
  MEM address (MAP FST (merge_lists (addresses, bytes)))
  ==>
  MEM address addresses
Proof
Induct THENL
[
 INTRO_TAC THEN ETAC bbb_usb_functionsTheory.merge_lists THEN ETAC listTheory.MAP THEN STAC
 ,
 INTRO_TAC THEN
 PTAC bbb_usb_functionsTheory.merge_lists THEN1 (ETAC listTheory.MAP THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC) THEN
 ETAC listTheory.MAP THEN
 ETAC pairTheory.FST THEN
 ETAC listTheory.MEM THEN
 SPLIT_ASM_DISJS_TAC THEN1 STAC THEN
 AIRTAC THEN
 STAC
]
QED

Theorem MEM_MAP_FST_MERGE_LISTS_WORD32ALIGNED_LEMMA:
!address_bytes bd_was n bytes address.
  address_bytes = merge_lists (word32aligned bd_was n, bytes) /\
  MEM address (MAP FST address_bytes)
  ==>
  MEM address bd_was
Proof
INTRO_TAC THEN
LRTAC THEN
IRTAC MEM_MAP_FST_MERGE_LISTS_LEMMA THEN
IRTAC MEM_WORD32ALIGNED_ADDRESSES_IMPLIES_MEM_ADDRESSES_LEMMA THEN
STAC
QED

Theorem SOME_OPTION_MAP_INDEX_FIND_IS_MEM_LEMMA:
!l n e P.
  SOME e = (OPTION_MAP SND o INDEX_FIND n P) l
  ==>
  MEM e l
Proof
Induct THENL
[
 INTRO_TAC THEN
 ETAC combinTheory.o_THM THEN
 ETAC listTheory.INDEX_FIND_def THEN
 ETAC optionTheory.OPTION_MAP_DEF THEN
 IRTAC optionTheory.NOT_SOME_NONE THEN
 SOLVE_F_ASM_TAC
 ,
 INTRO_TAC THEN
 ETAC combinTheory.o_THM THEN
 ETAC listTheory.INDEX_FIND_def THEN
 IF_SPLIT_TAC THENL
 [
  ETAC optionTheory.OPTION_MAP_DEF THEN
  ETAC pairTheory.SND THEN
  ETAC optionTheory.SOME_11 THEN
  LRTAC THEN
  ETAC listTheory.MEM THEN
  STAC
  ,
  PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (REWRITE_RULE [combinTheory.o_THM] thm)) THEN
  AIRTAC THEN
  ETAC listTheory.MEM THEN
  STAC
 ]
]
QED

Theorem FIND_SOME_IS_MEMBER_LEMMA:
!e P l.
  SOME e = FIND P l
  ==>
  MEM e l
Proof
INTRO_TAC THEN
ETAC listTheory.FIND_def THEN
IRTAC SOME_OPTION_MAP_INDEX_FIND_IS_MEM_LEMMA THEN
STAC
QED

Theorem MEM_PACKET_BDS_IMPLIES_MEM_BDS_TO_WRITE_BACK_LEMMA:
!bds_to_write_back packet_bds remaining_bds bd.
  (packet_bds, remaining_bds) = get_dma_packet_bds bds_to_write_back /\
  MEM bd packet_bds
  ==>
  MEM bd bds_to_write_back
Proof
Induct THEN1 (INTRO_TAC THEN ETAC bbb_usb_functionsTheory.get_dma_packet_bds THEN EQ_PAIR_ASM_TAC THEN STAC) THEN
INTRO_TAC THEN
PTAC bbb_usb_functionsTheory.get_dma_packet_bds THENL
[
 EQ_PAIR_ASM_TAC THEN LRTAC THEN ETAC listTheory.MEM THEN REMOVE_F_DISJUNCTS_TAC THEN LRTAC THEN ALL_RLTAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 LRTAC THEN
 LRTAC THEN
 ETAC listTheory.MEM THEN
 SPLIT_ASM_DISJS_TAC THEN1 (LRTAC THEN ALL_RLTAC THEN STAC) THEN
 REPEAT (WEAKEN_TAC is_eq) THEN
 WEAKEN_TAC is_neg THEN
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 INST_IMP_ASM_GOAL_TAC THEN
 EXISTS_EQ_TAC THEN
 STAC
]
QED

Theorem MEM_REMAINING_BDS_IMPLIES_MEM_BDS_TO_WRITE_BACK_LEMMA:
!bds_to_write_back packet_bds remaining_bds bd.
  (packet_bds, remaining_bds) = get_dma_packet_bds bds_to_write_back /\
  MEM bd remaining_bds
  ==>
  MEM bd bds_to_write_back
Proof
Induct THEN1 (INTRO_TAC THEN ETAC bbb_usb_functionsTheory.get_dma_packet_bds THEN EQ_PAIR_ASM_TAC THEN STAC) THEN
INTRO_TAC THEN
PTAC bbb_usb_functionsTheory.get_dma_packet_bds THENL
[
 EQ_PAIR_ASM_TAC THEN WEAKEN_TAC is_eq THEN LRTAC THEN ETAC listTheory.MEM THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN AIRTAC THEN ETAC listTheory.MEM THEN STAC
]
QED

Theorem MEM_PACKET_BD_IMPLIES_MEM_BDS_TO_WRITE_BACK_LEMMA:
!packets_bds bds_to_write_back bd bds.
  packets_bds = get_dma_packets_bds bds_to_write_back /\
  MEM bds packets_bds /\
  MEM bd bds
  ==>
  MEM bd bds_to_write_back
Proof
Induct THEN1 (REWRITE_TAC [listTheory.MEM]) THEN
INTRO_TAC THEN
PTAC bbb_usb_functionsTheory.get_dma_packets_bds THEN1 (IRTAC listTheory.NOT_CONS_NIL THEN SOLVE_F_ASM_TAC) THEN
RLTAC THEN
ETAC listTheory.MEM THEN
SPLIT_ASM_DISJS_TAC THENL
[
 RLTAC THEN ETAC listTheory.CONS_11 THEN IRTAC MEM_PACKET_BDS_IMPLIES_MEM_BDS_TO_WRITE_BACK_LEMMA THEN STAC
 ,
 ETAC listTheory.CONS_11 THEN
 MATCH_MP_TAC MEM_REMAINING_BDS_IMPLIES_MEM_BDS_TO_WRITE_BACK_LEMMA THEN
 PAXTAC THEN
 ASM_REWRITE_TAC [] THEN
 INST_IMP_ASM_GOAL_TAC THEN
 STAC
]
QED

Theorem MEM_DMA_PACKET_BDS_TO_RELEASE_IMPLIES_MEM_BDS_TO_WRITE_BACK_LEMMA:
!packet_bds internal_state endpoint bds_to_write_back bd.
  SOME packet_bds = get_dma_packet_bds_to_release internal_state endpoint bds_to_write_back /\
  MEM bd packet_bds
  ==>
  MEM bd bds_to_write_back
Proof
INTRO_TAC THEN
PTAC bbb_usb_functionsTheory.get_dma_packet_bds_to_release THEN TRY (IRTAC optionTheory.NOT_SOME_NONE THEN SOLVE_F_ASM_TAC) THENL
[
 ETAC optionTheory.SOME_11 THEN
 IRTAC lists_lemmasTheory.NOT_NULL_IMPLIES_EXISTING_HD_TL_LEMMA THEN
 AXTAC THEN
 LRTAC THEN
 IRTAC lists_lemmasTheory.LAST_IS_MEM_LEMMA THEN
 IRTAC MEM_PACKET_BD_IMPLIES_MEM_BDS_TO_WRITE_BACK_LEMMA THEN
 STAC
 ,
 ETAC optionTheory.SOME_11 THEN
 IRTAC lists_lemmasTheory.NOT_NULL_IMPLIES_EXISTING_HD_TL_LEMMA THEN
 AXTAC THEN
 LRTAC THEN
 IRTAC lists_lemmasTheory.LAST_IS_MEM_LEMMA THEN
 IRTAC MEM_PACKET_BD_IMPLIES_MEM_BDS_TO_WRITE_BACK_LEMMA THEN
 STAC
 ,
 IRTAC FIND_SOME_IS_MEMBER_LEMMA THEN IRTAC MEM_PACKET_BD_IMPLIES_MEM_BDS_TO_WRITE_BACK_LEMMA THEN STAC
 ,
 IRTAC FIND_SOME_IS_MEMBER_LEMMA THEN IRTAC MEM_PACKET_BD_IMPLIES_MEM_BDS_TO_WRITE_BACK_LEMMA THEN STAC
]
QED

Theorem APPEND_2_ZEROS_PRESERVES_LT_LEMMA:
!(x : 30 word) y.
  x <+ y
  ==>
  (x @@ (0w : 2 word)) <+ (y @@ (0w : 2 word)) : 32 word
Proof
blastLib.BBLAST_TAC
QED

Theorem APPEND_2_ZEROS_EQ_MULTIPLY_BY_4_LEMMA:
!x : 30 word.
  ((x @@ (0w : 2 word)) : 32 word) = (w2w x : 32 word) * 4w
Proof
blastLib.BBLAST_TAC
QED

Theorem W2W_30_W2W_32_EQ_W2W_32:
!x : 14 word.
  (w2w ((w2w x) : 30 word)) : 32 word = w2w x
Proof
blastLib.BBLAST_TAC
QED

Theorem LEQ_IMPLIES_2BIT_EXTENSION_MULTIPLY_BY_4_LEQ_LEMMA:
!(x : 30 word) y.
  x <=+ y
  ==>
  (w2w x : 32 word) * 4w <=+ (w2w y) * 4w
Proof
blastLib.BBLAST_TAC
QED

Theorem LT_IMPLIES_APPEND_2_ZEROS_MINUS_4_LEQ_LEMMA:
!(x : 30 word) (y : 30 word).
  x <+ y
  ==>
  (x @@ (0w : 2 word)) <=+ (y @@ (0w : 2 word)) - 4w : 32 word
Proof
blastLib.BBLAST_TAC
QED

Theorem LT_IMPLIES_APPEND_2_ZEROS_LEQ_4_LEMMA:
!(x : 30 word) y.
  x <+ y
  ==>
  4w <=+ (y @@ (0w : 2 word)) : 32 word
Proof
blastLib.BBLAST_TAC
QED

Theorem LR_BD_INDEX_LT_65535_PLUS_16383_LEMMA:
!lr_start_index mr lr_bd_index mr_bd_index internal_state.
  lr_start_index = (29 >< 16) (internal_state.registers.QMEMCTRL mr) : 30 word /\
  lr_bd_index = lr_start_index + w2w (mr_bd_index : 16 word)
  ==>
  lr_bd_index <+ 65536w + 16384w
Proof
blastLib.BBLAST_TAC
QED

Theorem LT_80000_IMPLIES_2BIT_EXTENSION_MULTIPLY_BY_4_LT_LEMMA:
!(x : 30 word).
  x <+ 0x10000w + 16384w
  ==>
  ((x @@ (0w : 2 word)) : 32 word) <+ 4w * (0x10000w + 16384w)
Proof
blastLib.BBLAST_TAC
QED

Definition ENDPOINTS_TX_SOP_LI_EQ:
ENDPOINTS_TX_SOP_LI_EQ endpoints_tx1 endpoints_tx2 =
!endpoint_id.
  (endpoints_tx1 endpoint_id).sop = (endpoints_tx2 endpoint_id).sop /\
  (endpoints_tx1 endpoint_id).sop_li = (endpoints_tx2 endpoint_id).sop_li
End

Theorem ENDPOINTS_TX_SOP_LI_EQ_REFL_LEMMA:
!endpoints_tx.
  ENDPOINTS_TX_SOP_LI_EQ endpoints_tx endpoints_tx
Proof
GEN_TAC THEN
PTAC ENDPOINTS_TX_SOP_LI_EQ THEN
STAC
QED

val _ = export_theory();
