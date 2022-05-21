open HolKernel Parse boolLib bossLib helper_tactics;
open bbb_usb_stateTheory;

val _ = new_theory "bbb_usb_functions";

Definition DMA_SCHED_CTRL_ENABLE:
DMA_SCHED_CTRL_ENABLE (DMA_SCHED_CTRL : 32 word) =
  word_bit 31 DMA_SCHED_CTRL
End

Definition DMA_SCHED_CTRL_LAST_ENTRY:
DMA_SCHED_CTRL_LAST_ENTRY (DMA_SCHED_CTRL : 32 word) = (7 >< 0) DMA_SCHED_CTRL : 8 word
End

Definition word32_to_bytes:
word32_to_bytes (bytes4 : 32 word) =
  [(31 >< 24) (bytes4) : 8 word; (23 >< 16) (bytes4) : 8 word;
   (15 ><  8) (bytes4) : 8 word; ( 7 ><  0) (bytes4) : 8 word]
End

(* 4 addresses to address 4 bytes, and being 4-byte word aligned.
 *)
Definition WORD_ALIGNED_ADDRESSES:
WORD_ALIGNED_ADDRESSES addresses = (
  LENGTH addresses = 4 /\
  HD addresses && 0xFFFFFFFCw = 0w
)
End

Definition CONSECUTIVE_ADDRESSES:
CONSECUTIVE_ADDRESSES (addresses : 32 word list) = (
  HD addresses = ((HD o TL) addresses) + 1w /\
  (HD o TL) addresses = ((HD o TL o TL) addresses) + 1w /\
  (HD o TL o TL) addresses = ((HD o TL o TL o TL) addresses) + 1w
)
End

Definition generate_consecutive_addresses_rec:
generate_consecutive_addresses_rec current_address current_index =
  if current_index = 0 then
    [current_address]
  else
    current_address::(generate_consecutive_addresses_rec (current_address + 1w) (current_index - 1))
End

Definition generate_consecutive_addresses:
generate_consecutive_addresses start_address number_of_addresses =
  generate_consecutive_addresses_rec start_address (number_of_addresses - 1)
End

(*
Definition generate_consecutive_addresses:
generate_consecutive_addresses start_address number_of_addresses = GENLIST (\n. start_address + n2w n) number_of_addresses
End
*)

Definition bd_aligned_read_addresses:
bd_aligned_read_addresses (bd_address : 32 word) =
  let bd_aligned_address = bd_address && 0xFFFFFFE0w in
  let read_addresses = generate_consecutive_addresses bd_aligned_address 32 in
    read_addresses
End

(* word32_aligned
  [address0, address1, address2, address3,
   address4, address5, address6, address7,
   address8, address9, address10, address11]
  2 =
  [address4, address5, address6, address7]
*)
Definition word32aligned:
word32aligned (addresses : 32 word list) (word_index : num) =
  TAKE 4 (DROP (word_index*4) addresses)
End

Definition merge_lists:
(merge_lists ([], l2) = []) /\
(merge_lists (l1, []) = []) /\
(merge_lists (h1::t1, h2::t2) = (h1, h2)::merge_lists (t1, t2))
End


Definition form_bd:
form_bd (bytes : 8 word list) (word_index : num) =
  if word_index = 0 then
    concat_word_list (TAKE 4 (DROP  0 bytes)) : 32 word
  else if word_index = 1 then
    concat_word_list (TAKE 4 (DROP  4 bytes))
  else if word_index = 2 then
    concat_word_list (TAKE 4 (DROP  8 bytes))
  else if word_index = 3 then
    concat_word_list (TAKE 4 (DROP 12 bytes))
  else if word_index = 4 then
    concat_word_list (TAKE 4 (DROP 16 bytes))
  else if word_index = 5 then
    concat_word_list (TAKE 4 (DROP 20 bytes))
  else if word_index = 6 then
    concat_word_list (TAKE 4 (DROP 24 bytes))
  else (*if word_index = 7 then*)
    concat_word_list (TAKE 4 (DROP 28 bytes))
End

Definition form_bd_li:
form_bd_li (bytes : 8 word list) =
  ((form_bd bytes), concat_word_list (TAKE 4 (DROP 32 bytes)) : 32 word)
End

Definition next_bd_pointer:
next_bd_pointer (bd : num -> 32 word) = bd 5
End

Definition buffer_length:
buffer_length (bd : num -> 32 word) = (21 >< 0) (bd 3) : 32 word
End

Definition buffer_pointer:
buffer_pointer (bd : num -> 32 word) = bd 4
End

Definition eop_bd:
eop_bd (bd : num -> 32 word) = (bd 5 = 0w)
End

Definition tx_completion_queue_id:
tx_completion_queue_id (sop_bd : num -> 32 word) = ((7 >< 0) (sop_bd 2))
End


Definition LRAM_TOTAL_NUMBER_OF_BDS:
LRAM_TOTAL_NUMBER_OF_BDS = 65536
End

Definition LRAM_BD_BYTE_SIZE:
LRAM_BD_BYTE_SIZE = 4
End

Definition linking_ram_addresses_accurate:
linking_ram_addresses_accurate registers =
  let linking_ram0_start = (w2w registers.LRAM0BASE << 2) : 32 word in
  let linking_ram0_byte_size = w2n ((registers.LRAM0SIZE @@ (0w : 2 word)) : 16 word) in
  let linking_ram0_addresses = generate_consecutive_addresses linking_ram0_start linking_ram0_byte_size in
  let linking_ram1_start = (w2w registers.LRAM1BASE << 2) : 32 word in
  let linking_ram1_byte_size = LRAM_TOTAL_NUMBER_OF_BDS*LRAM_BD_BYTE_SIZE - linking_ram0_byte_size in
  let linking_ram1_addresses = generate_consecutive_addresses linking_ram1_start linking_ram1_byte_size in
  let linking_ram_addresses = linking_ram0_addresses ++ linking_ram1_addresses in
    linking_ram_addresses
End

Definition linking_ram_addresses_approximate:
linking_ram_addresses_approximate registers =
  let linking_ram0_start = ((w2w registers.LRAM0BASE : 30 word) @@ (0w : 2 word)) : 32 word in
  let linking_ram0_byte_size = w2n (((w2w registers.LRAM0SIZE : 30 word) @@ (0w : 2 word)) : 32 word) in
  let linking_ram0_addresses = generate_consecutive_addresses linking_ram0_start linking_ram0_byte_size in
  let linking_ram1_start = ((w2w registers.LRAM1BASE : 30 word) @@ (0w : 2 word)) : 32 word in
  let linking_ram1_byte_size = 2*LRAM_TOTAL_NUMBER_OF_BDS*LRAM_BD_BYTE_SIZE in (* Twice the maximum size covers the largest possible BD index computed by bd_mr_info_rec, which can give indexes up to 2^16 + 2^14 and here we have 2^17. *)
  let linking_ram1_addresses = generate_consecutive_addresses linking_ram1_start linking_ram1_byte_size in
  let linking_ram_addresses = linking_ram0_addresses ++ linking_ram1_addresses in
    linking_ram_addresses
End







(*
			bd_mr_info(bd_address : word32) ≝
				//Identification of the memory region and index (the position of
				//the BD at @bd_address in the address space counted in terms of
				//number of BDs with respect to the byte size of the BDs in the
				//memory region) of the BD:
				for r = 0...7	//Iterate until correct region is found.
					bd_size ≔ 5 + QMEMCTRL[r].DESC_SIZE
					start_index ≔ QMEMRBASE[r] >> bd_size
					bd_index ≔ bd_address >> bd_size
					number_of_bds ≔ 1 << (5 + QMEMCTRL[r].REG_SIZE)
					end_index ≔ start_index + number_of_bds
					if start_index ≤ bd_index ∧ bd_index < end_index then
						mr ≔ r	//Index of memory region from 0 through 7.
						mr_bd_index ≔ bd_index - start_index	//BD index in mr
						return (mr, mr_bd_index)
*)
Definition bd_mr_info_rec:
bd_mr_info_rec registers (bd_address : 32 word) (r : num) =
  let bd_size = (5w + ((11 >< 8) (registers.QMEMCTRL (n2w r)))) : 4 word in
  let start_index = ((w2w (registers.QMEMRBASE (n2w r))) : 32 word) >>> (w2n bd_size) in
  let bd_index = bd_address >>> (w2n bd_size) in
  let number_of_bds = 1w : 32 word << w2n (5w + ((2 >< 0) (registers.QMEMCTRL (n2w r)) : 4 word)) in
  let end_index = start_index + number_of_bds in
    if r = 0 then
      (r, (15 >< 0) (bd_index - start_index) : 16 word)
    else if start_index <=+ bd_index /\ bd_index <+ end_index then
      (r, (15 >< 0) (bd_index - start_index) : 16 word)
    else
      bd_mr_info_rec registers bd_address (r - 1)
End

Definition bd_mr_info:
bd_mr_info registers (bd_address : 32 word) =
let current_memory_region = 7 in
  bd_mr_info_rec registers bd_address current_memory_region
End

(*
			bd_address_to_li_address(bd_address : word32) ≝
				(mr, mr_bd_index) ≔ bd_mr_info(bd_address)

				//Identification of linking RAM index of the BD.
				lr_start_index ≔ QMEMCTRL[mr][29:16]
				lr_bd_index ≔ lr_start_index + mr_bd_index

				//Identification of absolute linking information address.
				if lr_bd_index < LRAM0SIZE then		//Linking RAM 0.
					li_address ≔ (LRAM0BASE + lr_bd_index) << 2 ++ "00"
				else
					li_address ≔ (LRAM1BASE + lr_bd_index) << 2 ++ "00"

				return li_address
*)
Definition bd_address_to_li_address:
bd_address_to_li_address registers (bd_address : 32 word) =
  let (mr, mr_bd_index) = bd_mr_info registers bd_address in
  let lr_start_index = (29 >< 16) (registers.QMEMCTRL (n2w mr)) : 30 word in
  let lr_bd_index = lr_start_index + w2w mr_bd_index in
    if lr_bd_index <+ w2w registers.LRAM0SIZE then
      (((w2w registers.LRAM0BASE : 30 word) @@ (0w : 2 word)) : 32 word) + ((lr_bd_index @@ (0w : 2 word)) : 32 word)
    else
      (((w2w registers.LRAM1BASE : 30 word) @@ (0w : 2 word)) : 32 word) + ((lr_bd_index @@ (0w : 2 word)) : 32 word)
End

Definition bd_address_to_li_addresses:
bd_address_to_li_addresses registers bd_address =
  let li_address = bd_address_to_li_address registers bd_address in
  let li_addresses = generate_consecutive_addresses li_address 4 in
    li_addresses
End




(*
			bd_address_to_internal_4lsb(bd_address : word32) ≝
				if bd_address[0] = 0 then		//Even size.
					bd_address[4:1]
				else							//Odd size.
					(bd_address[4:0] + 1)[4:1]	//One more than was written.
*)
Definition bd_address_to_internal_4lsb:
bd_address_to_internal_4lsb (bd_address : 32 word) =
  if (0 >< 0) bd_address = 0w : 1 word then
    (4 >< 1) bd_address : 4 word
  else
    (4 >< 1) (((4 >< 0) bd_address : 5 word) + 1w)
End

Definition form_li_bytes:
form_li_bytes (next_bd_mr : num) (next_bd_mr_index : 16 word) (next_bd_size : 4 word) (eoq : bool) =
  let li_next_bd_mr = (n2w next_bd_mr : 32 word) << 21 in
  let li_next_bd_mr_index = (w2w next_bd_mr_index : 32 word) << 5 in
  let li_next_bd_size = (w2w next_bd_size : 32 word) << 1 in
  let li_eoq = if eoq then 1w : 32 word else 0w : 32 word in
  let li = li_next_bd_mr || li_next_bd_mr_index || li_next_bd_size || li_eoq in
  let li_bytes = [(31 >< 24) li : 8 word; (23 >< 16) li : 8 word; (15 >< 8) li : 8 word; (7 >< 0) li : 8 word] in
    li_bytes
End






(*
			linking_information ≝ {
				next_bd_mr : word3,			//Memory region ID of next BD: linking_information[23:21].
				next_bd_mr_index : word16,	//BD index of next BD: linking_information[20:5].
				next_bd_size : word4		//Internal BD size from D register: linking_information[4:1].
				EOQ : word1					//This is the SOP BD in the queue: linking_information[0].
			}
*)
Definition li_to_next_bd_mr:
li_to_next_bd_mr (li : 32 word) = (23 >< 21) li : 3 word
End

Definition li_to_next_mr_bd_index:
li_to_next_mr_bd_index (li : 32 word) = (20 >< 5) li : 16 word
End

Definition li_to_next_bd_size:
li_to_next_bd_size (li : 32 word) = (4 >< 1) li : 4 word
End

Definition li_to_eoq:
li_to_eoq (li : 32 word) = word_bit 0 li
End

(*
			li_to_next_bd_address(li : linking_information) ≝
				mr_bd_size ≔ QMEMCTRL[li.next_bd_mr][11:8] + 5
				mr_index ≔ QMEMRBASE[li.next_bd_mr] >> mr_bd_size
				mr_bd_index ≔ li.next_bd_mr_index
				bd_address ≔ (mr_index + mr_bd_index) << mr_bd_size
				bd_size ≔ li.next_bd_size
				bd_address ≔ bd_address[31:5] ++ bd_size ++ "0"
				return bd_address
*)
Definition li_to_next_bd_address:
li_to_next_bd_address registers (li : 32 word) =
  let mr_bd_size = w2n ((11 >< 8) (registers.QMEMCTRL (li_to_next_bd_mr li)) : 4 word) + 5 in
  let mr_index = w2w ((registers.QMEMRBASE (li_to_next_bd_mr li)) >> mr_bd_size) : 32 word in
  let mr_bd_index = w2w (li_to_next_mr_bd_index li) : 32 word in
  let bd_address = (mr_index + mr_bd_index) << mr_bd_size in
  let bd_size = w2w (li_to_next_bd_size li) : 32 word in
  let bd_address = (bd_address && 0xFFFFFFEw) || bd_size in
    bd_address
End

Definition get_bd_ras:
get_bd_ras registers bd_ra =
(*  if bd_ra = 0w then
    []
  else*)
    let bd_addresses = bd_aligned_read_addresses bd_ra in
    let li_addresses = bd_address_to_li_addresses registers bd_ra in
      bd_addresses ++ li_addresses
End

Definition get_dma_packet_bds:
(get_dma_packet_bds [] = ([], [])) /\
(get_dma_packet_bds (((bd, li), bd_ras, bd_was)::bds) =
  if eop_bd bd then
    ([((bd, li), bd_ras, bd_was)], bds)
  else
    let (dma_packet_bds, remaining_bds) = get_dma_packet_bds bds in
      (((bd, li), bd_ras, bd_was)::dma_packet_bds, remaining_bds))
End

val get_dma_packets_bds_tgoal = Hol_defn "get_dma_packets_bds" ‘
(get_dma_packets_bds [] = []) /\
(get_dma_packets_bds (bd::bds) =
  let (dma_packet_bds, remaining_bds) = get_dma_packet_bds (bd::bds) in
    dma_packet_bds::(get_dma_packets_bds remaining_bds))’

val (get_dma_packets_bds, get_dma_packets_bds_ind) = Defn.tprove (
(*Defn.tgoal*) get_dma_packets_bds_tgoal,
WF_REL_TAC ‘measure LENGTH’ THEN
Induct THENL
[
 INTRO_TAC THEN
 PTAC get_dma_packet_bds THENL
 [
  EQ_PAIR_ASM_TAC THEN LRTAC THEN REWRITE_TAC [listTheory.LENGTH, prim_recTheory.LESS_0]
  ,
  EQ_PAIR_ASM_TAC THEN PTAC get_dma_packet_bds THEN EQ_PAIR_ASM_TAC THEN NRLTAC 2 THEN LRTAC THEN
  REWRITE_TAC [listTheory.LENGTH, prim_recTheory.LESS_0]
 ]
 ,
 INTRO_TAC THEN
 PTAC get_dma_packet_bds THENL
 [
  EQ_PAIR_ASM_TAC THEN LRTAC THEN REWRITE_TAC [listTheory.LENGTH, prim_recTheory.LESS_MONO_EQ, prim_recTheory.LESS_SUC_REFL]
  ,
  AIRTAC THEN EQ_PAIR_ASM_TAC THEN RLTAC THEN ETAC listTheory.LENGTH THEN IRTAC prim_recTheory.LESS_SUC THEN STAC
 ]
]
)

val get_dma_packets_bds = save_thm ("get_dma_packets_bds", get_dma_packets_bds)
val get_dma_packets_bds_ind = save_thm ("get_dma_packets_bds_ind", get_dma_packets_bds_ind)

Definition find_packet_bds:
(find_packet_bds P [] = F) /\
(find_packet_bds P ((sop_bd, sop_bd_ras, sop_bd_was)::packet_bds) = P (HD sop_bd_ras))
End

Definition get_dma_packet_bds_to_release:
get_dma_packet_bds_to_release internal_state endpoint_state bds_to_release =
  let packets_bds = get_dma_packets_bds bds_to_release in
    if endpoint_state = tx_write_back_sop_bd1 then
      if NULL packets_bds then NONE else SOME (LAST packets_bds)
    else if endpoint_state = tx_write_back_sop_bd2 then
      if NULL packets_bds then NONE else SOME (LAST packets_bds)
    else if endpoint_state = tx_write_back_sop_bd3 then
      let P = \bd_ra. EXISTS (\(a, li). bd_ra = a) internal_state.completion_queue_write_backs in
        FIND (find_packet_bds P) packets_bds
    else if endpoint_state = tx_write_back_sop_bd4 then
      let P = \bd_ra. EXISTS (\a. bd_ra = a) internal_state.write_back_popped_bds in
        FIND (find_packet_bds P) packets_bds
    else
      NONE
End

val _ = export_theory();

