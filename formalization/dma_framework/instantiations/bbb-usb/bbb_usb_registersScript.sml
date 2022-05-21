open HolKernel Parse boolLib bossLib;
open bbb_usb_functionsTheory bbb_usb_rxTheory bbb_usb_txTheory;

val _ = new_theory "bbb_usb_registers";

Definition CPPI_DMA_REGISTERS_BASE:
CPPI_DMA_REGISTERS_BASE = 0x47402000w : 32 word
End

Definition TXGCR_ADDRESSES:
TXGCR_ADDRESSES (address : 32 word) = (
  address = CPPI_DMA_REGISTERS_BASE + 0x800w \/ (* TXGCR0 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x820w \/ (* TXGCR1 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x840w \/ (* TXGCR2 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x860w \/ (* TXGCR3 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x880w \/ (* TXGCR4 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x8A0w \/ (* TXGCR5 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x8C0w \/ (* TXGCR6 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x8E0w \/ (* TXGCR7 *)

  address = CPPI_DMA_REGISTERS_BASE + 0x900w \/ (* TXGCR8 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x920w \/ (* TXGCR9 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x940w \/ (* TXGCR10 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x960w \/ (* TXGCR11 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x980w \/ (* TXGCR12 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x9A0w \/ (* TXGCR13 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x9C0w \/ (* TXGCR14 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x9E0w \/ (* TXGCR15 *)

  address = CPPI_DMA_REGISTERS_BASE + 0xA00w \/ (* TXGCR16 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xA20w \/ (* TXGCR17 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xA40w \/ (* TXGCR18 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xA60w \/ (* TXGCR19 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xA80w \/ (* TXGCR20 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xAA0w \/ (* TXGCR21 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xAC0w \/ (* TXGCR22 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xAE0w \/ (* TXGCR23 *)

  address = CPPI_DMA_REGISTERS_BASE + 0xB00w \/ (* TXGCR24 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xB20w \/ (* TXGCR25 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xB40w \/ (* TXGCR26 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xB60w \/ (* TXGCR27 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xB80w \/ (* TXGCR28 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xBA0w    (* TXGCR29 *)
)
End

Definition RXGCR_ADDRESSES:
RXGCR_ADDRESSES (address : 32 word) = (
  address = CPPI_DMA_REGISTERS_BASE + 0x808w \/ (* RXGCR0 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x828w \/ (* RXGCR1 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x848w \/ (* RXGCR2 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x868w \/ (* RXGCR3 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x888w \/ (* RXGCR4 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x8A8w \/ (* RXGCR5 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x8C8w \/ (* RXGCR6 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x8E8w \/ (* RXGCR7 *)

  address = CPPI_DMA_REGISTERS_BASE + 0x908w \/ (* RXGCR8 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x928w \/ (* RXGCR9 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x948w \/ (* RXGCR10 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x968w \/ (* RXGCR11 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x988w \/ (* RXGCR12 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x9A8w \/ (* RXGCR13 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x9C8w \/ (* RXGCR14 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x9E8w \/ (* RXGCR15 *)

  address = CPPI_DMA_REGISTERS_BASE + 0xA08w \/ (* RXGCR16 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xA28w \/ (* RXGCR17 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xA48w \/ (* RXGCR18 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xA68w \/ (* RXGCR19 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xA88w \/ (* RXGCR20 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xAA8w \/ (* RXGCR21 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xAC8w \/ (* RXGCR22 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xAE8w \/ (* RXGCR23 *)

  address = CPPI_DMA_REGISTERS_BASE + 0xB08w \/ (* RXGCR24 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xB28w \/ (* RXGCR25 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xB48w \/ (* RXGCR26 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xB68w \/ (* RXGCR27 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xB88w \/ (* RXGCR28 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xBA8w    (* RXGCR29 *)
)
End

Definition QUEUE_MANAGER_BASE:
QUEUE_MANAGER_BASE = 0x47404000w : 32 word
End

Definition LRAM_ADDRESSES:
LRAM_ADDRESSES (address : 32 word) = (
  address = QUEUE_MANAGER_BASE + 80w \/ (* LRAM0BASE *)
  address = QUEUE_MANAGER_BASE + 84w \/ (* LRAM0SIZE *)
  address = QUEUE_MANAGER_BASE + 88w    (* LRAM1BASE *)
)
End

Definition QMEMCTRL_ADDRESSES:
QMEMCTRL_ADDRESSES (address : 32 word) = (
  QUEUE_MANAGER_BASE + 0x1004w = address \/ (* QMEMCTRL0 *)
  QUEUE_MANAGER_BASE + 0x1014w = address \/ (* QMEMCTRL1 *)
  QUEUE_MANAGER_BASE + 0x1024w = address \/ (* QMEMCTRL2 *)
  QUEUE_MANAGER_BASE + 0x1034w = address \/ (* QMEMCTRL3 *)
  QUEUE_MANAGER_BASE + 0x1044w = address \/ (* QMEMCTRL4 *)
  QUEUE_MANAGER_BASE + 0x1054w = address \/ (* QMEMCTRL5 *)
  QUEUE_MANAGER_BASE + 0x1064w = address \/ (* QMEMCTRL6 *)
  QUEUE_MANAGER_BASE + 0x1074w = address    (* QMEMCTRL7 *)
)
End

Definition QMEMRBASE_ADDRESSES:
QMEMRBASE_ADDRESSES (address : 32 word) = (
  QUEUE_MANAGER_BASE + 0x1000w = address \/ (* QMEMRBASE0 *)
  QUEUE_MANAGER_BASE + 0x1010w = address \/ (* QMEMRBASE1 *)
  QUEUE_MANAGER_BASE + 0x1020w = address \/ (* QMEMRBASE2 *)
  QUEUE_MANAGER_BASE + 0x1030w = address \/ (* QMEMRBASE3 *)
  QUEUE_MANAGER_BASE + 0x1040w = address \/ (* QMEMRBASE4 *)
  QUEUE_MANAGER_BASE + 0x1050w = address \/ (* QMEMRBASE5 *)
  QUEUE_MANAGER_BASE + 0x1060w = address \/ (* QMEMRBASE6 *)
  QUEUE_MANAGER_BASE + 0x1070w = address    (* QMEMRBASE7 *)
)
End

Definition SCHEDULER_BASE:
SCHEDULER_BASE = 0x47403000w : 32 word
End

Definition SCHEDULER_SCHED_CTRL_OFFSET:
SCHEDULER_SCHED_CTRL_OFFSET = 0w : 32 word
End

Definition WORD0_OFFSET:
WORD0_OFFSET = 0x800w : 32 word
End

Definition WORD63_OFFSET:
WORD63_OFFSET = 0x8FCw : 32 word
End

Definition SCHEDULER_ADDRESSES:
SCHEDULER_ADDRESSES (address : 32 word) = (
  SCHEDULER_BASE + SCHEDULER_SCHED_CTRL_OFFSET = address \/
  SCHEDULER_BASE + WORD0_OFFSET <=+ address /\ address <=+ SCHEDULER_BASE + WORD63_OFFSET
)
End

Definition RXHPCRA_ADDRESSES:
RXHPCRA_ADDRESSES (address : 32 word) = (
  address = CPPI_DMA_REGISTERS_BASE + 0x80Cw \/ (* RXHPCRA0 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x82Cw \/ (* RXHPCRA1 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x84Cw \/ (* RXHPCRA2 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x86Cw \/ (* RXHPCRA3 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x88Cw \/ (* RXHPCRA4 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x8ACw \/ (* RXHPCRA5 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x8CCw \/ (* RXHPCRA6 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x8ECw \/ (* RXHPCRA7 *)

  address = CPPI_DMA_REGISTERS_BASE + 0x90Cw \/ (* RXHPCRA8 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x92Cw \/ (* RXHPCRA9 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x94Cw \/ (* RXHPCRA10 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x96Cw \/ (* RXHPCRA11 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x98Cw \/ (* RXHPCRA12 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x9ACw \/ (* RXHPCRA13 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x9CCw \/ (* RXHPCRA14 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x9ECw \/ (* RXHPCRA15 *)

  address = CPPI_DMA_REGISTERS_BASE + 0xA0Cw \/ (* RXHPCRA16 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xA2Cw \/ (* RXHPCRA17 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xA4Cw \/ (* RXHPCRA18 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xA6Cw \/ (* RXHPCRA19 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xA8Cw \/ (* RXHPCRA20 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xAACw \/ (* RXHPCRA21 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xACCw \/ (* RXHPCRA22 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xAECw \/ (* RXHPCRA23 *)

  address = CPPI_DMA_REGISTERS_BASE + 0xB0Cw \/ (* RXHPCRA24 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xB2Cw \/ (* RXHPCRA25 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xB4Cw \/ (* RXHPCRA26 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xB6Cw \/ (* RXHPCRA27 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xB8Cw \/ (* RXHPCRA28 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xBACw    (* RXHPCRA29 *)
)
End

Definition RXHPCRB_ADDRESSES:
RXHPCRB_ADDRESSES (address : 32 word) = (
  address = CPPI_DMA_REGISTERS_BASE + 0x800w \/ (* RXHPCRB0 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x820w \/ (* RXHPCRB1 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x840w \/ (* RXHPCRB2 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x860w \/ (* RXHPCRB3 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x880w \/ (* RXHPCRB4 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x8A0w \/ (* RXHPCRB5 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x8C0w \/ (* RXHPCRB6 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x8E0w \/ (* RXHPCRB7 *)

  address = CPPI_DMA_REGISTERS_BASE + 0x900w \/ (* RXHPCRB8 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x920w \/ (* RXHPCRB9 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x940w \/ (* RXHPCRB10 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x960w \/ (* RXHPCRB11 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x980w \/ (* RXHPCRB12 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x9A0w \/ (* RXHPCRB13 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x9C0w \/ (* RXHPCRB14 *)
  address = CPPI_DMA_REGISTERS_BASE + 0x9E0w \/ (* RXHPCRB15 *)

  address = CPPI_DMA_REGISTERS_BASE + 0xA00w \/ (* RXHPCRB16 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xA20w \/ (* RXHPCRB17 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xA40w \/ (* RXHPCRB18 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xA60w \/ (* RXHPCRB19 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xA80w \/ (* RXHPCRB20 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xAA0w \/ (* RXHPCRB21 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xAC0w \/ (* RXHPCRB22 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xAE0w \/ (* RXHPCRB23 *)

  address = CPPI_DMA_REGISTERS_BASE + 0xB00w \/ (* RXHPCRB24 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xB20w \/ (* RXHPCRB25 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xB40w \/ (* RXHPCRB26 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xB60w \/ (* RXHPCRB27 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xB80w \/ (* RXHPCRB28 *)
  address = CPPI_DMA_REGISTERS_BASE + 0xBA0w    (* RXHPCRB29 *)
)
End

Definition QUEUE_D_0_OFFSET:
QUEUE_D_0_OFFSET = 0x200Cw
End

Definition QUEUE_D_ADDRESSES:
QUEUE_D_ADDRESSES (address : 32 word) =
  ?queue_id : num.
     0 <= queue_id /\ queue_id <= 155 /\ (* 156 queues from 0 to 155 *)
     address = QUEUE_MANAGER_BASE + QUEUE_D_0_OFFSET + n2w (16*queue_id) (* 16 bytes between each D register. *)
End

Definition bbb_usb_DMA_REGISTER_ADDRESSES:
bbb_usb_DMA_REGISTER_ADDRESSES (address : 32 word) = (
  TXGCR_ADDRESSES address \/
  RXGCR_ADDRESSES address \/
  LRAM_ADDRESSES address \/
  QMEMCTRL_ADDRESSES address \/
  QMEMRBASE_ADDRESSES address \/
  SCHEDULER_ADDRESSES address \/
  RXHPCRA_ADDRESSES address \/
  RXHPCRB_ADDRESSES address \/
  QUEUE_D_ADDRESSES address
)
End

(* Register accesses can only cause memory accesses to linking RAM, where in
   this case linking ram is larger than necessary to facilitate the proof.
 *)
Definition bbb_usb_scratchpad_addresses:
bbb_usb_scratchpad_addresses internal_state =
  (linking_ram_addresses_approximate internal_state.registers)
End





Definition read_register_txgcr:
read_register_txgcr internal_state address =
  let endpoint_id = w2w ((address - (CPPI_DMA_REGISTERS_BASE + 0x800w)) >>> 5) : 5 word in
  let register_value = internal_state.registers.TXGCR endpoint_id in
  let bytes = word32_to_bytes register_value in
    (bytes, [])
End

Definition read_register_rxgcr:
read_register_rxgcr internal_state address =
  let endpoint_id = w2w ((address - (CPPI_DMA_REGISTERS_BASE + 0x808w)) >>> 5) : 5 word in
  let register_value = internal_state.registers.RXGCR endpoint_id in
  let bytes = word32_to_bytes register_value in
    (bytes, [])
End

Definition read_registers_lram:
read_registers_lram internal_state address =
  if address = QUEUE_MANAGER_BASE + 80w then      (* LRAM0BASE *)
    (word32_to_bytes ((w2w internal_state.registers.LRAM0BASE : 32 word) << 2), [])
  else if address = QUEUE_MANAGER_BASE + 84w then (* LRAM0SIZE *)
    (word32_to_bytes (w2w internal_state.registers.LRAM0SIZE : 32 word), [])
  else (* address = QUEUE_MANAGER_BASE + 88w *)   (* LRAM1BASE *)
    (word32_to_bytes ((w2w internal_state.registers.LRAM1BASE : 32 word) << 2), [])
End

Definition read_register_qmemctrl:
read_register_qmemctrl internal_state address =
  let memory_region_id = w2w ((address - (QUEUE_MANAGER_BASE + 0x1004w)) >>> 4) : 3 word in
  let register_value = internal_state.registers.QMEMCTRL memory_region_id in
  let bytes = word32_to_bytes register_value in
    (bytes, [])
End

Definition read_register_qmemrbase:
read_register_qmemrbase internal_state address =
  let memory_region_id = w2w ((address - (QUEUE_MANAGER_BASE + 0x1000w)) >>> 4) : 3 word in
  let register_value = w2w (internal_state.registers.QMEMRBASE memory_region_id) : 32 word in
  let bytes = word32_to_bytes register_value in
    (bytes, [])
End

Definition read_register_scheduler:
read_register_scheduler internal_state address =
  if SCHEDULER_BASE + SCHEDULER_SCHED_CTRL_OFFSET = address then
    (word32_to_bytes internal_state.registers.DMA_SCHED_CTRL, [])
  else
    let word_index = w2w ((address - (SCHEDULER_BASE + WORD0_OFFSET)) >>> 2) : 6 word in
    let register_value = internal_state.registers.WORD word_index in
    let bytes = word32_to_bytes register_value in
      (bytes, [])
End

Definition read_register_rxhpcra:
read_register_rxhpcra internal_state address =
  let endpoint_id = w2w ((address - (CPPI_DMA_REGISTERS_BASE + 0x80Cw)) >>> 5) : 5 word in
  let register_value = internal_state.registers.RXHPCRA endpoint_id in
  let bytes = word32_to_bytes register_value in
    (bytes, [])
End

Definition read_register_rxhpcrb:
read_register_rxhpcrb internal_state address =
  let endpoint_id = w2w ((address - (CPPI_DMA_REGISTERS_BASE + 0x800w)) >>> 5) : 5 word in
  let register_value = internal_state.registers.RXHPCRB endpoint_id in
  let bytes = word32_to_bytes register_value in
    (bytes, [])
End

(*
read_register_d(queue_id : word8) ≝
	if hdp[queue_id] = 0 then
		bd_address ≔ 0
	else
		bd_address ≔ hdp[queue_id]		//Get head BD address.

		//MEMORY READ (WHICH MAY BE PERFORMED AFTER RETURNED VALUE
		//BUT THEN THE CPU CAN READ THE SAME BD ADDRESS MULTIPLE
		//TIMES IF READING FAST ENOUGH, WHICH MAY CAUSE MULTIPLE
		//MEMORY READS; ALL READS AND OPERATIONS ARE IDENTICAL).
		//Can be modeled by updating the internal state such that
		//the first/some/last BD in the queue, if there is one to
		//fetch, reads linking ram. Otherwise this does not work.
		li_address ≔ bd_address_to_li_address(bd_address)
		//MEMORY READ!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
		li ≔ memory4[li_address]
		if li.EOQ then			//Empty queue.
			hdp[queue_id] ≔ 0
			tdp[queue_id] ≔ 0
		else					//Move head to second element.
			hdp[queue_id] ≔ li_to_next_bd_address(li)

	return bd_address
*)
Definition read_register_d:
read_register_d internal_state address =
  let queue_id = w2w (address - (QUEUE_MANAGER_BASE + QUEUE_D_0_OFFSET) >>> 16) : 8 word in
  let bd_address = if internal_state.chp queue_id = 0w then 0w else internal_state.chp queue_id in
  let bytes = word32_to_bytes bd_address in
  let read_addresses = bd_address_to_li_addresses internal_state.registers bd_address in
  let tag = queue_id in
  let memory_request = request_read read_addresses tag in
    (bytes, [memory_request])
End

Definition bbb_usb_read_register:
bbb_usb_read_register internal_state addresses =
  if ~WORD_ALIGNED_ADDRESSES addresses \/ ~CONSECUTIVE_ADDRESSES addresses then
    (internal_state, [] : 8 word list, [] : ((32, 8) interconnect_request_type list))
  else
    let address = HD addresses in
    let (bytes, memory_requests) =
      if TXGCR_ADDRESSES address then
        read_register_txgcr internal_state address
      else if RXGCR_ADDRESSES address then
        read_register_rxgcr internal_state address
      else if LRAM_ADDRESSES address then
        read_registers_lram internal_state address
      else if QMEMCTRL_ADDRESSES address then
        read_register_qmemctrl internal_state address
      else if QMEMRBASE_ADDRESSES address then
        read_register_qmemrbase internal_state address
      else if SCHEDULER_ADDRESSES address then
        read_register_scheduler internal_state address
      else if RXHPCRA_ADDRESSES address then
        read_register_rxhpcra internal_state address
      else if RXHPCRB_ADDRESSES address then
        read_register_rxhpcrb internal_state address
      else if QUEUE_D_ADDRESSES address then
        read_register_d internal_state address
      else
        ([], [])
    in
    (internal_state, bytes, memory_requests)
End







(* Instantiated function used to update the internal state when processing
 * memory replies to memory requests from register accesses. The unprocessed
 * requests are returned.
 *
read_register_d(queue_id : word8) ≝
	if hdp[queue_id] = 0 then
		bd_address ≔ 0
	else
		bd_address ≔ hdp[queue_id]		//Get head BD address.

		//MEMORY READ (WHICH MAY BE PERFORMED AFTER RETURNED VALUE
		//BUT THEN THE CPU CAN READ THE SAME BD ADDRESS MULTIPLE
		//TIMES IF READING FAST ENOUGH, WHICH MAY CAUSE MULTIPLE
		//MEMORY READS; ALL READS AND OPERATIONS ARE IDENTICAL).
		//Can be modeled by updating the internal state such that
		//the first/some/last BD in the queue, if there is one to
		//fetch, reads linking ram. Otherwise this does not work.
		li_address ≔ bd_address_to_li_address(bd_address)
		//MEMORY READ!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
		li ≔ memory4[li_address]
		if li.EOQ then			//Empty queue.
			hdp[queue_id] ≔ 0
			tdp[queue_id] ≔ 0
		else					//Move head to second element.
			hdp[queue_id] ≔ li_to_next_bd_address(li)

	return bd_address

The tag is the queue ID.
 *)
Definition bbb_usb_process_register_related_memory_reply:
bbb_usb_process_register_related_memory_reply internal_state (bytes : 8 word list) (tag : 8 word) =
  let li = concat_word_list (TAKE 4 bytes) : 32 word in
  let queue_id = tag in
  let popped_bds = if li_to_eoq li then [internal_state.ctp queue_id] else [] in (* Popped BD was last and can now be released *)
  let chp = if li_to_eoq li then (queue_id =+ 0w) internal_state.chp
                            else (queue_id =+ li_to_next_bd_address internal_state.registers li) internal_state.chp in
  let ctp = if li_to_eoq li then (queue_id =+ 0w) internal_state.ctp else internal_state.ctp in
  let internal_state = internal_state with <| ctp := ctp;
                                              chp := chp;
                                              write_back_popped_bds := internal_state.write_back_popped_bds ++ popped_bds |> in
    internal_state
End

Definition bbb_usb_process_register_related_memory_replies:
(bbb_usb_process_register_related_memory_replies internal_state requests [] = (internal_state, [])) /\
(bbb_usb_process_register_related_memory_replies internal_state requests ((bytes, tag)::replies) =
 (bbb_usb_process_register_related_memory_reply internal_state bytes tag, [(bytes, tag)])) (* Complete one reply at a time: Fine-grained interleavings. *)
End









Definition write_register_txgcr:
write_register_txgcr internal_state address value =
  let endpoint_id = w2w ((address - (CPPI_DMA_REGISTERS_BASE + 0x800w)) >>> 5) : 5 word in
  let internal_state = internal_state with registers := internal_state.registers with TXGCR := (endpoint_id =+ value) internal_state.registers.TXGCR in
    (internal_state, [])
End

Definition write_register_rxgcr:
write_register_rxgcr internal_state address value =
  let endpoint_id = w2w ((address - (CPPI_DMA_REGISTERS_BASE + 0x808w)) >>> 5) : 5 word in
  let internal_state = internal_state with registers := internal_state.registers with RXGCR := (endpoint_id =+ value) internal_state.registers.TXGCR in
    (internal_state, [])
End

Definition write_registers_lram:
write_registers_lram internal_state address (value : 32 word) =
  let value = w2w value : 14 word in
    if address = QUEUE_MANAGER_BASE + 80w then      (* LRAM0BASE *)
      let value = value && 0xFFFFFFFCw in
      let internal_state = internal_state with registers := internal_state.registers with LRAM0BASE := w2w (value >>> 2) in
        (internal_state, [])
    else if address = QUEUE_MANAGER_BASE + 84w then (* LRAM0SIZE *)
      let internal_state = internal_state with registers := internal_state.registers with LRAM0SIZE := value in
        (internal_state, [])
    else (* address = QUEUE_MANAGER_BASE + 88w *)   (* LRAM1BASE *)
      let value = value && 0xFFFFFFFCw in
      let internal_state = internal_state with registers := internal_state.registers with LRAM1BASE := w2w (value >>> 2) in
        (internal_state, [])
End

Definition write_register_qmemctrl: 
write_register_qmemctrl internal_state address value =
  let memory_region_id = w2w ((address - (QUEUE_MANAGER_BASE + 0x1004w)) >>> 4) : 3 word in
  let internal_state = internal_state with registers := internal_state.registers with QMEMCTRL := (memory_region_id =+ value) internal_state.registers.QMEMCTRL in
    (internal_state, [])
End

Definition write_register_qmemrbase:
write_register_qmemrbase internal_state address (value : 32 word) =
  let value = w2w value : 27 word in
  let memory_region_id = w2w ((address - (QUEUE_MANAGER_BASE + 0x1000w)) >>> 4) : 3 word in
  let internal_state = internal_state with registers := internal_state.registers with QMEMRBASE := (memory_region_id =+ value) internal_state.registers.QMEMRBASE in
    (internal_state, [])
End

Definition write_register_scheduler:
write_register_scheduler internal_state address value =
  if SCHEDULER_BASE + SCHEDULER_SCHED_CTRL_OFFSET = address then
    let internal_state = internal_state with registers := internal_state.registers with DMA_SCHED_CTRL := value in
    (internal_state, [])
  else
    let word_index = w2w ((address - (SCHEDULER_BASE + WORD0_OFFSET)) >>> 2) : 6 word in
    let internal_state = internal_state with registers := internal_state.registers with WORD := (word_index =+ value) internal_state.registers.WORD in
      (internal_state, [])
End

Definition write_register_rxhpcra:
write_register_rxhpcra internal_state address value =
  let endpoint_id = w2w ((address - (CPPI_DMA_REGISTERS_BASE + 0x80Cw)) >>> 5) : 5 word in
  let internal_state = internal_state with registers := internal_state.registers with RXHPCRA := (endpoint_id =+ value) internal_state.registers.RXHPCRA in
    (internal_state, [])
End

Definition write_register_rxhpcrb:
write_register_rxhpcrb internal_state address value =
  let endpoint_id = w2w ((address - (CPPI_DMA_REGISTERS_BASE + 0x800w)) >>> 5) : 5 word in
  let internal_state = internal_state with registers := internal_state.registers with RXHPCRB := (endpoint_id =+ value) internal_state.registers.RXHPCRB in
    (internal_state, [])
End

(*
write_register_d(queue_id : word8, bd_address : word32) ≝
	if tdp[queue_id] = 0 then	//Initialize head.
		hdp[queue_id] ≔ bd_address
	else			//Link previous tail to new tail @bd_address.
		(next_bd_mr, next_bd_mr_index) ≔ bd_mr_info(bd_address)
		li ≔ {
			next_bd_mr ≔ next_bd_mr
			next_bd_mr_index ≔ next_bd_mr_index
			next_bd_size ≔ bd_address_to_internal_4lsb(bd_address)
			EOQ ≔ 0
		}
		li_address ≔ bd_address_to_li_address(tdp[queue_id])
		//Write to linking RAM of previous tail.
		//MEMORY WRITE (WHICH MAY BE PERFORMED AFTER HDP AND TDP
		//WRITES)!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
		//Can be modeled as appending a BD with one memory write.
		//
		//FETCH_BD RETURNS BD DESCRIBING THIS!
		memory4[li_address] ≔ li

	tdp[queue_id] ≔ bd_address
*)
Definition write_register_d:
write_register_d internal_state address value =
  let bd_address = value in
  let queue_id = w2w (address - (QUEUE_MANAGER_BASE + QUEUE_D_0_OFFSET) >>> 16) : 8 word in
    if internal_state.qtp queue_id = 0w then
      let qhp = (queue_id =+ bd_address) internal_state.qhp in
      let qtp = (queue_id =+ bd_address) internal_state.qtp in
      let internal_state = internal_state with <| qhp := qhp; qtp := qtp |> in
        (internal_state, [])
    else
      let li_addresses = bd_address_to_li_addresses internal_state.registers (internal_state.qtp queue_id) in 
      let (next_bd_mr, next_bd_mr_index) = bd_mr_info internal_state.registers bd_address in
      let li_bytes = form_li_bytes next_bd_mr next_bd_mr_index (bd_address_to_internal_4lsb bd_address) F in
      let internal_state = internal_state with qhp := (queue_id =+ bd_address) internal_state.qhp in
      let address_bytes = ZIP (li_addresses, li_bytes) in
      let write_request = request_write address_bytes 0w in
        (internal_state, [write_request])
End

Definition bbb_usb_write_register:
bbb_usb_write_register internal_state address_bytes =
  let (addresses, bytes) = UNZIP address_bytes in
    if ~WORD_ALIGNED_ADDRESSES addresses \/ ~CONSECUTIVE_ADDRESSES addresses then
      (internal_state, [] : ((32, 8) interconnect_request_type list))
    else
      let address = HD addresses in
      let value = concat_word_list bytes in
        if TXGCR_ADDRESSES address then
          write_register_txgcr internal_state address value
        else if RXGCR_ADDRESSES address then
          write_register_rxgcr internal_state address value
        else if LRAM_ADDRESSES address then
          write_registers_lram internal_state address value
        else if QMEMCTRL_ADDRESSES address then
          write_register_qmemctrl internal_state address value
        else if QMEMRBASE_ADDRESSES address then
          write_register_qmemrbase internal_state address value
        else if SCHEDULER_ADDRESSES address then
          write_register_scheduler internal_state address value
        else if RXHPCRA_ADDRESSES address then
          write_register_rxhpcra internal_state address value
        else if RXHPCRB_ADDRESSES address then
          write_register_rxhpcrb internal_state address value
        else if QUEUE_D_ADDRESSES address then
          write_register_d internal_state address value
        else
          (internal_state, [])
End

val _ = export_theory();
