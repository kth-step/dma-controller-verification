open HolKernel Parse boolLib bossLib;
open stateTheory;

val _ = new_theory "bbb_usb_state";

Datatype: endpoint_state_tx_type =
  tx_fetch_bd
| tx_transfer_data
| tx_write_back_sop_bd1
| tx_write_back_sop_bd2
| tx_write_back_sop_bd3
| tx_write_back_sop_bd4
End

Datatype: endpoint_tx_type = <|
  state : endpoint_state_tx_type;
  sop : bool -> bool;		(* Each TX endpoint manages 2 channels; sop_li exists for two channels therefore, identified by LSB. *)
  sop_li : bool -> 32 word;	(* Each TX endpoint manages 2 channels; sop_li exists for two channels therefore, identified by LSB. *)
  number_of_data_bytes_read : 22 word;
  current_queue_id: 8 word;
|>
End

Datatype: endpoint_state_rx_type =
  rx_fetch_bd
| rx_transfer_data
| rx_write_back_current_bd
| rx_write_back_previous_bd
| rx_write_back_sop_bd1
| rx_write_back_sop_bd2
| rx_write_back_sop_bd3
| rx_write_back_sop_bd4
| rx_write_back_sop_bd5
End

Datatype: endpoint_rx_type = <|
  state : endpoint_state_rx_type;
  next_descriptor_pointer : 32 word;
  number_of_written_bytes_of_dma_packet : 15 word;
  sop_bd_queue_id : 8 word; (* Used by the scheduler to identify the channel with the SOP BD, when in state write_back_sop_bd1. *)
  sop_bd_ra : 32 word;	(* Used by write back to find the SOP bd among the bds to write back. *)
  number_of_written_bytes_to_buffer : 32 word;
  bd_index : 2 word;
  usb_packet : 8 word list;
  current_queue_id : 8 word;
  previous_queue_id : 8 word;
  write_back_bd_queue_id : 8 word;
  start_buffer_address : 32 word;
|>
End

Definition tag:
  tag = 0w : 8 word
End

Datatype: registers_type = <|
  TXGCR : 5 word -> 32 word;
  RXGCR : 5 word -> 32 word;
  LRAM0BASE : 30 word;
  LRAM1BASE : 30 word;
  LRAM0SIZE : 14 word;
  QMEMCTRL : 3 word -> 32 word;
  QMEMRBASE : 3 word -> 27 word;
  WORD : 6 word -> 32 word;
  DMA_SCHED_CTRL : 32 word;
  RXHPCRA : 5 word -> 32 word; (* 0 argument gives RXHPCRA for endpoint 0, etc. *)
  RXHPCRB : 5 word -> 32 word; (* 0 argument gives RXHPCRB for endpoint 0, etc. *)
|>
End

Datatype: tx_rx_type =
  tx
| rx
End

Datatype: internal_state_type = <|
  registers : registers_type;
  qhp : 8 word -> 32 word;
  qtp : 8 word -> 32 word;
  chp : 8 word -> 32 word;
  ctp : 8 word -> 32 word;
  scheduler_index : 8 word;
  cdma_sreq : bool;
  current_endpoint_txrx: tx_rx_type;
  current_rx_endpoint_id : 5 word;
  endpoints_tx : 5 word -> endpoint_tx_type;
  endpoints_rx : 5 word -> endpoint_rx_type;
  endpoint_previous_state_tx : endpoint_state_tx_type;
  endpoint_previous_state_rx : endpoint_state_rx_type;
  completion_queue_write_backs : (32 word # 8 word list) list; (* [..., (bd_address, li_bytes), ...] *)
  write_back_popped_bds : 32 word list; (* [..., bd_address, ...] *)
|>
End

Datatype: environment_type = <|
  CPPI_FIFO_FULL : 5 word -> bool;
  CPPI_FIFO_EMPTY : 5 word -> bool;
  endpoint_tx_queue_id : 1 word; (* Odd or even queue. *)
  source_tag_channel : 6 word;
  source_tag_sub_channel : 5 word;
  packet_error : 1 word;
  type_of_packet : 5 word;
  zero_length_packet_indicator : 1 word;
  new_usb_packet : 8 word list;
  (* True if and only if an internal operation shall be performed with higher
   * priority than processing memory reply due to register write.
   *)
  DMA_OPERATION : bool
|>
End

Definition MAXIMUM_NUMBER_OF_BDS:
MAXIMUM_NUMBER_OF_BDS = 65536
End

Definition NUMBER_OF_QUEUES:
NUMBER_OF_QUEUES = 92
End

val _ = export_theory();

