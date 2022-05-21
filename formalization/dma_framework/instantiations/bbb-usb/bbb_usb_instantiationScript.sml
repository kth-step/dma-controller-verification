open HolKernel Parse boolLib bossLib;
open stateTheory bbb_usb_txTheory bbb_usb_rxTheory bbb_usb_queue_txTheory bbb_usb_queue_rxTheory;
open bbb_usb_schedulerTheory bbb_usb_registersTheory;

val _ = new_theory "bbb_usb_instantiation";

Definition tx_verification:
tx_verification queue_id = <|
  bds_to_fetch := tx_bds_to_fetch queue_id;
  update_bd_addresses := tx_update_bd_addresses;
  bd_transfer_ras_was := tx_bd_transfer_ras_was;
  write_back_bd_addresses := tx_write_back_bd_addresses queue_id
|>
End

Definition rx_verification:
rx_verification queue_id = <|
  bds_to_fetch := rx_bds_to_fetch queue_id;
  update_bd_addresses := rx_update_bd_addresses;
  bd_transfer_ras_was := rx_bd_transfer_ras_was;
  write_back_bd_addresses := rx_write_back_bd_addresses queue_id
|>
End

Definition bbb_usb_verification:
bbb_usb_verification queue_id =
  if queue_id <=+ 31w : 8 word then
    SOME (rx_verification queue_id)
  else if 32w : 8 word <=+ queue_id /\ queue_id <=+ 91w : 8 word then
    SOME (tx_verification queue_id)
  else
    NONE
End

Definition tx_operation:
tx_operation (queue_id : 8 word) = <|
  fetch_bd_addresses := tx_fetch_bd_addresses queue_id;
  fetch_bd := tx_fetch_bd queue_id;
  update_bd := tx_update_bd;
  process_replies_generate_requests := tx_process_replies_generate_requests queue_id;
  write_back_bd := tx_write_back_bd queue_id
|>
End

Definition rx_operation:
rx_operation (queue_id : 8 word) = <|
  fetch_bd_addresses := rx_fetch_bd_addresses queue_id;
  fetch_bd := rx_fetch_bd queue_id;
  update_bd := rx_update_bd;
  process_replies_generate_requests := rx_process_replies_generate_requests;
  write_back_bd := rx_write_back_bd queue_id
|>
End

Definition bbb_usb_operation:
bbb_usb_operation queue_id =
  if queue_id <=+ 31w : 8 word then
    SOME (rx_operation queue_id)
  else if 32w : 8 word <=+ queue_id /\ queue_id <=+ 91w : 8 word then
    SOME (tx_operation queue_id)
  else NONE
End

Definition bbb_usb_dma_characteristics:
bbb_usb_dma_characteristics = <|
  bd_location := external;
  (* Simple example. addresses 0 and 1 are readable and addresses 1 and 2 are writable. *)
  R := (\(memory : 32 word -> 8 word) (address : 32 word). address = 0w \/ address = 1w);
  W := (\(memory : 32 word -> 8 word) (address : 32 word). address = 1w \/ address = 2w);
  scheduler := bbb_usb_dma_scheduler;
  register_read := bbb_usb_read_register;
  register_write := bbb_usb_write_register;
  process_register_related_memory_replies := bbb_usb_process_register_related_memory_replies;
  scratchpad_addresses := bbb_usb_scratchpad_addresses;
  DMA_REGISTER_ADDRESSES := bbb_usb_DMA_REGISTER_ADDRESSES;
  max_index  := 91w : 8 word;
  verification := bbb_usb_verification;
  operation := bbb_usb_operation
|>
End

(* Instantiation of the USB DMA controller on BeagleBone Black.
 *)
Definition bbb_usb_device_characteristics:
bbb_usb_device_characteristics = <|
  device_scheduler := bbb_usb_device_scheduler;
  function_characteristics := NONE;                            (* USB features are not considered. *)
  dma_characteristics := bbb_usb_dma_characteristics
|>
End

val _ = export_theory();

