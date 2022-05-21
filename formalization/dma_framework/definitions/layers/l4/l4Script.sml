open HolKernel Parse boolLib bossLib stateTheory concreteTheory operationsTheory;

val _ = new_theory "l4";

(* The layer 4 model describes the general operation of DMA controllers. The
 * difference from the layer 3 model is that no checks are made when there is a
 * possibility to overwrite a BD to fetch.
 *)

Definition fetching_bd_l4:
  fetching_bd_l4 device_characteristics channel_id internal_state channel =
    if INTERNAL_BDS device_characteristics then
      fetching_bd_fetch_bd_concrete (coperation device_characteristics channel_id).fetch_bd internal_state channel NONE
    else
      if IS_NONE channel.pending_accesses.replies.fetching_bd then
        let (addresses, tag) = (coperation device_characteristics channel_id).fetch_bd_addresses internal_state in
          (internal_state, fetching_bd_set_request channel addresses tag)
      else
        let reply = channel.pending_accesses.replies.fetching_bd in
        let channel = fetching_bd_clear_reply channel in
          fetching_bd_fetch_bd_concrete (coperation device_characteristics channel_id).fetch_bd internal_state channel reply
End

Definition updating_bd_l4:
  updating_bd_l4 device_characteristics channel_id internal_state channel =
    case channel.queue.bds_to_update of
    | [] => (internal_state, channel)
    | bd_ras_was::bd_ras_wass =>
      let (internal_state, write_address_bytes, tag, update_status) = (coperation device_characteristics channel_id).update_bd internal_state bd_ras_was in
      let channel = updating_bd_update_qs update_status channel bd_ras_was bd_ras_wass in
      if INTERNAL_BDS device_characteristics then
        (internal_state, channel)
      else
        (internal_state, updating_bd_append_request channel write_address_bytes tag)
End

Definition transferring_data_l4:
transferring_data_l4 device_characteristics channel_id internal_state channel =
  case channel.queue.bds_to_process of
    [] => (internal_state, channel)
  | (bd, bd_ras, bd_was)::bd_ras_wass =>
    let (internal_state, channel, new_requests, complete) = transferring_data_replies_requests channel.pending_accesses.replies.transferring_data (coperation device_characteristics channel_id).process_replies_generate_requests internal_state channel bd in
    let channel = if complete then transferring_data_update_qs channel (bd, bd_ras, bd_was) bd_ras_wass else channel in
      (internal_state, transferring_data_append_requests channel new_requests)
End

Definition writing_back_bd_l4:
  writing_back_bd_l4 device_characteristics channel_id environment internal_state channel =
    let (internal_state, write_address_bytes, tag, released_bd_ras_wass) = (coperation device_characteristics channel_id).write_back_bd environment internal_state channel.queue.bds_to_write_back in
    let channel = writing_back_bd_remove_released_bds channel released_bd_ras_wass in
      if INTERNAL_BDS device_characteristics then
        (internal_state, channel)
      else
        (internal_state, writing_back_bd_append_request channel write_address_bytes tag)
End

Definition channel_operation_case_l4:
  (channel_operation_case_l4 fetch_bd      device_characteristics channel_id environment internal_state channel = fetching_bd_l4       device_characteristics channel_id             internal_state channel) /\
  (channel_operation_case_l4 update_bd     device_characteristics channel_id environment internal_state channel = updating_bd_l4       device_characteristics channel_id             internal_state channel) /\
  (channel_operation_case_l4 transfer_data device_characteristics channel_id environment internal_state channel = transferring_data_l4 device_characteristics channel_id             internal_state channel) /\
  (channel_operation_case_l4 write_back_bd device_characteristics channel_id environment internal_state channel = writing_back_bd_l4   device_characteristics channel_id environment internal_state channel)
End

Definition channel_operation_l4:
  channel_operation_l4                                                            device_characteristics channel_id dma_channel_operation memory environment internal_state channel =
  let (internal_state, channel) = channel_operation_case_l4 dma_channel_operation device_characteristics channel_id                              environment internal_state channel in
    (internal_state, channel)
End

Definition internal_device_operation_l4:
  internal_device_operation_l4 (device_characteristics :
                                  ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type) environment device_state =
  internal_device_operation device_characteristics channel_operation_l4 (NONE : 'interconnect_address_width memory_type option) environment device_state
End

Definition dma_pending_requests_l4:
  dma_pending_requests_l4 device_characteristics device_state =
  dma_pending_requests    device_characteristics device_state
End

Definition dma_request_served_l4:
  dma_request_served_l4 device_characteristics device_state serviced_request =
  dma_request_served    device_characteristics device_state serviced_request
End

Definition is_valid_l4:
  is_valid_l4 request = T
End

Definition device_register_read_l4:
  device_register_read_l4 device_characteristics             device_state addresses =
  device_register_read    device_characteristics is_valid_l4 device_state addresses
End

Definition device_register_write_l4:
  device_register_write_l4 device_characteristics                  device_state address_bytes =
  device_register_write    device_characteristics is_valid_l4 NONE device_state address_bytes
End

Inductive device_transitions_l4:
(* Internal transition:
 * internal_device_operation_l4 device_characteristics environment device1 = device2
 * ---------------------------------------------------------------------------------
 * device1 -->internal_operation device2
 *)
(!device1 device2 device_characteristics environment memory.
  (internal_device_operation_l4 device_characteristics environment device1 = device2)
  ==>
  device_transition_l4 device_characteristics device1 (memory, device_internal_operation environment) device2) /\



(* Device reads memory:
 * (request_read (MAP FST address_bytes) tag) ∈ dma_pending_requests_l4 device_characteristics device1
 * dma_request_served_l4 device_characteristics device1 (SOME bytes, request_read (MAP FST address_bytes)) = device2
 * -----------------------------------------------------------------------------------------------------------------
 * device1 -->(memory_read address_bytes) device2
 *)
(!device1 device2 device_characteristics address_bytes tag memory.
  MEM (request_read (MAP FST address_bytes) tag) (dma_pending_requests_l4 device_characteristics device1) /\
  (dma_request_served_l4 device_characteristics device1 (MAP SND address_bytes, request_read (MAP FST address_bytes) tag) = device2)
  ==>
  device_transition_l4 device_characteristics device1 (memory, device_memory_read address_bytes) device2) /\



(* Device writes memory:
 * (request_write address_bytes tag) ∈ dma_pending_requests_l4 device_characteristics device1
 * dma_request_served_l4 device_characteristics device1 (NONE, request_write address_bytes tag) = device2
 * ------------------------------------------------------------------------------------------------------
 * device1 -->(memory_write address_bytes) device2
 *)
(!device1 device2 device_characteristics address_bytes tag memory.
  MEM (request_write address_bytes tag) (dma_pending_requests_l4 device_characteristics device1) /\
  (dma_request_served_l4 device_characteristics device1 ([], request_write address_bytes tag) = device2)
  ==>
  device_transition_l4 device_characteristics device1 (memory, device_memory_write address_bytes) device2) /\



(* CPU reads register:
 * device_register_read_l4 device1 (MAP FST address_bytes) = (device2, MAP SND address_bytes)
 * MAP FST address_bytes ⊆ DMA_REGISTER_ADDRESSES ∪ FUNCTION_REGISTER_ADDRESSES
 * ------------------------------------------------------------------------------------------
 * device1 -->(register_read address_bytes) device2
 *)
(!device1 device2 device_characteristics cpu_address_bytes dma_address_bytes memory.
  (device_register_read_l4 device_characteristics device1 (MAP FST cpu_address_bytes) = (device2, dma_address_bytes, MAP SND cpu_address_bytes)) /\
  (EVERY device_characteristics.dma_characteristics.DMA_REGISTER_ADDRESSES (MAP FST cpu_address_bytes) \/
   (IS_SOME device_characteristics.function_characteristics /\
    EVERY (THE device_characteristics.function_characteristics).FUNCTION_REGISTER_ADDRESSES (MAP FST cpu_address_bytes)))
  ==>
  device_transition_l4 device_characteristics device1 (memory, device_register_read (cpu_address_bytes, dma_address_bytes)) device2) /\



(* CPU writes register:
 * device_register_write_l4 device1 address_bytes = device2
 * MAP FST address_bytes ⊆ DMA_REGISTER_ADDRESSES ∪ FUNCTION_REGISTER_ADDRESSES
 * ----------------------------------------------------------------------------
 * device1 -->(register_write address_bytes) device2
 *)
(!device1 device2 device_characteristics cpu_address_bytes dma_address_bytes memory.
  (device_register_write_l4 device_characteristics device1 cpu_address_bytes = (device2, dma_address_bytes)) /\
  (EVERY device_characteristics.dma_characteristics.DMA_REGISTER_ADDRESSES (MAP FST cpu_address_bytes) \/
   (IS_SOME device_characteristics.function_characteristics /\
    EVERY (THE device_characteristics.function_characteristics).FUNCTION_REGISTER_ADDRESSES (MAP FST cpu_address_bytes)))
  ==>
  device_transition_l4 device_characteristics device1 (memory, device_register_write (cpu_address_bytes, dma_address_bytes)) device2) /\



(* Memory is written by the CPU (or another device; the fourth layer does not
 * react to this since there is no abstract BD queue):
 *                         -
 * ----------------------------------------------------
 * device -->external_memory_write memory device
 *)
(!(device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
  device_characteristics memory.
   device_transition_l4 device_characteristics device (memory, external_bds_appended (* : 'interconnect_address_width device_transition_labels_type*)) device)
End

val _ = export_theory();

