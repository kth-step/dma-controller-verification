open HolKernel Parse boolLib bossLib bd_queuesTheory abstractTheory access_propertiesTheory;

val _ = new_theory "l1";

(* All functions with a name starting with dma are interface functions. *)



(* The layer 1 model describes an abstract isolated general DMA controller.
 * Fetches BDs from an abstract immutable BD queue that is part of the framework
 * state. Checks that memory requests only address readable and writable memory.
 * That is:
 *   •BDs to fetch from the BD queue are immutable.
 *   •Checks that each memory read request addresses readable memory.
 *   •Checks that each memory write request addresses writable memory.
 *
 * An important property of the layer 1 model is that, once a BD has been added
 * to the BD queue to fetch, such a BD can only be modified if predicted by the
 * instantiated definition of bds_to_fetch. bds_to_fetch must give the BDs as
 * interpreted by the DMA controller when the BD fetches them. This requirement
 * on the definition of bds_to_fetch affects the instantiated functions
 * update_bd and bd_write_back, in the sense that the framework does not allow
 * unpredicted/unexpected/not considered modifications of BDs to fetch. The
 * framework is defined such that if a BD is updated or written back, then it is
 * by design of the DMA controller, and predicted/expected/considered in the
 * definition of bds_to_fetch, and not as an unpredicted/unexpected/not
 * considered side effect of BD updates and write backs.
 *
 * The framework can handle unpredicted/unexpected/not considered BD updates and
 * write backs (e.g. size of a received frame for a NIC), if such updates and
 * write backs do not affect the memory accesses specified by BDs.
 *)



(* Input:
 * -memory: External memory.
 * -internal_state: Internal DMA state of instantiation.
 * -bd_location: Locations of BDs of instantiation (internal or external memory).
 * -channel_state: Framework DMA channel state.
 * -operation: Instantiation of DMA channel operation.
 *
 * Output:
 * -Internal DMA controller state.
 * -DMA channel state.
 *
 * Cannot have multiple pending requests and replies as the BD processing logic
 * cannot advance until the complete BD has been fetched, which means that it
 * must wait until the pending request has been replied. The only scenario in
 * which multiple pending requests make sense is when multiple interconnect ports
 * are used.
 *
 * For externally stored BDs, if there is a pending reply, then it is processed,
 * otherwise one is generated.
 *)
Definition fetching_bd_l1:
  fetching_bd_l1 device_characteristics channel_id memory internal_state channel =
    if INTERNAL_BDS device_characteristics then
      fetching_bd_fetch_bd_abstract (coperation device_characteristics channel_id).fetch_bd internal_state channel NONE
    else
      if IS_NONE channel.pending_accesses.replies.fetching_bd then
        let (fetch_bd_addresses, tag) = (coperation device_characteristics channel_id).fetch_bd_addresses internal_state in
        let fetch_bd_read_addresses = bd_read_addresses channel.queue.bds_to_fetch fetch_bd_addresses in
          if EVERY (device_characteristics.dma_characteristics.R memory) fetch_bd_read_addresses then
            (internal_state, fetching_bd_set_request channel fetch_bd_read_addresses tag)
          else
            (internal_state, channel)
      else
        let reply = channel.pending_accesses.replies.fetching_bd in
        let channel = fetching_bd_clear_reply channel in
          fetching_bd_fetch_bd_abstract (coperation device_characteristics channel_id).fetch_bd internal_state channel reply
End

(* Updates a BD. If in external memory, the addresses must be writable.
 *)
Definition updating_bd_l1:
  updating_bd_l1 device_characteristics channel_id memory internal_state channel =
  case channel.queue.bds_to_update of
  | [] => (internal_state, channel)
  | (bd, bd_ras, bd_was)::bd_ras_wass =>
    let bd_write_addresses = (cverification device_characteristics channel_id).update_bd_addresses internal_state (bd, bd_ras, bd_was) in
      if CONSISTENT_BD_WRITE device_characteristics memory internal_state bd_write_addresses then
        let (internal_state, write_address_bytes, tag, update_status) = (coperation device_characteristics channel_id).update_bd internal_state (bd, bd_ras, bd_was) in
        let channel = updating_bd_update_qs update_status channel (bd, bd_ras, bd_was) bd_ras_wass in
          if INTERNAL_BDS device_characteristics then
            (internal_state, channel)
          else
            if EVERY (device_characteristics.dma_characteristics.W memory) bd_write_addresses then
              (internal_state, updating_bd_append_request channel write_address_bytes tag)
            else
              (internal_state, channel)
      else
        (internal_state, channel)
End

(* If there are pending replies, then they are given to the instantiation.
 * Then the instantiation is peeked whether it has any requests left for the
 * currently processed BD. If requests remain, then they are added to the pending
 * requests list. If no requests remain, then the currently processed BD is moved
 * from the bds_to_process queue to the bds_to_write_back queue.
 *
 * For copy DMA channels, this definition leads to alternating request issuing
 * and reply processing. Consecutive issuing or processing is simulated by the
 * scheduler postponing the invocation of transferring_data, enabling more
 * requests/replies to pile up in the internal state/pending reply queue.
 *
 * That is, transferring data works as follows:
 * 1. Process replies as soon as possible
 * 2. Issue requests as soon as possible.
 * Which describes the scheme of no waiting, which fits performance, as a write
 * (2) due to a read (1) (i.e. a copy) is completed as soon as possible. This
 * means that internal processing of a read in several operations and then
 * issuing writes are not possible, as that would lead to NONE being returned by
 * generate_request.
 *)
Definition transferring_data_l1:
transferring_data_l1 device_characteristics channel_id memory internal_state channel =
  case channel.queue.bds_to_process of
    [] => (internal_state, channel)
  | (bd, bd_ras, bd_was)::bd_ras_wass =>
    let (internal_state, channel, new_requests, complete) = transferring_data_replies_requests channel.pending_accesses.replies.transferring_data (coperation device_characteristics channel_id).process_replies_generate_requests internal_state channel bd in
    let channel = if complete then transferring_data_update_qs channel (bd, bd_ras, bd_was) bd_ras_wass else channel in
      if CONSISTENT_DMA_WRITE device_characteristics memory internal_state (FLAT (MAP request_to_write_addresses new_requests)) then
        if READABLE_WRITABLE device_characteristics.dma_characteristics.R device_characteristics.dma_characteristics.W memory new_requests then
          (internal_state, transferring_data_append_requests channel new_requests)
        else
          (internal_state, channel)
      else
        (internal_state, channel)
End

(* Issues a write request if it identifies writable locations, and removes
 * released BDs from the BDs to write back queue.
 *)
Definition writing_back_bd_l1:
  writing_back_bd_l1 device_characteristics channel_id memory environment internal_state channel =
  let write_addresses = (cverification device_characteristics channel_id).write_back_bd_addresses environment internal_state channel.queue.bds_to_write_back in
    if CONSISTENT_BD_WRITE device_characteristics memory internal_state write_addresses then
      let (internal_state, write_address_bytes, tag, released_bd_ras_wass) = (coperation device_characteristics channel_id).write_back_bd environment internal_state channel.queue.bds_to_write_back in
      let channel = writing_back_bd_remove_released_bds channel released_bd_ras_wass in
        if INTERNAL_BDS device_characteristics then
          (internal_state, channel)
        else
          if EVERY (device_characteristics.dma_characteristics.W memory) write_addresses then
            (internal_state, writing_back_bd_append_request channel write_address_bytes tag)
          else
            (internal_state, channel)
    else
      (internal_state, channel)
End



(*Internal DMA controller operation********************************************)

Definition channel_operation_case_l1:
  (channel_operation_case_l1 fetch_bd      device_characteristics channel_id memory environment internal_state channel = fetching_bd_l1       device_characteristics channel_id memory             internal_state channel) /\
  (channel_operation_case_l1 update_bd     device_characteristics channel_id memory environment internal_state channel = updating_bd_l1       device_characteristics channel_id memory             internal_state channel) /\
  (channel_operation_case_l1 transfer_data device_characteristics channel_id memory environment internal_state channel = transferring_data_l1 device_characteristics channel_id memory             internal_state channel) /\
  (channel_operation_case_l1 write_back_bd device_characteristics channel_id memory environment internal_state channel = writing_back_bd_l1   device_characteristics channel_id memory environment internal_state channel)
End

Definition channel_operation_l1:
  (channel_operation_l1                                                           device_characteristics channel_id dma_channel_operation NONE          environment internal_state channel = (internal_state, channel)) /\
  (channel_operation_l1                                                           device_characteristics channel_id dma_channel_operation (SOME memory) environment internal_state channel =
  let (internal_state, channel) = channel_operation_case_l1 dma_channel_operation device_characteristics channel_id                             memory  environment internal_state channel in
    (internal_state, channel))
End

(* An internal operation of the device with a DMA controller at the highest
 * abstraction layer.
 *)
Definition internal_device_operation_l1:
  internal_device_operation_l1 device_characteristics                            memory  environment device =
  internal_device_operation    device_characteristics channel_operation_l1 (SOME memory) environment device
End

(*End of internal DMA controller operation************************************)



(* Returns all pending interconnect requests. *)
Definition dma_pending_requests_l1:
  dma_pending_requests_l1 device_characteristics device =
  dma_pending_requests    device_characteristics device
End

(* Removes the pending request whose tag matches that of serviced_request.
 *)
Definition dma_request_served_l1:
  dma_request_served_l1 device_characteristics device serviced_request =
  dma_request_served    device_characteristics device serviced_request
End

Definition is_valid_l1:
is_valid_l1 = is_valid_readable_writable
End

Definition device_register_read_l1:
  device_register_read_l1 device_characteristics memory device addresses =
  let is_valid = is_valid_l1 device_characteristics memory device in
    device_register_read device_characteristics is_valid device addresses
End

(* -memory: memory used to append BDs when a DMA channel is started or just for
 *  appending BDs.
 * -device: The state of the device to which the register write is performed.
 * -address_bytes: The addresses and associated bytes to be written.
 *)
Definition device_register_write_l1:
  device_register_write_l1 device_characteristics memory device address_bytes =
  let is_valid = is_valid_l1 device_characteristics memory device in
    device_register_write    device_characteristics is_valid (SOME memory) device address_bytes
End

(*Append BDs if BDs are appended by writing external memory********************)

(* -controller1: State of the DMA controller at the time when external memory is
 *  written causing BDs to be appended.
 * -memory2: State of the memory resulting from the external writing causing BDs
 *  to be appended.
 *)
Definition append_external_abstract_bds_l1:
  append_external_abstract_bds_l1  device_characteristics memory device =
  if EXTERNAL_BDS device_characteristics then
    dma_append_external_abstract_bds device_characteristics memory device
  else
    device
End

(*End of append BDs if BDs are appended by writing external memory*************)







(* Transition system.
 *
 * NOTE: memory is a separate component included in all labels. The reason for
 * extracting memory from the operation identifier is to be able to relate the
 * memory component to the invariant without considering the specific label
 * identifying the operation of the device.
 *
 * NOTE: The memory component identifies the state of the memory when the device
 * performs its transition, and acts as an external parameter
 * affecting/restricting the behavior of the transition system of the device.
 *)
Inductive device_transitions_l1:
(* Internal transition:
 * internal_device_operation_l1 device_characteristics memory environment device1 = device2
 * ----------------------------------------------------------------------------------------
 * device1 -->internal_operation device2
 *)
(!device1 device2 device_characteristics memory.
  (internal_device_operation_l1 device_characteristics memory environment device1 = device2)
  ==>
  device_transition_l1 device_characteristics device1 (memory, device_internal_operation environment) device2) /\



(* Device reads memory:
 * (request_read (MAP FST address_bytes) tag) ∈ dma_pending_requests_l1 device_characteristics device1
 * dma_request_served_l1 device_characteristics device1 (SOME (MAP SND address_bytes), request_read (MAP FST address_bytes) tag) = device2
 * ---------------------------------------------------------------------------------------------------------------------------------------
 * device1 -->(memory_read address_bytes) device2
 *)
(!device1 device2 device_characteristics address_bytes tag memory.
  MEM (request_read (MAP FST address_bytes) tag) (dma_pending_requests_l1 device_characteristics device1) /\
  (dma_request_served_l1 device_characteristics device1 (MAP SND address_bytes, request_read (MAP FST address_bytes) tag) = device2)
  ==>
  device_transition_l1 device_characteristics device1 (memory, device_memory_read address_bytes) device2) /\



(* Device writes memory:
 * (request_write address_bytes tag) ∈ dma_pending_requests_l1 device_characteristics device1
 * dma_request_served_l1 device_characteristics device1 (NONE, request_write address_bytes tag) = device2
 * ------------------------------------------------------------------------------------------------------
 * device1 -->(memory_write address_bytes) device2
 *)
(!device1 device2 device_characteristics address_bytes tag memory.
  MEM (request_write address_bytes tag) (dma_pending_requests_l1 device_characteristics device1) /\
  (dma_request_served_l1 device_characteristics device1 ([], request_write address_bytes tag) = device2)
  ==>
  device_transition_l1 device_characteristics device1 (memory, device_memory_write address_bytes) device2) /\



(* CPU reads register:
 * device_register_read_l1 device1 (MAP FST address_bytes) = (device2, MAP SND address_bytes)
 * MAP FST address_bytes ⊆ DMA_REGISTER_ADDRESSES ∪ FUNCTION_REGISTER_ADDRESSES
 * ------------------------------------------------------------------------------------------
 * device1 -->(register_read address_bytes) device2
 *)
(!device1 device2 device_characteristics cpu_address_bytes dma_address_bytes memory.
  (device_register_read_l1 device_characteristics memory device1 (MAP FST cpu_address_bytes) = (device2, dma_address_bytes, MAP SND cpu_address_bytes)) /\
  (EVERY device_characteristics.dma_characteristics.DMA_REGISTER_ADDRESSES (MAP FST cpu_address_bytes) \/
   (IS_SOME device_characteristics.function_characteristics /\
    EVERY (THE device_characteristics.function_characteristics).FUNCTION_REGISTER_ADDRESSES (MAP FST cpu_address_bytes)))
  ==>
  device_transition_l1 device_characteristics device1 (memory, device_register_read (cpu_address_bytes, dma_address_bytes)) device2) /\



(* CPU writes register:
 * device_register_write_l1 memory device1 address_bytes = device2
 * MAP FST address_bytes ⊆ DMA_REGISTER_ADDRESSES ∪ FUNCTION_REGISTER_ADDRESSES
 * ----------------------------------------------------------------------------
 * device1 -->(register_write address_bytes) device2
 *)
(!device1 device2 device_characteristics cpu_address_bytes dma_address_bytes memory.
  (device_register_write_l1 device_characteristics memory device1 cpu_address_bytes = (device2, dma_address_bytes)) /\
  (EVERY device_characteristics.dma_characteristics.DMA_REGISTER_ADDRESSES (MAP FST cpu_address_bytes) \/
   (IS_SOME device_characteristics.function_characteristics /\
    EVERY (THE device_characteristics.function_characteristics).FUNCTION_REGISTER_ADDRESSES (MAP FST cpu_address_bytes)))
  ==>
  device_transition_l1 device_characteristics device1 (memory, device_register_write (cpu_address_bytes, dma_address_bytes)) device2) /\



(* Memory is written by the CPU or another device, causing memory to transition
 * from memory1 to memory2. This necessitates the first layer to potentially
 * append new abstract BDs to the abstract BD queue, which occurs only if BDs
 * are appended as a consequence of the memory write; e.g. writing pointers or
 * incrementing counter/length fields. If the appending of BDs is done by
 * writing DMA registers, then no BDs get appended when writing memory. Note
 * that due to the definition of layer 1, BDs cannot be modified once appended
 * to the BD queue.
 *
 * append_external_abstract_bds_l1 device_characteristics memory2 device1 = device2
 * --------------------------------------------------------------------------------
 * device -->external_memory_write addresses bytes device
 *)
(!device1 device2 device_characteristics memory2.
  (append_external_abstract_bds_l1 device_characteristics memory2 device1 = device2)
  ==>
  device_transition_l1 device_characteristics device1 (memory2, external_bds_appended) device2)
End

val _ = export_theory();

