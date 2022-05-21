open HolKernel Parse boolLib bossLib stateTheory operationsTheory;

val _ = new_theory "write_properties";

(* Fetching BD write requests address only writable locations. *)
Definition FETCHING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES:
  FETCHING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel =
  !address_bytes tag addresses.
  SOME (request_write address_bytes tag) = channel.pending_accesses.requests.fetching_bd /\
  addresses = MAP FST address_bytes
  ==>
  EVERY (W memory) addresses
End

(* Updating BD requests are only for writing. *)
Definition UPDATING_BD_WRITE_REQUESTS_ONLY:
  UPDATING_BD_WRITE_REQUESTS_ONLY channel =
  !request.
    MEM request channel.pending_accesses.requests.updating_bd
    ==>
    ?address_bytes tag. request = request_write address_bytes tag
End

(* Updating BD write requests address only writable locations. *)
Definition UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES:
  UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel =
  !address_bytes tag addresses.
  MEM (request_write address_bytes tag) channel.pending_accesses.requests.updating_bd /\
  addresses = MAP FST address_bytes
  ==>
  EVERY (W memory) addresses
End

(* Transferring data write requests address only writable locations. *)
Definition TRANSFERRING_DATA_CHANNEL_REQUESTING_WRITE_ADDRESSES:
  TRANSFERRING_DATA_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel =
  !address_bytes tag addresses.
  MEM (request_write address_bytes tag) channel.pending_accesses.requests.transferring_data /\
  addresses = MAP FST address_bytes
  ==>
  EVERY (W memory) addresses
End

(* Writing back BD requests are only for writing. *)
Definition WRITING_BACK_BD_WRITE_REQUESTS_ONLY:
  WRITING_BACK_BD_WRITE_REQUESTS_ONLY channel =
  !request.
    MEM request channel.pending_accesses.requests.writing_back_bd
    ==>
    ?address_bytes tag. request = request_write address_bytes tag
End

(* Updating BD write requests address only writable locations. *)
Definition WRITING_BACK_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES:
  WRITING_BACK_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel =
  !address_bytes tag addresses.
  MEM (request_write address_bytes tag) channel.pending_accesses.requests.writing_back_bd /\
  addresses = MAP FST address_bytes
  ==>
  EVERY (W memory) addresses
End

(* All write requests of a DMA channel address writable locations. *)
Definition CHANNEL_REQUESTING_WRITE_ADDRESSES:
  CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel =
  !address_bytes tag addresses.
    MEM (request_write address_bytes tag) (channel_pending_requests channel.pending_accesses.requests) /\
    addresses = MAP FST address_bytes
    ==>
    EVERY (W memory) addresses
End

(* All write requests of all DMA channels (the complete DMA controller) address
 * writable locations.
 *)
Definition DMA_REQUESTING_WRITE_ADDRESSES:
  DMA_REQUESTING_WRITE_ADDRESSES device_characteristics memory device =
  !channel_state channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id /\
    channel_state = schannel device channel_id
    ==>
    CHANNEL_REQUESTING_WRITE_ADDRESSES device_characteristics.dma_characteristics.W memory channel_state
End

(* Write requests originating from CPU accessing DMA registers address writable
 * memory.
 *)
Definition REGISTER_REQUESTING_WRITE_ADDRESSES:
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device =
  !address_bytes tag.
    MEM (request_write address_bytes tag) device.dma_state.pending_register_related_memory_requests
    ==>
    EVERY (device_characteristics.dma_characteristics.W memory) (MAP FST address_bytes)
End

(* All write requests of of the I/O device/peripheral address writable
 * locations.
 *)
Definition DEVICE_REQUESTING_WRITE_ADDRESSES:
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device = (
  DMA_REQUESTING_WRITE_ADDRESSES device_characteristics memory device /\
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device
  )
End

Definition REQUEST_VALIDATION_WRITABLE:
  REQUEST_VALIDATION_WRITABLE W memory is_valid =
  !address_bytes tag.
    is_valid (request_write address_bytes tag) ==> EVERY (W memory) (MAP FST address_bytes)
End

val _ = export_theory();

