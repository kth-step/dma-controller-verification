open HolKernel Parse boolLib bossLib stateTheory operationsTheory;

val _ = new_theory "read_properties";

(* Fetching BD requests are only for reading. *)
Definition FETCHING_BD_READ_REQUESTS_ONLY:
  FETCHING_BD_READ_REQUESTS_ONLY channel =
  !request.
  SOME request = channel.pending_accesses.requests.fetching_bd
  ==>
  ?addresses tag. request = request_read addresses tag
End

(* Fetching BD read requests address only readable locations. *)
Definition FETCHING_BD_CHANNEL_REQUESTING_READ_ADDRESSES:
  FETCHING_BD_CHANNEL_REQUESTING_READ_ADDRESSES R memory channel =
  !addresses tag.
  SOME (request_read addresses tag) = channel.pending_accesses.requests.fetching_bd
  ==>
  EVERY (R memory) addresses
End

(* Updating BD read requests address only readable locations. *)
Definition UPDATING_BD_CHANNEL_REQUESTING_READ_ADDRESSES:
  UPDATING_BD_CHANNEL_REQUESTING_READ_ADDRESSES R memory channel =
  !addresses tag.
  MEM (request_read addresses tag) channel.pending_accesses.requests.updating_bd 
  ==>
  EVERY (R memory) addresses
End

(* Transferring data read requests address only readable locations. *)
Definition TRANSFERRING_DATA_CHANNEL_REQUESTING_READ_ADDRESSES:
  TRANSFERRING_DATA_CHANNEL_REQUESTING_READ_ADDRESSES R memory channel =
  !addresses tag.
  MEM (request_read addresses tag) channel.pending_accesses.requests.transferring_data
  ==>
  EVERY (R memory) addresses
End

(* Updating BD read requests address only readable locations. *)
Definition WRITING_BACK_BD_CHANNEL_REQUESTING_READ_ADDRESSES:
  WRITING_BACK_BD_CHANNEL_REQUESTING_READ_ADDRESSES R memory channel =
  !addresses tag.
  MEM (request_read addresses tag) channel.pending_accesses.requests.writing_back_bd 
  ==>
  EVERY (R memory) addresses
End

(* All read requests of a DMA channel address readable locations. *)
Definition CHANNEL_REQUESTING_READ_ADDRESSES:
  CHANNEL_REQUESTING_READ_ADDRESSES R memory channel =
  !addresses tag.
    MEM (request_read addresses tag) (channel_pending_requests channel.pending_accesses.requests)
    ==>
    EVERY (R memory) addresses
End

(* All read requests of all DMA channels (the complete DMA controller) address
 * readable locations.
 *)
Definition DMA_REQUESTING_READ_ADDRESSES:
  DMA_REQUESTING_READ_ADDRESSES device_characteristics memory device =
  !channel_state channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id /\
    channel_state = schannel device channel_id
    ==>
    CHANNEL_REQUESTING_READ_ADDRESSES device_characteristics.dma_characteristics.R memory channel_state
End

(* Read requests originating from CPU accessing DMA registers address readable
 * memory.
 *)
Definition REGISTER_REQUESTING_READ_ADDRESSES:
  REGISTER_REQUESTING_READ_ADDRESSES device_characteristics memory device =
  !addresses tag.
    MEM (request_read addresses tag) device.dma_state.pending_register_related_memory_requests
    ==>
    EVERY (device_characteristics.dma_characteristics.R memory) addresses
End

(* All read requests of of the I/O device/peripheral address readable locations.
 *)
Definition DEVICE_REQUESTING_READ_ADDRESSES:
  DEVICE_REQUESTING_READ_ADDRESSES device_characteristics memory device = (
  DMA_REQUESTING_READ_ADDRESSES device_characteristics memory device /\
  REGISTER_REQUESTING_READ_ADDRESSES device_characteristics memory device
  )
End

Definition REQUEST_VALIDATION_READABLE:
  REQUEST_VALIDATION_READABLE R memory is_valid =
  !addresses tag.
    is_valid (request_read addresses tag) ==> EVERY (R memory) addresses
End

val _ = export_theory();

