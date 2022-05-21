open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory operationsTheory read_propertiesTheory write_propertiesTheory invariant_l2Theory;

val _ = new_theory "invariant_l3";

Definition EXTERNAL_BD_ADDRESSES:
EXTERNAL_BD_ADDRESSES device_characteristics channel_id memory internal_state channel =
!bytes tag1 tag2 addresses.
  EXTERNAL_BDS device_characteristics /\
  SOME (bytes, tag1) = channel.pending_accesses.replies.fetching_bd /\
  (addresses, tag2) = (coperation device_characteristics channel_id).fetch_bd_addresses internal_state
  ==>
  tag1 = tag2 /\
  MAP memory addresses = bytes
End

Definition channel_bd_queues:
channel_bd_queues device_characteristics channel_id memory internal_state channel =
  let bds_to_fetch = MAP FST ((cverification device_characteristics channel_id).bds_to_fetch memory internal_state) in
  let bds_to_update = channel.queue.bds_to_update in
  let bds_to_process = channel.queue.bds_to_process in
  let bds_to_write_back = channel.queue.bds_to_write_back in
    bds_to_fetch ++ bds_to_update ++ bds_to_process ++ bds_to_write_back
End

Definition INTERNAL_BD_FETCH:
INTERNAL_BD_FETCH device_characteristics channel_id internal_state1 internal_state2 bd = (
  INTERNAL_BDS device_characteristics
  ==>
  ?update_flag.
    (internal_state2, SOME (bd, update_flag)) = (coperation device_characteristics channel_id).fetch_bd internal_state1 NONE
)
End

Definition EXTERNAL_BD_FETCH:
EXTERNAL_BD_FETCH device_characteristics memory channel_id internal_state1 channel1 internal_state2 bd = (
  EXTERNAL_BDS device_characteristics
  ==>
  ?addresses tag bytes update_flag.
    (addresses, tag) = (coperation device_characteristics channel_id).fetch_bd_addresses internal_state1 /\
    SOME (bytes, tag) = channel1.pending_accesses.replies.fetching_bd /\
    MAP memory addresses = bytes /\
    (internal_state2, SOME (bd, update_flag)) = (coperation device_characteristics channel_id).fetch_bd internal_state1 channel1.pending_accesses.replies.fetching_bd
)
End

Definition CHANNEL_SET:
CHANNEL_SET l = {e | MEM e l}
End

Definition CHANNEL_BD_QUEUES_SUBSET:
CHANNEL_BD_QUEUES_SUBSET device_characteristics memory device1 device2 =
!channel_id channel1 channel2 channel_bd_queues1 channel_bd_queues2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channel1 = schannel device1 channel_id /\
  channel2 = schannel device2 channel_id /\
  channel_bd_queues1 = channel_bd_queues device_characteristics channel_id memory device1.dma_state.internal_state channel1 /\
  channel_bd_queues2 = channel_bd_queues device_characteristics channel_id memory device2.dma_state.internal_state channel2
  ==>
  CHANNEL_SET channel_bd_queues2 SUBSET CHANNEL_SET channel_bd_queues1
End






(* BDs to fetch of each channel are disjoint. *)
Definition INVARIANT_BDS_TO_FETCH_DISJOINT:
INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device =
!bds_to_fetch channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory device.dma_state.internal_state
  ==>
  BDS_TO_FETCH_DISJOINT bds_to_fetch
End

(* Channel requests do not address BDs to fetch.
 *)
Definition NO_MEMORY_WRITES_TO_BDS:
NO_MEMORY_WRITES_TO_BDS device_characteristics memory device =
!requests requests_was request_was.
  requests = channel_requests device_characteristics device /\
  requests_was = MAP request_to_write_addresses requests /\
  MEM request_was requests_was
  ==>
  CONSISTENT_DMA_WRITE device_characteristics memory device.dma_state.internal_state request_was
End

Definition channel_bds:
channel_bds device_characteristics memory dma_state channel_id =
  let bds_to_fetch = MAP FST ((cverification device_characteristics channel_id).bds_to_fetch memory dma_state.internal_state) in
  let channel = THE (dma_state.channels channel_id) in
  let bds_to_update = channel.queue.bds_to_update in
  let bds_to_process = channel.queue.bds_to_process in
  let bds_to_write_back = channel.queue.bds_to_write_back in
    bds_to_fetch ++ bds_to_update ++ bds_to_process ++ bds_to_write_back
End

Definition CHANNEL_BDS_EQ:
CHANNEL_BDS_EQ device_characteristics memory device1 device2 =
!channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  channel_bds device_characteristics memory device1.dma_state channel_id =
  channel_bds device_characteristics memory device2.dma_state channel_id
End

(* Used to preserve NO_MEMORY_WRITES_TO_BDS.
 *
 * External BDs to fetch must not perform DMA writes to BDs to fetch (including
 * itself).
 *)
Definition NOT_DMA_BDS:
NOT_DMA_BDS device_characteristics memory device =
!channel_id_dma_bd channel_id_bd dma_bd dma_bd_ras dma_bd_was bd bd_ras bd_was dma_was.
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id_dma_bd /\
  VALID_CHANNEL_ID device_characteristics channel_id_bd /\
  MEM (dma_bd, dma_bd_ras, dma_bd_was) (channel_bds device_characteristics memory device.dma_state channel_id_dma_bd) /\
  dma_was = SND ((cverification device_characteristics channel_id_dma_bd).bd_transfer_ras_was device.dma_state.internal_state dma_bd) /\
  MEM (bd, bd_ras, bd_was) (channel_bds device_characteristics memory device.dma_state channel_id_bd)
  ==>
  DISJOINT_LISTS dma_was bd_ras
End

Definition MEMORY_WRITES_PRESERVES_BDS_TO_FETCH:
MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device =
  READ_REQUESTS device.dma_state.pending_register_related_memory_requests
End

(* Preserved by NO_MEMORY_WRITES_TO_BDS and NOT_DMA_SCRATCHPAD since the
 * addresses returned by fetch_bd_addresses are a subset of the BD read
 * addresses, which must not overlap any DMA write addresses.
 *)
Definition INVARIANT_EXTERNAL_FETCH_BD_REPLY:
INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device =
!channel_id bytes tag1 tag2 addresses.
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  SOME (bytes, tag1) = (schannel device channel_id).pending_accesses.replies.fetching_bd /\
  (addresses, tag2) = (coperation device_characteristics channel_id).fetch_bd_addresses device.dma_state.internal_state
  ==>
  tag1 = tag2 /\
  MAP memory addresses = bytes
End

(* Used to preserve INVARIANT_EXTERNAL_FETCH_BD_REPLY.
 *)
Definition FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES:
FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
memory
(device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) =
!channel_id addresses tag.
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (schannel device channel_id).pending_accesses.requests.fetching_bd = SOME (request_read addresses tag)
  ==>
  (coperation device_characteristics channel_id).fetch_bd_addresses device.dma_state.internal_state = (addresses, tag)
End

Definition INVARIANT_CONCRETE_L3:
INVARIANT_CONCRETE_L3 device_characteristics memory device = (
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device /\
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device
)
End

(* Replaces INVARIANT_FETCH_BD_L2 since INVARIANT_FETCH_BD_L2 depends in
 * abstract BDs to fetch.
 *)
Definition INVARIANT_FETCH_BD_L3:
INVARIANT_FETCH_BD_L3 device_characteristics memory device =
!channel_id R W EXTERNAL_MEMORY_BDS internal_state bd bd_ras bd_was update_flag ras_was bds_to_fetch.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  R = device_characteristics.dma_characteristics.R memory /\
  W = device_characteristics.dma_characteristics.W memory /\
  (EXTERNAL_MEMORY_BDS = EXTERNAL_BDS device_characteristics) /\
  internal_state = device.dma_state.internal_state /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state /\
  MEM ((bd, bd_ras, bd_was), update_flag) bds_to_fetch /\
  ras_was = (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state bd
  ==>
  BD_READ R EXTERNAL_MEMORY_BDS bd_ras /\
  BD_WRITE W EXTERNAL_MEMORY_BDS bd_was /\
  BD_DATA R W ras_was
End

Definition INVARIANT_L3:
INVARIANT_L3
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
(memory : 'interconnect_address_width memory_type)
(device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) = (
  (* From INVARIANT_L1. *)
  DEVICE_REQUESTING_READ_ADDRESSES device_characteristics memory device /\
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device /\

  (* From INVARIANT_L2. *)
  DEFINED_CHANNELS device_characteristics device /\
  INVARIANT_FETCH_BD_L3 device_characteristics memory device /\	(* New for INVARIANT_L3, replacing INVARIANT_FETCH_BD_L2. *)
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device /\
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device /\

  (* New for INVARIANT_L3: INVARIANT_CONCRETE_L3. *)
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device /\
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device
)
End

val _ = export_theory();
