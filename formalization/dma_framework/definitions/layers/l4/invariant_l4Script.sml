open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory invariant_l3Theory bd_queuesTheory concreteTheory;

val _ = new_theory "invariant_l4";

Definition BD_WRITE:
BD_WRITE device_characteristics memory device queue_type_bds_to_operation =
!channel_id channel bd bd_ras bd_was.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channel = schannel device channel_id /\
  MEM (bd, bd_ras, bd_was) (queue_type_bds_to_operation channel.queue)
  ==>
  CONSISTENT_BD_WRITE device_characteristics memory device.dma_state.internal_state bd_was
End

Definition DMA_WRITE:
DMA_WRITE device_characteristics memory device queue_type_bds_to_operation =
!channel_id channel bd bd_ras bd_was ras was.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channel = schannel device channel_id /\
  MEM (bd, bd_ras, bd_was) (queue_type_bds_to_operation channel.queue) /\
  (ras, was) = (cverification device_characteristics channel_id).bd_transfer_ras_was device.dma_state.internal_state bd
  ==>
  CONSISTENT_DMA_WRITE device_characteristics memory device.dma_state.internal_state was
End



Definition INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4:
INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4 device_characteristics memory device =
!channel_id bd1 bd_ras1 bd_was1 uf1 bd2 bd_ras2 bd_was2 uf2 bds_to_fetch preceding_bds following_bds.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory device.dma_state.internal_state /\
  preceding_bds ++ [((bd1, bd_ras1, bd_was1), uf1)] ++ following_bds = bds_to_fetch /\
  MEM ((bd2, bd_ras2, bd_was2), uf2) (preceding_bds ++ following_bds)
  ==>
  DISJOINT_LISTS bd_was1 bd_ras2
End

Definition INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4:
INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4 device_characteristics memory device =
!channel_id bd bd_ras bd_was update_flag bds_to_fetch.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory device.dma_state.internal_state /\
  MEM ((bd, bd_ras, bd_was), update_flag) bds_to_fetch
  ==>
  DISJOINT_FROM_OTHER_BDS_TO_FETCH device_characteristics channel_id memory device.dma_state.internal_state bd_was
End

Definition INVARIANT_UPDATE_BD_BD_WRITE_L4:
INVARIANT_UPDATE_BD_BD_WRITE_L4 device_characteristics memory device =
  BD_WRITE device_characteristics memory device queue_type_bds_to_update
End

Definition INVARIANT_PROCESS_BD_BD_WRITE_L4:
INVARIANT_PROCESS_BD_BD_WRITE_L4 device_characteristics memory device =
  BD_WRITE device_characteristics memory device queue_type_bds_to_process
End

Definition INVARIANT_WRITE_BACK_BD_BD_WRITE_L4:
INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 device_characteristics memory device =
  BD_WRITE device_characteristics memory device queue_type_bds_to_write_back
End



Definition INVARIANT_FETCH_BD_DMA_WRITE_L4:
INVARIANT_FETCH_BD_DMA_WRITE_L4 device_characteristics memory device =
!channel_id bd bd_ras bd_was update_flag ras was bds_to_fetch.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory device.dma_state.internal_state /\
  MEM ((bd, bd_ras, bd_was), update_flag) bds_to_fetch /\
  (ras, was) = (cverification device_characteristics channel_id).bd_transfer_ras_was device.dma_state.internal_state bd
  ==>
  CONSISTENT_DMA_WRITE device_characteristics memory device.dma_state.internal_state was
End

Definition INVARIANT_UPDATE_BD_DMA_WRITE_L4:
INVARIANT_UPDATE_BD_DMA_WRITE_L4 device_characteristics memory device =
  DMA_WRITE device_characteristics memory device queue_type_bds_to_update
End

Definition INVARIANT_PROCESS_BD_DMA_WRITE_L4:
INVARIANT_PROCESS_BD_DMA_WRITE_L4 device_characteristics memory device =
  DMA_WRITE device_characteristics memory device queue_type_bds_to_process
End



Definition INVARIANT_CONCRETE_L4:
INVARIANT_CONCRETE_L4 device_characteristics memory device = (
  INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4 device_characteristics memory device /\ (* To preserve the other three predicates of INVARIANT_CONCRETE_L4. *)
  INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4 device_characteristics memory device /\ (* To preserve the other three predicates of INVARIANT_CONCRETE_L4. *)
  INVARIANT_UPDATE_BD_BD_WRITE_L4 device_characteristics memory device /\
  INVARIANT_PROCESS_BD_BD_WRITE_L4 device_characteristics memory device /\ (* To preserve the other three predicates of INVARIANT_CONCRETE_L4. *)
  INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 device_characteristics memory device /\

  INVARIANT_FETCH_BD_DMA_WRITE_L4 device_characteristics memory device /\ (* To preserve the other three predicates of INVARIANT_CONCRETE_L4. *)
  INVARIANT_UPDATE_BD_DMA_WRITE_L4 device_characteristics memory device /\ (* To preserve the other three predicates of INVARIANT_CONCRETE_L4. *)
  INVARIANT_PROCESS_BD_DMA_WRITE_L4 device_characteristics memory device
)
End

Definition INVARIANT_L4:
INVARIANT_L4
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

  (* From INVARIANT_L3. *)
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device /\
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device /\

  (* New for INVARIANT_L4. *)
  INVARIANT_UPDATE_BD_BD_WRITE_L4 device_characteristics memory device /\
  INVARIANT_PROCESS_BD_DMA_WRITE_L4 device_characteristics memory device /\
  INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 device_characteristics memory device /\

  INVARIANT_FETCH_BD_BD_WRITE_SAME_CHANNEL_L4 device_characteristics memory device /\
  INVARIANT_FETCH_BD_BD_WRITE_OTHER_CHANNEL_L4 device_characteristics memory device /\
  INVARIANT_PROCESS_BD_BD_WRITE_L4 device_characteristics memory device /\
  INVARIANT_FETCH_BD_DMA_WRITE_L4 device_characteristics memory device /\
  INVARIANT_UPDATE_BD_DMA_WRITE_L4 device_characteristics memory device
)
End

val _ = export_theory();
