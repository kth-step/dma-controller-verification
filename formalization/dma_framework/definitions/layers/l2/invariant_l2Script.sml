open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory proof_obligations_dma_l2Theory l2Theory;

val _ = new_theory "invariant_l2";

(* I2 device: BDs address R/W.
 *
 * Preservation proof: device_characteristics and channel_id are not part of the
 * state, and the BDs in the different queues are not changed.
 *
 *
 * Each BD is located at readable locations if BDs are located in external
 * memory.
 *)
Definition INVARIANT_FETCH_BD_L2:
INVARIANT_FETCH_BD_L2
  (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
  (memory : 'interconnect_address_width memory_type)
  (device : ('bd_type, 'channel_index_width,
             'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) =
!channel_id R W EXTERNAL_MEMORY_BDS internal_state bd bd_ras bd_was update_flag ras_was.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  R = device_characteristics.dma_characteristics.R memory /\
  W = device_characteristics.dma_characteristics.W memory /\
  EXTERNAL_MEMORY_BDS = EXTERNAL_BDS device_characteristics /\
  internal_state = device.dma_state.internal_state /\
  MEM ((bd, bd_ras, bd_was), update_flag) (schannel device channel_id).queue.bds_to_fetch /\
  ras_was = (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state bd
  ==>
  BD_READ R EXTERNAL_MEMORY_BDS bd_ras /\
  BD_WRITE W EXTERNAL_MEMORY_BDS bd_was /\
  BD_DATA R W ras_was
End

Definition INVARIANT_UPDATE_BD_L2:
INVARIANT_UPDATE_BD_L2
  (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
  (memory : 'interconnect_address_width memory_type)
  (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) =
!channel_id R W EXTERNAL_MEMORY_BDS internal_state bd bd_ras bd_was ras_was.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  R = device_characteristics.dma_characteristics.R memory /\
  W = device_characteristics.dma_characteristics.W memory /\
  EXTERNAL_MEMORY_BDS = EXTERNAL_BDS device_characteristics /\
  internal_state = device.dma_state.internal_state /\
  MEM (bd, bd_ras, bd_was) (schannel device channel_id).queue.bds_to_update /\
  ras_was = (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state bd
  ==>
  BD_WRITE W EXTERNAL_MEMORY_BDS bd_was /\
  BD_DATA R W ras_was
End

Definition INVARIANT_TRANSFER_DATA_L2:
INVARIANT_TRANSFER_DATA_L2
  (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
  (memory : 'interconnect_address_width memory_type)
  (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) =
!channel_id R W EXTERNAL_MEMORY_BDS internal_state bd bd_ras bd_was ras_was.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  R = device_characteristics.dma_characteristics.R memory /\
  W = device_characteristics.dma_characteristics.W memory /\
  EXTERNAL_MEMORY_BDS = EXTERNAL_BDS device_characteristics /\
  internal_state = device.dma_state.internal_state /\
  MEM (bd, bd_ras, bd_was) (schannel device channel_id).queue.bds_to_process /\
  ras_was = (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state bd
  ==>
  BD_WRITE W EXTERNAL_MEMORY_BDS bd_was /\
  BD_DATA R W ras_was
End

Definition INVARIANT_WRITE_BACK_BD_L2:
INVARIANT_WRITE_BACK_BD_L2
  (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
  (memory : 'interconnect_address_width memory_type)
  (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) =
!channel_id W EXTERNAL_MEMORY_BDS bd bd_ras bd_was.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  W = device_characteristics.dma_characteristics.W memory /\
  EXTERNAL_MEMORY_BDS = EXTERNAL_BDS device_characteristics /\
  MEM (bd, bd_ras, bd_was) (schannel device channel_id).queue.bds_to_write_back
  ==>
  BD_WRITE W EXTERNAL_MEMORY_BDS bd_was
End

Definition INVARIANT_SCRATCHPAD_R_L2:
INVARIANT_SCRATCHPAD_R_L2
  (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
  (memory : 'interconnect_address_width memory_type)
  (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) =
!scratchpad_addresses.
  scratchpad_addresses = device_characteristics.dma_characteristics.scratchpad_addresses device.dma_state.internal_state
  ==>
  EVERY (device_characteristics.dma_characteristics.R memory) scratchpad_addresses
End

Definition INVARIANT_SCRATCHPAD_W_L2:
INVARIANT_SCRATCHPAD_W_L2
  (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
  (memory : 'interconnect_address_width memory_type)
  (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) =
!scratchpad_addresses.
  scratchpad_addresses = device_characteristics.dma_characteristics.scratchpad_addresses device.dma_state.internal_state
  ==>
  EVERY (device_characteristics.dma_characteristics.W memory) scratchpad_addresses
End

Definition INVARIANT_L2:
INVARIANT_L2
  (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
  (memory : 'interconnect_address_width memory_type)
  (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) = (
  DEFINED_CHANNELS device_characteristics device /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory device /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory device /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory device /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory device /\
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory device /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory device
)
End

val _ = export_theory();

