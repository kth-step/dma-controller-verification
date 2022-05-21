open HolKernel Parse boolLib bossLib;
open stateTheory;

val _ = new_theory "L23EQ";

Definition L23EQ:
L23EQ
(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
memory
(device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
(device3 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) = (
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device2 device3 /\
  BDS_TO_UPDATE_EQ device_characteristics device2 device3 /\
  BDS_TO_PROCESS_EQ device_characteristics device2 device3 /\
  BDS_TO_WRITE_BACK_EQ device_characteristics device2 device3 /\
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device2 device3 /\ (* Replies make internal state transitions identical when processing replies. *)
  FUNCTION_STATES_EQ device2 device3 /\
  INTERNAL_STATES_EQ device2 device3 /\
  DEFINED_CHANNELS_EQ device_characteristics device2 device3 (* Propagates L2 invariant about defined channels.*)
)
End

val _ = export_theory();

