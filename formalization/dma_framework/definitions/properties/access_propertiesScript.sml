open HolKernel Parse boolLib bossLib stateTheory operationsTheory bd_queuesTheory;

val _ = new_theory "access_properties";

Definition REQUEST_CONDITION_R:
  (REQUEST_CONDITION_R R memory (request_read addresses tag) = EVERY (R memory) addresses) /\
  (REQUEST_CONDITION_R R memory (request_write address_bytes tag) = T)
End

Definition REQUEST_CONDITION_W:
  (REQUEST_CONDITION_W W memory (request_read addresses tag) = T) /\
  (REQUEST_CONDITION_W W memory (request_write address_bytes tag) = EVERY (W memory) (MAP FST address_bytes))
End

Definition REQUEST_CONDITION_R_W:
REQUEST_CONDITION_R_W R W memory request = (
  REQUEST_CONDITION_R R memory request /\
  REQUEST_CONDITION_W W memory request
)
End

Definition PENDING_ACCESSES_UNMODIFIED_FETCHING_BD:
  PENDING_ACCESSES_UNMODIFIED_FETCHING_BD (channel1 : ('a, 'b, 'c) channel_state_type) (channel2 : ('a, 'b, 'c) channel_state_type) =
    (channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd)
End

Definition PENDING_ACCESSES_UNMODIFIED_UPDATING_BD:
  PENDING_ACCESSES_UNMODIFIED_UPDATING_BD (channel1 : ('a, 'b, 'c) channel_state_type) (channel2 : ('a, 'b, 'c) channel_state_type) =
    (channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd)
End

Definition PENDING_ACCESSES_UNMODIFIED_TRANSFERRING_DATA:
  PENDING_ACCESSES_UNMODIFIED_TRANSFERRING_DATA (channel1 : ('a, 'b, 'c) channel_state_type)
                                                (channel2 : ('a, 'b, 'c) channel_state_type) =
    (channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data)
End

Definition PENDING_ACCESSES_UNMODIFIED_WRITING_BACK_BD:
  PENDING_ACCESSES_UNMODIFIED_WRITING_BACK_BD (channel1 : ('a, 'b, 'c) channel_state_type)
                                              (channel2 : ('a, 'b, 'c) channel_state_type) =
    (channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd)
End

Definition PENDING_ACCESSES_UNMODIFIED_REGISTER:
  PENDING_ACCESSES_UNMODIFIED_REGISTER
    (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
    (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) =
  (device1.dma_state.pending_register_related_memory_requests =
   device2.dma_state.pending_register_related_memory_requests)
End





Definition PENDING_ACCESSES_UNEXPANDED_FETCHING_BD:
  PENDING_ACCESSES_UNEXPANDED_FETCHING_BD (channel1 : ('a, 'b, 'c) channel_state_type) (channel2 : ('a, 'b, 'c) channel_state_type) =
  !request.
    channel2.pending_accesses.requests.fetching_bd = SOME request
    ==>
    channel1.pending_accesses.requests.fetching_bd = SOME request
End

Definition PENDING_ACCESSES_UNEXPANDED_UPDATING_BD:
  PENDING_ACCESSES_UNEXPANDED_UPDATING_BD (channel1 : ('a, 'b, 'c) channel_state_type) (channel2 : ('a, 'b, 'c) channel_state_type) =
  !request.
    MEM request channel2.pending_accesses.requests.updating_bd
    ==>
    MEM request channel1.pending_accesses.requests.updating_bd
End

Definition PENDING_ACCESSES_UNEXPANDED_TRANSFERRING_DATA:
  PENDING_ACCESSES_UNEXPANDED_TRANSFERRING_DATA (channel1 : ('a, 'b, 'c) channel_state_type)
                                                (channel2 : ('a, 'b, 'c) channel_state_type) =
  !request.
    MEM request channel2.pending_accesses.requests.transferring_data
    ==>
    MEM request channel1.pending_accesses.requests.transferring_data
End

Definition PENDING_ACCESSES_UNEXPANDED_WRITING_BACK_BD:
  PENDING_ACCESSES_UNEXPANDED_WRITING_BACK_BD (channel1 : ('a, 'b, 'c) channel_state_type)
                                              (channel2 : ('a, 'b, 'c) channel_state_type) =
  !request.
    MEM request channel2.pending_accesses.requests.writing_back_bd
    ==>
    MEM request channel1.pending_accesses.requests.writing_back_bd
End

Definition PENDING_ACCESSES_UNEXPANDED_REGISTER:
  PENDING_ACCESSES_UNEXPANDED_REGISTER
    (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
    (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) =
  !request.
    MEM request device2.dma_state.pending_register_related_memory_requests
    ==>
    MEM request device1.dma_state.pending_register_related_memory_requests
End




Definition PENDING_ACCESSES_CONDITIONALLY_EXPANDED_FETCHING_BD:
  PENDING_ACCESSES_CONDITIONALLY_EXPANDED_FETCHING_BD R W memory (channel1 : ('a, 'b, 'c) channel_state_type)
                                                                 (channel2 : ('a, 'b, 'c) channel_state_type) =
  !request.
    channel2.pending_accesses.requests.fetching_bd = SOME request
    ==>
    REQUEST_CONDITION_R_W R W memory request
End

Definition PENDING_ACCESSES_CONDITIONALLY_EXPANDED_UPDATING_BD:
  PENDING_ACCESSES_CONDITIONALLY_EXPANDED_UPDATING_BD R W memory (channel1 : ('a, 'b, 'c) channel_state_type)
                                                                 (channel2 : ('a, 'b, 'c) channel_state_type) =
  !request.
    MEM request channel2.pending_accesses.requests.updating_bd
    ==>
    MEM request channel1.pending_accesses.requests.updating_bd \/
    REQUEST_CONDITION_R_W R W memory request
End

Definition PENDING_ACCESSES_CONDITIONALLY_EXPANDED_TRANSFERRING_DATA:
  PENDING_ACCESSES_CONDITIONALLY_EXPANDED_TRANSFERRING_DATA R W memory (channel1 : ('a, 'b, 'c) channel_state_type)
                                                                       (channel2 : ('a, 'b, 'c) channel_state_type) =
  !request.
    MEM request channel2.pending_accesses.requests.transferring_data
    ==>
    MEM request channel1.pending_accesses.requests.transferring_data \/
    REQUEST_CONDITION_R_W R W memory request
End

Definition PENDING_ACCESSES_CONDITIONALLY_EXPANDED_WRITING_BACK_BD:
  PENDING_ACCESSES_CONDITIONALLY_EXPANDED_WRITING_BACK_BD R W memory (channel1 : ('a, 'b, 'c) channel_state_type)
                                                                     (channel2 : ('a, 'b, 'c) channel_state_type) =
  !request.
    MEM request channel2.pending_accesses.requests.writing_back_bd
    ==>
    MEM request channel1.pending_accesses.requests.writing_back_bd \/
    REQUEST_CONDITION_R_W R W memory request
End

Definition PENDING_ACCESSES_CONDITIONALLY_EXPANDED_REGISTER:
  PENDING_ACCESSES_CONDITIONALLY_EXPANDED_REGISTER
  R W memory
    (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
    (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) =
  !request.
    MEM request device2.dma_state.pending_register_related_memory_requests
    ==>
    MEM request device1.dma_state.pending_register_related_memory_requests \/
    REQUEST_CONDITION_R_W R W memory request
End



Definition PENDING_ACCESSES_RESTRICTED_FETCHING_BD:
  PENDING_ACCESSES_RESTRICTED_FETCHING_BD R W memory channel1 channel2 = (
    PENDING_ACCESSES_UNMODIFIED_FETCHING_BD channel1 channel2 \/
    PENDING_ACCESSES_UNEXPANDED_FETCHING_BD channel1 channel2 \/
    PENDING_ACCESSES_CONDITIONALLY_EXPANDED_FETCHING_BD R W memory channel1 channel2)
End

Definition PENDING_ACCESSES_RESTRICTED_UPDATING_BD:
  PENDING_ACCESSES_RESTRICTED_UPDATING_BD R W memory channel1 channel2 = (
    PENDING_ACCESSES_UNMODIFIED_UPDATING_BD channel1 channel2 \/
    PENDING_ACCESSES_UNEXPANDED_UPDATING_BD channel1 channel2 \/
    PENDING_ACCESSES_CONDITIONALLY_EXPANDED_UPDATING_BD R W memory channel1 channel2)
End

Definition PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA:
  PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA R W memory channel1 channel2 = (
    PENDING_ACCESSES_UNMODIFIED_TRANSFERRING_DATA channel1 channel2 \/
    PENDING_ACCESSES_UNEXPANDED_TRANSFERRING_DATA channel1 channel2 \/
    PENDING_ACCESSES_CONDITIONALLY_EXPANDED_TRANSFERRING_DATA R W memory channel1 channel2)
End

Definition PENDING_ACCESSES_RESTRICTED_WRITING_BACK_BD:
  PENDING_ACCESSES_RESTRICTED_WRITING_BACK_BD R W memory channel1 channel2 = (
    PENDING_ACCESSES_UNMODIFIED_WRITING_BACK_BD channel1 channel2 \/
    PENDING_ACCESSES_UNEXPANDED_WRITING_BACK_BD channel1 channel2 \/
    PENDING_ACCESSES_CONDITIONALLY_EXPANDED_WRITING_BACK_BD R W memory channel1 channel2)
End

Definition PENDING_ACCESSES_RESTRICTED_REGISTER:
  PENDING_ACCESSES_RESTRICTED_REGISTER R W memory device1 device2 = (
    PENDING_ACCESSES_UNMODIFIED_REGISTER device1 device2 \/
    PENDING_ACCESSES_UNEXPANDED_REGISTER device1 device2 \/
    PENDING_ACCESSES_CONDITIONALLY_EXPANDED_REGISTER R W memory device1 device2)
End

Definition PENDING_ACCESSES_RESTRICTED:
  PENDING_ACCESSES_RESTRICTED R W memory channel1 channel2 = (
  PENDING_ACCESSES_RESTRICTED_FETCHING_BD R W memory channel1 channel2 /\
  PENDING_ACCESSES_RESTRICTED_UPDATING_BD R W memory channel1 channel2 /\
  PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA R W memory channel1 channel2 /\
  PENDING_ACCESSES_RESTRICTED_WRITING_BACK_BD R W memory channel1 channel2)
End

Definition PENDING_ACCESSES_UNEXPANDED:
  PENDING_ACCESSES_UNEXPANDED channel1 channel2 = (
  PENDING_ACCESSES_UNEXPANDED_FETCHING_BD channel1 channel2 /\
  PENDING_ACCESSES_UNEXPANDED_UPDATING_BD channel1 channel2 /\
  PENDING_ACCESSES_UNEXPANDED_TRANSFERRING_DATA channel1 channel2 /\
  PENDING_ACCESSES_UNEXPANDED_WRITING_BACK_BD channel1 channel2)
End

Definition PENDING_ACCESSES_UNEXPANDED:
  PENDING_ACCESSES_UNEXPANDED channel1 channel2 = (
  PENDING_ACCESSES_UNEXPANDED_FETCHING_BD channel1 channel2 /\
  PENDING_ACCESSES_UNEXPANDED_UPDATING_BD channel1 channel2 /\
  PENDING_ACCESSES_UNEXPANDED_TRANSFERRING_DATA channel1 channel2 /\
  PENDING_ACCESSES_UNEXPANDED_WRITING_BACK_BD channel1 channel2)
End

Definition READABLE_WRITABLE:
  (READABLE_WRITABLE R W memory [] = T) /\
  (READABLE_WRITABLE R W memory ((request_read addresses tag)::requests) =
   (EVERY (R memory) addresses /\ READABLE_WRITABLE R W memory requests)) /\
  (READABLE_WRITABLE R W memory ((request_write address_bytes tag)::requests) =
   (EVERY (W memory) (MAP FST address_bytes) /\ READABLE_WRITABLE R W memory requests))
End

Definition is_valid_readable_writable:
  (is_valid_readable_writable (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
            (memory : 'interconnect_address_width memory_type)
            (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
            (request_read (addresses : 'interconnect_address_width interconnect_addresses_type) (tag : 'tag_width tag_type)) = EVERY (device_characteristics.dma_characteristics.R memory) addresses)
  /\
  (is_valid_readable_writable device_characteristics memory device (request_write address_bytes tag) = (EVERY (device_characteristics.dma_characteristics.W memory) (MAP FST address_bytes)))
End

val _ = export_theory();

