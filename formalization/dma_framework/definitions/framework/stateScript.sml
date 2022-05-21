open HolKernel Parse boolLib bossLib listTheory wordsTheory;

val _ = new_theory "state";



(************************Types related to a DMA channel************************)

(* Instantiate 'interconnect_address_width with the number of bits that
 * constitute an address of one byte of a buffer descriptor. The type of a
 * set/list of BD addresses.
 *
 * Instantiate 'interconnect_address_width with the number of bits that
 * constitute an address related to each request to the interconnect
 * interconnecting all devices.
 *)
type_abbrev_pp ("interconnect_address_type", ``: 'interconnect_address_width word``);

(* Instantiate 'interconnect_address_width with the number of bits that
 * constitute an address of one byte of a buffer descriptor. The type of a
 * set/list of BD addresses.
 *
 * Instantiate 'interconnect_address_width with the number of bits that
 * constitute an address of the interconnect. The type of a set/list of
 * interconnect addresses.
 *)
type_abbrev_pp ("interconnect_addresses_type", ``: 'interconnect_address_width interconnect_address_type list``);

(* Instantiate 'bd_type with the type of an abstract buffer descriptor.
 * Makes pretty printing print bd_triple instead of x # y # z.
 *
 * Argument order:
 * 1. 'interconnect_address_width.
 * 2. 'bd_type.
 *)
type_abbrev_pp ("bd_ras_was_type", ``: 'bd_type # 'interconnect_address_width interconnect_addresses_type # 'interconnect_address_width interconnect_addresses_type``);

(* A part of an abstract queue entry: Specifies whether the BD of that entry
  shall be updated after being fetched. *)
Datatype: bd_update_type =
   update
 | no_update
End

(* Type of the entries in the abstract BD queue to fetch.
 *
 * Argument order:
 * 1. 'interconnect_address_width.
 * 2. 'bd_type.
 *)
type_abbrev_pp ("bds_to_fetch_entry_type", ``: ('bd_type, 'interconnect_address_width) bd_ras_was_type # bd_update_type``);

(* Type of tags intended to match interconnect reads with interconnect replies. *)
type_abbrev_pp ("tag_type", “: 'tag_width word”);

(* Datatype for interconnect accesses. The tag is used to match
 * replies/acknowledgements to reads/writes.
 * Argument order:
 * 1. 'interconnect_address_width
 * 2. 'tag_width
 *)
Datatype: interconnect_request_type =
   request_read   ('interconnect_address_width interconnect_addresses_type)             ('tag_width tag_type)
 | request_write (('interconnect_address_width interconnect_address_type # word8) list) ('tag_width tag_type)
End

(* Type of one interconnect read reply.
 *)
type_abbrev_pp ("interconnect_read_reply", “: word8 list # 'tag_width tag_type”);

(* Type of external memory which may be used to store BDs and data to be
   transferred. *)
type_abbrev_pp ("memory_type", ``: ('interconnect_address_width interconnect_address_type) -> word8``);

(* Flag used by the update_bd function to specify whether the update of a BD is
   complete. *)
Datatype: update_status_type =
  update_incomplete
| update_complete
End

type_abbrev_pp ("channel_index_type", ``: 'channel_index_width word``);

(* The operations of one type of DMA channel. The possible DMA channel types are
 * read, write and copy.
 *
 * Type variable argument order:
 * 1. 'interconnect_address_width
 * 2. 'bd_type
 * 3. 'channel_index_width
 * 4. 'environment_type
 * 5. 'interconnect_address_width
 * 6. 'internal_state_type
 * 7. 'tag_width
 *
 * The instantiated functions do not need the index as argument, because the
 * index is known from the instantiated scheduler function. If the scheduler
 * schedules (channel_sort, channel_index, channel_operation), then when
 * channel_operation is applied immediately, after, that application is with
 * respect to the index channel_index.
 *)
Datatype: channel_operations_type = <|
  (* The addresses of the next read of the BD currently being fetched.
   *)
  fetch_bd_addresses :
    'internal_state_type ->
    'interconnect_address_width interconnect_addresses_type # 'tag_width tag_type;

  (* Returns the BD now being fetched, and/or updates the internal DMA
   * controller state.
   *)
  fetch_bd :
    'internal_state_type ->
    'tag_width interconnect_read_reply option ->
    'internal_state_type # (('bd_type, 'interconnect_address_width) bds_to_fetch_entry_type option);

  (* Returns the bytes to be updated of the BD currently being updated, and a
   * flag indicating whether this is the last write of the BD update.
   *)
  update_bd :
    'internal_state_type ->
    ('bd_type, 'interconnect_address_width) bd_ras_was_type ->
    'internal_state_type # ('interconnect_address_width interconnect_address_type # 8 word) list # 'tag_width tag_type # update_status_type;

  (* Given a list of memory request replies and the associated BD, updates the
   * internal DMA controller state, generates potentially additional requests
   * and a boolean flag indicating whether all requests of the BD have now been
   * processed and the BD shall now be moved to the write back queue.
   *)
  process_replies_generate_requests :
    'internal_state_type ->
    'bd_type ->
    'tag_width interconnect_read_reply list ->
    ('internal_state_type # ((('interconnect_address_width, 'tag_width) interconnect_request_type) list) # bool);

  (* Returns the bytes to be written back of the BD currently being written
   * back, and the BDs that became released as a consequence of the write back.
   *)
  write_back_bd :
    'environment_type ->
    'internal_state_type ->
    ('bd_type, 'interconnect_address_width) bd_ras_was_type list ->
    'internal_state_type # ('interconnect_address_width interconnect_address_type # 8 word) list # 'tag_width tag_type # ('bd_type, 'interconnect_address_width) bd_ras_was_type list;
  |>
End



(****************State components of the DMA channel automata******************)

Datatype: pending_requests_type = <|
  fetching_bd       : ('interconnect_address_width, 'tag_width) interconnect_request_type option;
  updating_bd       : ('interconnect_address_width, 'tag_width) interconnect_request_type list;
  transferring_data : ('interconnect_address_width, 'tag_width) interconnect_request_type list;
  writing_back_bd   : ('interconnect_address_width, 'tag_width) interconnect_request_type list
  |>
End

Datatype: pending_replies_type = <|
  fetching_bd       : 'tag_width interconnect_read_reply option;
  transferring_data : 'tag_width interconnect_read_reply list
  |>
End

(* Pending interconnect requests and replies of all operations of a DMA channel.
 *
 * Argument order:
 * 1. 'interconnect_address_width
 * 2. 'tag_width
 *)
Datatype: pending_accesses_type = <|
  requests : ('interconnect_address_width, 'tag_width) pending_requests_type;
  replies  : 'tag_width pending_replies_type
  |>
End

(* All queues which BDs go through when processed by a DMA channel.
 *
 * Argument order:
 * 1. 'interconnect_address_width
 * 2. 'tag_width
 *)
Datatype: queue_type = <|
  (* Is is easier to reason about BDs if they cannot be changed. Therefore, it
   * is ideal that once the CPU has committed BD to queue, the BD is
   * unmodifiable. This bds_to_fetch queue ensures this property.
   *)
  bds_to_fetch      : ('bd_type, 'interconnect_address_width) bds_to_fetch_entry_type list;
  bds_to_update     : ('bd_type, 'interconnect_address_width) bd_ras_was_type list;
  bds_to_process    : ('bd_type, 'interconnect_address_width) bd_ras_was_type list;
  bds_to_write_back : ('bd_type, 'interconnect_address_width) bd_ras_was_type list
  |>
End

(* DMA channel state.
 *
 * ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type
 *)
Datatype: channel_state_type = <|
  pending_accesses : ('interconnect_address_width, 'tag_width) pending_accesses_type;
  queue            : ('bd_type, 'interconnect_address_width) queue_type
  |>
End

(********************************DMA channels**********************************)

(* Functions related to verification.
 *
 * Type arguments:
 * ('bd_type, 'environment_type, 'interconnect_address_width, 'internal_state_type) channel_verification_type
 *)
Datatype: channel_verification_type = <|
  (* Function used for proving: The abstract BD queue to be fetched of the given
   * DMA channel ID.
   *)
  bds_to_fetch :
    'interconnect_address_width memory_type ->
    'internal_state_type ->
    ((('bd_type, 'interconnect_address_width) bds_to_fetch_entry_type) list);

  (* The addresses of the next write of the BD currently being updated.
   *)
  update_bd_addresses :
    'internal_state_type ->
    ('bd_type, 'interconnect_address_width) bd_ras_was_type ->
    'interconnect_address_width interconnect_addresses_type;

  (* Function used for proving: Returns the addresses that the given BD has been
   * allocated to read and write. All these addresses may not be accessed (for
   * instance of a read channel of a NIC, a received frame may not fill the
   * buffer).
   *)
  bd_transfer_ras_was :
    'internal_state_type ->
    'bd_type ->
    'interconnect_address_width interconnect_addresses_type # 'interconnect_address_width interconnect_addresses_type;

  (* The BD read addresses of the BD currently being written back, and the
   * addresses of the next write request. The BD read addresses are used to
   * identify which BD is written back, used to check that no other BD is
   * written.
   *)
  write_back_bd_addresses :
    'environment_type ->
    'internal_state_type ->
    ('bd_type, 'interconnect_address_width) bd_ras_was_type list ->
    'interconnect_address_width interconnect_addresses_type;
  |>
End

(*************************End of DMA channels**********************************)







(*************************DMA controller***************************************)

(* The BDs are either stored in internal memory or in external memory, where the
 * latter requires accesses to the interconnect to fetch, update and write back
 * BDs.
 *)
Datatype: bd_location_type =
   internal
 | external
End

(* Datatype for identifying each of the DMA channel automata: fetch BD, update
   BD, transfer data, and write back BD. *)
Datatype: channel_operation_type =
   fetch_bd
 | update_bd
 | transfer_data
 | write_back_bd
End

type_abbrev_pp ("channel_id_type", ``: 'channel_index_width word``);

(* Type abbreviations used for the scheduler. *)
type_abbrev_pp ("bds_to_update_process_write_back_type", ``: ('bd_type, 'interconnect_address_width) bd_ras_was_type list #
                                                             ('bd_type, 'interconnect_address_width) bd_ras_was_type list #
                                                             ('bd_type, 'interconnect_address_width) bd_ras_was_type list ``); 

type_abbrev_pp ("channel_state_components_type", ``: ('interconnect_address_width, 'tag_width) pending_accesses_type # ('bd_type, 'interconnect_address_width) bds_to_update_process_write_back_type``);

type_abbrev_pp ("collected_channel_state_components_type", ``: 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_components_type option``);

type_abbrev_pp ("pending_register_related_memory_accesses_type", ``: ('interconnect_address_width, 'tag_width) interconnect_request_type list # 'tag_width interconnect_read_reply list``);

type_abbrev_pp ("collected_dma_state_type", ``: ('bd_type, 'channel_index_width, 'interconnect_address_width, 'tag_width) collected_channel_state_components_type # ('interconnect_address_width, 'tag_width) pending_register_related_memory_accesses_type``);

(* Contains the state of the DMA controller part of the device.
 *
 * Operations of a DMA controller.
 *
 * Argument order:
 * 1. 'interconnect_address_width,
 * 2. 'bd_type,
 * 3. 'channel_index_width,
 * 6. 'environment_type,
 * 7. 'function_state_type,
 * 8. 'interconnect_address_width,
 * 9. 'internal_state_type,
 * 10. 'tag_width
 *)
Datatype: dma_characteristics_type = <|
  (* Locations of BDs. *)
  bd_location :
    bd_location_type;

  (* For proving: The interconnect addresses the DMA controller is allowed to
     issue read requests to. *)
  R :
    'interconnect_address_width memory_type ->
    'interconnect_address_width interconnect_address_type ->
    bool;

  (* For proving: The interconnect addresses the DMA controller is allowed to
     issue write requests to. *)
  W :
    'interconnect_address_width memory_type ->
    'interconnect_address_width interconnect_address_type ->
    bool;

  (* Given:
   * -external information (environment; for instance a frame has been received
   *  of a NIC),
   * -non-DMA state of the device,
   * -internal DMA state of the device, and
   * -the framework DMA state (channels, which include replies and internal BD
   *  queues that may affect scheduling),
   *
   * identifies the next sort of DMA channel, which DMA channel of that sort,
   * and which automaton of that DMA channel, that shall perform the next
   * transition of the DMA part of the device.
   *)
  scheduler :
    'environment_type ->
    'function_state_type option ->
    'internal_state_type ->
    (('bd_type, 'channel_index_width, 'interconnect_address_width, 'tag_width) collected_dma_state_type) -> 'internal_state_type # 'channel_index_width channel_id_type # channel_operation_type;

  (* Instantiated function used to read registers related to DMA. Returns a list
   * of bytes and an updated state in case reads have side effects, and a list
   * of memory requests.
   *)
  register_read :
    'internal_state_type ->
    'interconnect_address_width interconnect_addresses_type ->
    'internal_state_type # (word8 list) # (('interconnect_address_width, 'tag_width) interconnect_request_type list);

  (* Instantiated function used to write registers related to DMA. Returns a
   * list of bytes, and a list of memory requests.
   *)
  register_write :
    'internal_state_type ->
    ('interconnect_address_width interconnect_address_type # word8) list ->
    'internal_state_type # (('interconnect_address_width, 'tag_width) interconnect_request_type list);

  (* Instantiated function used to update the internal state when processing
   * memory request replies (where missing writes mimic a signal of write
   * completion). The processed requests are returned.
   *)
  process_register_related_memory_replies :
    'internal_state_type ->
    ('interconnect_address_width, 'tag_width) interconnect_request_type list ->
    'tag_width interconnect_read_reply list ->
    'internal_state_type # ('tag_width interconnect_read_reply list);

  (* Scratch pad memory addresses accessible to the DMAC in the current internal
   * state.
   *)
  scratchpad_addresses : 'internal_state_type -> 'interconnect_address_width interconnect_addresses_type;

  (* All byte addresses of the registers of the device accessible to the CPU
   * related to DMA, both reads and writes.
   *
   * DISJOINT FROM FUNCTION_REGISTER_ADDRESSES.
   *)
  DMA_REGISTER_ADDRESSES :
    'interconnect_address_width interconnect_address_type ->
    bool;

  (* Index of the last channel. Assumes indexes are in the interval [0, last_index].
   *)
  max_index  : 'channel_index_width channel_id_type;

  (* Functions used for verification. Mapping channel IDs to verification
   * functions. NONE is returned if the specified DMA channel is not
   * implemented.
   *)
  verification : 'channel_index_width channel_id_type -> ('bd_type, 'environment_type, 'interconnect_address_width, 'internal_state_type) channel_verification_type option;

  (* Maps DMA channel IDs to the operations of the associated DMA channel. NONE
   * is returned if the specified DMA channel is not implemented.
   *)
  operation : 'channel_index_width channel_id_type -> ('bd_type, 'environment_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) channel_operations_type option
  |>
End

Datatype: dma_state_type = <|
  internal_state : 'internal_state_type;

  (* Maps DMA channel ID to DMA channel state, or NONE if the specified DMA
   * channel is not implemented.
   *)
  channels : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option;

  (* Pending and served memory requests associated with memory accesses due to register accesses.
   *)
  pending_register_related_memory_requests : ('interconnect_address_width, 'tag_width) interconnect_request_type list;
  pending_register_related_memory_replies  : 'tag_width interconnect_read_reply list
  |>
End

(******************End of DMA controller***************************************)





(******************Device***************************************)

Datatype: function_characteristics_type = <|
  (* Transition function of the device.
   *)
  function_operation : ('environment_type -> 'function_state_type -> 'function_state_type);

  (* Instantiated function used to read registers unrelated to DMA. Returns a
   * list of bytes and an updated state in case reads have side effects.
   *)
  function_register_read :
    'function_state_type ->
    'interconnect_address_width interconnect_addresses_type ->
    'function_state_type # word8 list;

  (* Instantiated function used to write registers unrelated to DMA. Returns a
   * list of bytes.
   *)
  function_register_write :
    'function_state_type ->
    ('interconnect_address_width interconnect_address_type # word8) list ->
    'function_state_type;

  (* All byte addresses of the registers of the device accessible to the CPU but
   * independent of DMA (both reads and writes to these registers are
   * independent of DMA).
   *
   * DISJOINT FROM DMA_REGISTER_ADDRESSES.
   *)
  FUNCTION_REGISTER_ADDRESSES :
    'interconnect_address_width interconnect_address_type ->
    bool;
  |>
End

(* The state of a device, consisting of an optional non-DMA part and a DMA part.
 * ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type
 *)
Datatype: device_state_type = <|
  function_state :
    'function_state_type option;

  dma_state : ('bd_type, 'channel_index_width, 'interconnect_address_width, 'internal_state_type, 'tag_width) dma_state_type
  |>
End

(* Type used by the device scheduler to indicate whether the next operation of
 * the device is the functional part of the device (e.g. network logic) or the
 * DMA part of the device.
 *
 * If the device has no function implemented (stand-alone DMA controller), then
 * only dma is used by the scheduler function.
 *)
Datatype: device_parts_type =
   function
 | dma_register_memory_access
 | dma_operation
 | idle
End

(* The characteristics of the device.

 
 ('bd_type,
  'channel_index_width,
  'environment_type,
  'function_state_type,
  'interconnect_address_width,
  'internal_state_type,
  'tag_width)
 *)
Datatype: device_characteristics_type = <|
  (* Given external environment (e.g. data input to network interface
   * controller), and the state of the complete device (including both
   * functional and DMA parts), indicates whether the next step of the device
   * is performed by the functional part of the DMA part.
   *)
  device_scheduler :
    'environment_type ->
    'function_state_type option ->
    'internal_state_type ->
    (('bd_type, 'channel_index_width, 'interconnect_address_width, 'tag_width) collected_dma_state_type) ->
    device_parts_type;

  (* The characteristics of the device that describe the functions of the
   * device, which are unrelated to DMA, and which is an option in case it is
   * not implemented (stand-alone DMA controller)
   *)
  function_characteristics :
    ('environment_type, 'function_state_type, 'interconnect_address_width) function_characteristics_type option;

  dma_characteristics :
    ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) dma_characteristics_type
  |>
End





(*Start of definitions denoting implemented DMA channels***********************)

Definition VALID_CHANNEL_ID:
  VALID_CHANNEL_ID device_characteristics index = (index <=+ device_characteristics.dma_characteristics.max_index)
End

(* If the channels are implemented, then they have states.
 *)
Definition VALID_CHANNELS:
  VALID_CHANNELS device_characteristics channels =
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id ==> IS_SOME (channels channel_id)
End

(* State contains declared channels.
 *)
Definition DEFINED_CHANNELS:
DEFINED_CHANNELS device_characteristics device =
  VALID_CHANNELS device_characteristics device.dma_state.channels
End

(*End of definitions denoting implemented DMA channels*************************)

Definition INTERNAL_BDS:
  INTERNAL_BDS device_characteristics = (device_characteristics.dma_characteristics.bd_location = internal)
End

Definition EXTERNAL_BDS:
  EXTERNAL_BDS device_characteristics = (device_characteristics.dma_characteristics.bd_location = external)
End

(* c for characteristics. *)
Definition cverification:
  cverification device_characteristics channel_id = THE (device_characteristics.dma_characteristics.verification channel_id)
End

Definition coperation:
  coperation device_characteristics channel_id = THE (device_characteristics.dma_characteristics.operation channel_id)
End

Definition clocation:
  clocation device_characteristics = device_characteristics.dma_characteristics.bd_location
End

(* s for state.
 *
 * Obtains a DMA channel given a device state and a channel ID.
 *)
Definition schannel:
schannel device channel_id = THE (device.dma_state.channels channel_id)
End

(***********End of Device***************************************)


(* Start of BD predicates. *)

Definition BD_READ:
BD_READ R EXTERNAL_MEMORY_BDS bd_ras = (
  EXTERNAL_MEMORY_BDS
  ==>
  EVERY R bd_ras
)
End

Definition BD_WRITE:
BD_WRITE W EXTERNAL_MEMORY_BDS bd_was = (
  EXTERNAL_MEMORY_BDS
  ==>
  EVERY W bd_was
)
End

Definition BD_DATA:
BD_DATA R W (ras, was) = (
  EVERY R ras /\
  EVERY W was
)
End

(* End of BD predicates. *)



Definition READ_REQUEST:
(READ_REQUEST (request_read addresses tag) = T) /\
(READ_REQUEST (request_write address_bytes tag) = F)
End

Definition WRITE_REQUEST:
(WRITE_REQUEST (request_read addresses tag) = F) /\
(WRITE_REQUEST (request_write address_bytes tag) = T)
End

Definition READ_REQUESTS:
READ_REQUESTS requests = EVERY READ_REQUEST requests
End

Definition WRITE_REQUESTS:
WRITE_REQUESTS requests = EVERY WRITE_REQUEST requests
End

Definition R_W_EQ:
R_W_EQ device_characteristics memory1 memory2 = (
  device_characteristics.dma_characteristics.R memory1 = device_characteristics.dma_characteristics.R memory2 /\
  device_characteristics.dma_characteristics.W memory1 = device_characteristics.dma_characteristics.W memory2
)
End

Definition ALL_BDS_TO_FETCH_EQ:
ALL_BDS_TO_FETCH_EQ device_characteristics internal_state1 internal_state2 =
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    !memory.
      (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 =
      (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2
End

(***********Start of relations between layers************************)

Definition ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ:
ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ
  (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
  (memory : 'interconnect_address_width memory_type)
  (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
  (device3 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) =
!channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  (schannel device2 channel_id).queue.bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory device3.dma_state.internal_state
End

Definition ABSTRACT_BDS_TO_FETCH_EQ:
ABSTRACT_BDS_TO_FETCH_EQ device_characteristics device1 device2 =
!channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  (schannel device2 channel_id).queue.bds_to_fetch = (schannel device1 channel_id).queue.bds_to_fetch
End

Definition ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ:
ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds channel2 channel3 = (
  channel2.queue.bds_to_fetch      = concrete_bds /\
  channel2.queue.bds_to_update     = channel3.queue.bds_to_update /\
  channel2.queue.bds_to_process    = channel3.queue.bds_to_process /\
  channel2.queue.bds_to_write_back = channel3.queue.bds_to_write_back /\
  channel2.pending_accesses        = channel3.pending_accesses
)
End

Definition OTHER_BDS_TO_FETCH_EQ:
OTHER_BDS_TO_FETCH_EQ device_characteristics channel_id memory internal_state1 internal_state2 =
  !channel_id'.
    VALID_CHANNEL_ID device_characteristics channel_id' /\
    channel_id' <> channel_id
    ==>
    (cverification device_characteristics channel_id').bds_to_fetch memory internal_state2 =
    (cverification device_characteristics channel_id').bds_to_fetch memory internal_state1
End

Definition BDS_TO_FETCH_EQ:
BDS_TO_FETCH_EQ device_characteristics memory internal_state1 internal_state2 =
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 =
    (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2
End

Definition CONCRETE_BDS_TO_FETCH_EQ:
CONCRETE_BDS_TO_FETCH_EQ
  (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
  (memory : 'interconnect_address_width memory_type)
  (device3 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
  (device4 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) =
!channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  (cverification device_characteristics channel_id).bds_to_fetch memory device3.dma_state.internal_state = (cverification device_characteristics channel_id).bds_to_fetch memory device4.dma_state.internal_state
End

Definition BDS_TO_UPDATE_EQ:
BDS_TO_UPDATE_EQ device_characteristics device1 device2 =
!channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  (schannel device1 channel_id).queue.bds_to_update = (schannel device2 channel_id).queue.bds_to_update
End

Definition BDS_TO_PROCESS_EQ:
BDS_TO_PROCESS_EQ device_characteristics device1 device2 =
!channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  (schannel device1 channel_id).queue.bds_to_process = (schannel device2 channel_id).queue.bds_to_process
End

Definition BDS_TO_WRITE_BACK_EQ:
BDS_TO_WRITE_BACK_EQ device_characteristics device1 device2 =
!channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  (schannel device1 channel_id).queue.bds_to_write_back = (schannel device2 channel_id).queue.bds_to_write_back
End

Definition MEMORY_REQUESTS_REPLIES_EQ:
MEMORY_REQUESTS_REPLIES_EQ device_characteristics device1 device2 = (
device1.dma_state.pending_register_related_memory_requests = device2.dma_state.pending_register_related_memory_requests /\
device1.dma_state.pending_register_related_memory_replies = device2.dma_state.pending_register_related_memory_replies /\
!channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  (schannel device1 channel_id).pending_accesses = (schannel device2 channel_id).pending_accesses
)
End

Definition FUNCTION_STATES_EQ:
FUNCTION_STATES_EQ device1 device2 =
  (device1.function_state = device2.function_state)
End

Definition INTERNAL_STATES_EQ:
INTERNAL_STATES_EQ device1 device2 =
  (device1.dma_state.internal_state = device2.dma_state.internal_state)
End

Definition DEFINED_CHANNELS_EQ:
DEFINED_CHANNELS_EQ device_characteristics device1 device2 =
!channel_id.
  IS_SOME (device1.dma_state.channels channel_id) = IS_SOME (device2.dma_state.channels channel_id)
End

Definition BD_TRANSFER_RAS_WAS_EQ:
BD_TRANSFER_RAS_WAS_EQ device_characteristics internal_state1 internal_state2 =
!channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  !bd.
    (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state1 bd =
    (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state2 bd
End

Definition SCRATCHPAD_ADDRESSES_EQ:
SCRATCHPAD_ADDRESSES_EQ device_characteristics internal_state1 internal_state2 = (
  device_characteristics.dma_characteristics.scratchpad_addresses internal_state1 =
  device_characteristics.dma_characteristics.scratchpad_addresses internal_state2
)
End

Definition FETCH_BD_ADDRESSES_EQ:
FETCH_BD_ADDRESSES_EQ device_characteristics internal_state1 internal_state2 =
!channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  (coperation device_characteristics channel_id).fetch_bd_addresses internal_state1 =
  (coperation device_characteristics channel_id).fetch_bd_addresses internal_state2
End

Definition CHANNELS_EQ:
CHANNELS_EQ device1 device2 = (device1.dma_state.channels = device2.dma_state.channels)
End

(***********End of relations between layers************************)





(* Labels for device transition systems.
 *)
Datatype: device_transition_labels_type =
 | device_internal_operation 'environment_type
 | device_memory_read        (('interconnect_address_width interconnect_address_type # word8) list)
 | device_memory_write       (('interconnect_address_width interconnect_address_type # word8) list)
 | external_bds_appended
 | device_register_read      ((('interconnect_address_width interconnect_address_type # word8) list) # (('interconnect_address_width interconnect_address_type # word8) list))
 | device_register_write     ((('interconnect_address_width interconnect_address_type # word8) list) # (('interconnect_address_width interconnect_address_type # word8) list))
End

val _ = export_theory();
