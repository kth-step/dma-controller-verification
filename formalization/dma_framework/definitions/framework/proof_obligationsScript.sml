open HolKernel Parse boolLib bossLib;
open wordsTheory stateTheory operationsTheory bd_queuesTheory;

val _ = new_theory "proof_obligations";

(******************************************************************************)
(*Proof obligations related to fetching BDs.***********************************)
(******************************************************************************)

(* If there is no BD to fetch, then none is returned and the state is unchanged.
 *)
Definition PROOF_OBLIGATION_NO_BDS_TO_FETCH:
PROOF_OBLIGATION_NO_BDS_TO_FETCH device_characteristics =
!memory internal_state channel_id read_reply.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (cverification device_characteristics channel_id).bds_to_fetch memory internal_state = []
  ==>
  (coperation device_characteristics channel_id).fetch_bd internal_state read_reply = (internal_state, NONE)
End

(* If there is no BD to fetch, then there are no next BD addresses to read.
 *)
Definition PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ:
PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ device_characteristics =
!memory internal_state channel_id addresses tag.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (cverification device_characteristics channel_id).bds_to_fetch memory internal_state = [] /\
  (coperation device_characteristics channel_id).fetch_bd_addresses internal_state = (addresses, tag)
  ==>
  addresses = []
End

(* If there are BDs to fetch, then the next addresses to read to fetch a BD is a
 * subset of the "declared" BD read addresses.
 *)
Definition PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS:
PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS device_characteristics =
!memory internal_state bd bd_ras bd_was update_flag bds channel_id addresses tag.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (cverification device_characteristics channel_id).bds_to_fetch memory internal_state = ((bd, bd_ras, bd_was), update_flag)::bds /\
  (addresses, tag) = (coperation device_characteristics channel_id).fetch_bd_addresses internal_state
  ==>
  LIST1_IN_LIST2 addresses bd_ras
End

(* If an internal BD is fetched, then it is the first BD to fetch.
 *)
Definition PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL:
PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_INTERNAL device_characteristics =
!memory internal_state1 internal_state2 first_bd_ras_was first_bd_update bds fetched_bd_ras_was fetched_bd_update channel_id.
  INTERNAL_BDS device_characteristics
  ==>
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 = (first_bd_ras_was, first_bd_update)::bds /\
  (internal_state2, SOME (fetched_bd_ras_was, fetched_bd_update)) = (coperation device_characteristics channel_id).fetch_bd internal_state1 NONE
  ==>
  first_bd_ras_was = fetched_bd_ras_was /\
  first_bd_update = fetched_bd_update
End

(* If an external BD is fetched, then it is the first BD to fetch.
 *)
Definition PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL:
PROOF_OBLIGATION_FETCHED_BD_IS_FIRST_EXTERNAL device_characteristics =
!memory internal_state1 internal_state2 channel_id addresses tag bytes bd bd_ras bd_was first_bd_update bds fetched_bd_ras_was fetched_bd_update.
  EXTERNAL_BDS device_characteristics
  ==>
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (coperation device_characteristics channel_id).fetch_bd_addresses internal_state1 = (addresses, tag) /\
  bytes = MAP memory addresses /\
  (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 = ((bd, bd_ras, bd_was), first_bd_update)::bds /\
  (internal_state2, SOME (fetched_bd_ras_was, fetched_bd_update)) = (coperation device_characteristics channel_id).fetch_bd internal_state1 (SOME (bytes, tag))
  ==>
  (bd, bd_ras, bd_was) = fetched_bd_ras_was /\
  first_bd_update = fetched_bd_update
End

(* If an internal BD is fetched, then the first BD is removed from the BD queue
 * to fetch.
 *)
Definition PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT:
PROOF_OBLIGATION_FETCHING_INTERNAL_BD_QUEUE_EFFECT device_characteristics =
!internal_state1 internal_state2 channel_id fetch_result memory bd bds.
  INTERNAL_BDS device_characteristics
  ==>
  VALID_CHANNEL_ID device_characteristics channel_id /\
  bd::bds = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  BDS_TO_FETCH_DISJOINT (bd::bds) /\
  (internal_state2, SOME fetch_result) = (coperation device_characteristics channel_id).fetch_bd internal_state1 NONE
  ==>
  (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2 = bds
End

(* If an external BD is fetched, then the first BD is removed from the BD queue
 * to fetch.
 *)
Definition PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT:
PROOF_OBLIGATION_FETCHING_EXTERNAL_BD_QUEUE_EFFECT device_characteristics =
!internal_state1 internal_state2 channel_id fetch_result memory bd bds addresses bytes tag.
  EXTERNAL_BDS device_characteristics
  ==>
  VALID_CHANNEL_ID device_characteristics channel_id /\
  bd::bds = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  BDS_TO_FETCH_DISJOINT (bd::bds) /\
  (addresses, tag) = (coperation device_characteristics channel_id).fetch_bd_addresses internal_state1 /\
  bytes = MAP memory addresses /\
  (internal_state2, SOME fetch_result) = (coperation device_characteristics channel_id).fetch_bd internal_state1 (SOME (bytes, tag))
  ==>
  (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2 = bds
End




(* If no BD is fetched, then the BD queue to fetch is unchanged.
 *)
Definition PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT:
PROOF_OBLIGATION_NOT_FETCHING_BD_NO_BD_QUEUE_EFFECT device_characteristics =
!internal_state1 internal_state2 memory channel_id reply.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (coperation device_characteristics channel_id).fetch_bd internal_state1 reply = (internal_state2, NONE)
  ==>
  (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2
End

(* If BDs are stored internally, then memory has no effect on the BD queue to
 * fetch.
 *)
Definition PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY:
PROOF_OBLIGATION_INTERNAL_BDS_INDEPENDENT_OF_MEMORY device_characteristics =
!internal_state memory1 memory2 channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INTERNAL_BDS device_characteristics
  ==>
  (cverification device_characteristics channel_id).bds_to_fetch memory1 internal_state = (cverification device_characteristics channel_id).bds_to_fetch memory2 internal_state
End

(* Fetching a BD from one queue does not affect any other queue.
 *)
Definition PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE:
PROOF_OBLIGATION_BDS_TO_FETCH_INDEPENDENT_OF_FETCHING_BD_FROM_OTHER_QUEUE device_characteristics =
!channel_id internal_state1 internal_state2 memory reply fetch_result.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, fetch_result) = (coperation device_characteristics channel_id).fetch_bd internal_state1 reply
  ==>
  !channel_id'.
    VALID_CHANNEL_ID device_characteristics channel_id' /\
    channel_id' <> channel_id
    ==>
    (cverification device_characteristics channel_id').bds_to_fetch memory internal_state2 = (cverification device_characteristics channel_id').bds_to_fetch memory internal_state1
End

Definition PROOF_OBLIGATION_FETCH_BD_PRESERVES_OTHER_FETCH_BD_ADDRESSES:
PROOF_OBLIGATION_FETCH_BD_PRESERVES_OTHER_FETCH_BD_ADDRESSES device_characteristics =
!channel_id internal_state1 internal_state2 fetch_result_option reply_option.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, fetch_result_option) = (coperation device_characteristics channel_id).fetch_bd internal_state1 reply_option
  ==>
  !channel_id'.
    VALID_CHANNEL_ID device_characteristics channel_id' /\
    channel_id' <> channel_id
    ==>
    (coperation device_characteristics channel_id').fetch_bd_addresses internal_state2 =
    (coperation device_characteristics channel_id').fetch_bd_addresses internal_state1
End

Definition PROOF_OBLIGATION_UPDATE_BD_PRESERVES_FETCH_BD_ADDRESSES:
PROOF_OBLIGATION_UPDATE_BD_PRESERVES_FETCH_BD_ADDRESSES device_characteristics =
!channel_id internal_state1 internal_state2 write_address_bytes tag update_status bd_ras_was.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, write_address_bytes, tag, update_status) = (coperation device_characteristics channel_id).update_bd internal_state1 bd_ras_was
  ==>
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (coperation device_characteristics channel_id).fetch_bd_addresses internal_state2 =
    (coperation device_characteristics channel_id).fetch_bd_addresses internal_state1
End

Definition PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_FETCH_BD_ADDRESSES:
PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_FETCH_BD_ADDRESSES device_characteristics =
!channel_id internal_state1 internal_state2 requests complete bd replies.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, requests, complete) = (coperation device_characteristics channel_id).process_replies_generate_requests internal_state1 bd replies
  ==>
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (coperation device_characteristics channel_id).fetch_bd_addresses internal_state2 =
    (coperation device_characteristics channel_id).fetch_bd_addresses internal_state1
End

Definition PROOF_OBLIGATION_WRITE_BACK_BD_PRESERVES_FETCH_BD_ADDRESSES:
PROOF_OBLIGATION_WRITE_BACK_BD_PRESERVES_FETCH_BD_ADDRESSES device_characteristics =
!channel_id internal_state1 internal_state2 write_address_bytes tag released_bds environment bds_to_write_back.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, write_address_bytes, tag, released_bds) = (coperation device_characteristics channel_id).write_back_bd environment internal_state1 bds_to_write_back
  ==>
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (coperation device_characteristics channel_id).fetch_bd_addresses internal_state2 =
    (coperation device_characteristics channel_id).fetch_bd_addresses internal_state1
End

Definition PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_REPLIES_PRESERVES_FETCH_BD_ADDRESSES:
PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_REPLIES_PRESERVES_FETCH_BD_ADDRESSES device_characteristics =
!internal_state1 internal_state2 requests replies processed_replies.
  (internal_state2, processed_replies) = device_characteristics.dma_characteristics.process_register_related_memory_replies internal_state1 requests replies
  ==>
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (coperation device_characteristics channel_id).fetch_bd_addresses internal_state2 =
    (coperation device_characteristics channel_id).fetch_bd_addresses internal_state1
End



(******************************************************************************)
(*Proof obligations related to updating BDs.***********************************)
(******************************************************************************)

(* If a BD is updated, then the declared addresses to write are a subset of the
 * write addresses of the BD to update.
 *)
Definition PROOF_OBLIGATION_DECLARED_UPDATE_WRITES_BD_WAS:
PROOF_OBLIGATION_DECLARED_UPDATE_WRITES_BD_WAS device_characteristics =
!internal_state channel_id bd bd_ras bd_was write_addresses.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (cverification device_characteristics channel_id).update_bd_addresses internal_state (bd, bd_ras, bd_was) = write_addresses
  ==>
  LIST1_IN_LIST2 write_addresses bd_was
End

(* If a BD is updated, then the addresses to write are a subset of the
 * declared write addresses of the BD to update.
 *)
Definition PROOF_OBLIGATION_UPDATE_WRITES_DECLARED:
PROOF_OBLIGATION_UPDATE_WRITES_DECLARED device_characteristics =
!internal_state1 internal_state2 tag update_status channel_id bd_ras_was write_addresses write_address_bytes.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  write_addresses = (cverification device_characteristics channel_id).update_bd_addresses internal_state1 bd_ras_was /\
  (internal_state2, write_address_bytes, tag, update_status) = (coperation device_characteristics channel_id).update_bd internal_state1 bd_ras_was
  ==>
  LIST1_IN_LIST2 (MAP FST write_address_bytes) write_addresses
End

(* Updating an internal BD disjoint from other BDs to fetch preserves the BD
 * queue to fetch.
 *)
Definition PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL:
PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics =
!internal_state1 internal_state2 channel_id memory bd bd_ras bd_was write_addresses write_address_bytes tag update_status.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INTERNAL_BDS device_characteristics /\
  write_addresses = (cverification device_characteristics channel_id).update_bd_addresses internal_state1 (bd, bd_ras, bd_was) /\
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory internal_state1 write_addresses /\
  (internal_state2, write_address_bytes, tag, update_status) = (coperation device_characteristics channel_id).update_bd internal_state1 (bd, bd_ras, bd_was)
  ==>
  !channel_id memory.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2
End

(* Obtaining the requests for updating an external BD preserves all BD queues to
 * fetch.
 *)
Definition PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST:
PROOF_OBLIGATION_UPDATING_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics =
!internal_state1 internal_state2 channel_id bd_ras_was write_address_bytes tag update_status.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  EXTERNAL_BDS device_characteristics /\
  (internal_state2, write_address_bytes, tag, update_status) = (coperation device_characteristics channel_id).update_bd internal_state1 bd_ras_was
  ==>
  !channel_id memory.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1
End



(******************************************************************************)
(*Proof obligations related to transferring data.******************************)
(******************************************************************************)

(* Fetching BDs does not affect the interpretation of which read and write
 * locations a BD addresses.
 *)
Definition PROOF_OBLIGATION_FETCHING_BD_PRESERVES_BD_INTERPRETATION:
PROOF_OBLIGATION_FETCHING_BD_PRESERVES_BD_INTERPRETATION device_characteristics =
!internal_state1 internal_state2 channel_id reply fetched_bd.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (coperation device_characteristics channel_id).fetch_bd internal_state1 reply = (internal_state2, fetched_bd)
  ==>
  !channel_id bd.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state1 bd = (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state2 bd
End

(* Updating BDs does not affect the interpretation of which read and write
 * locations a BD addresses.
 *)
Definition PROOF_OBLIGATION_UPDATING_BD_PRESERVES_BD_INTERPRETATION:
PROOF_OBLIGATION_UPDATING_BD_PRESERVES_BD_INTERPRETATION device_characteristics =
!internal_state1 internal_state2 channel_id bd_ras_was bytes tag update_status.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (coperation device_characteristics channel_id).update_bd internal_state1 bd_ras_was = (internal_state2, bytes, tag, update_status)
  ==>
  !channel_id bd.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state1 bd = (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state2 bd
End

(* Generating and processing interconnect requests do not affect the
 * interpretation of which read and write locations a BD addresses.
 *)
Definition PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION:
PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_BD_INTERPRETATION device_characteristics =
!internal_state1 internal_state2 channel_id bd replies new_requests complete.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, new_requests, complete) = (coperation device_characteristics channel_id).process_replies_generate_requests internal_state1 bd replies
  ==>
  !channel_id bd.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state1 bd = (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state2 bd
End

(* Processing and generating requests does not affect the BD queue to fetch.
 *)
Definition PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH:
PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics =
!internal_state1 internal_state2 channel_id replies new_requests complete bd.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, new_requests, complete) = (coperation device_characteristics channel_id).process_replies_generate_requests internal_state1 bd replies
  ==>
  !channel_id memory.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2
End

(* The generated interconnect requests specify addresses accesses that are
 * consistent with the address accesses specified by BDs.
 *)
Definition PROOF_OBLIGATION_READ_REQUESTS_CONSISTENT_WITH_BD:
PROOF_OBLIGATION_READ_REQUESTS_CONSISTENT_WITH_BD device_characteristics =
!internal_state1 internal_state2 channel_id bd replies new_requests complete addresses tag.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, new_requests, complete) = (coperation device_characteristics channel_id).process_replies_generate_requests internal_state1 bd replies /\
  MEM (request_read addresses tag) new_requests
  ==>
  ?ras was.
    (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state1 bd = (ras, was) /\
    LIST1_IN_LIST2 addresses ras
End

Definition PROOF_OBLIGATION_WRITE_REQUESTS_CONSISTENT_WITH_BD:
PROOF_OBLIGATION_WRITE_REQUESTS_CONSISTENT_WITH_BD device_characteristics =
!internal_state1 internal_state2 channel_id bd replies new_requests complete address_bytes tag.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, new_requests, complete) = (coperation device_characteristics channel_id).process_replies_generate_requests internal_state1 bd replies /\
  MEM (request_write address_bytes tag) new_requests
  ==>
  ?ras was.
    (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state1 bd = (ras, was) /\
    LIST1_IN_LIST2 (MAP FST address_bytes) was
End

(* Writing back BDs does not affect the interpretation of which read and write
 * locations a BD addresses.
 *)
Definition PROOF_OBLIGATION_WRITE_BACK_PRESERVES_BD_INTERPRETATION:
PROOF_OBLIGATION_WRITE_BACK_PRESERVES_BD_INTERPRETATION device_characteristics =
!environment internal_state1 internal_state2 channel_id bds_to_write_back bytes tag bds_remaining_to_write_back.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, bytes, tag, bds_remaining_to_write_back) = (coperation device_characteristics channel_id).write_back_bd environment internal_state1 bds_to_write_back
  ==>
  !channel_id bd.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state1 bd = (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state2 bd
End

Definition PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION:
PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION device_characteristics =
!environment function_state internal_state1 internal_state2 channels channel_id dma_operation.
  (internal_state2, channel_id, dma_operation) = device_characteristics.dma_characteristics.scheduler environment function_state internal_state1 channels
  ==>
  !channel_id bd.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state1 bd = (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state2 bd
End

Definition PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_BD_INTERPRETATION:
PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_BD_INTERPRETATION device_characteristics =
!internal_state1 internal_state2 completed_pending_memory_replies pending_memory_requests pending_memory_replies.
  (internal_state2, completed_pending_memory_replies) = device_characteristics.dma_characteristics.process_register_related_memory_replies internal_state1 pending_memory_requests pending_memory_replies
  ==>
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    !bd.
      (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state1 bd = (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state2 bd
End

Definition PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BD_INTERPRETATION:
PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BD_INTERPRETATION device_characteristics =
!internal_state1 internal_state2 read_bytes addresses requests.
  (internal_state2, read_bytes, requests) = device_characteristics.dma_characteristics.register_read internal_state1 addresses
  ==>
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    !bd.
      (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state1 bd = (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state2 bd
End

Definition PROOF_OBLIGATION_REGISTER_WRITE_PRESERVES_BD_INTERPRETATION:
PROOF_OBLIGATION_REGISTER_WRITE_PRESERVES_BD_INTERPRETATION device_characteristics =
!internal_state1 internal_state2 requests address_bytes.
  (internal_state2, requests) = device_characteristics.dma_characteristics.register_write internal_state1 address_bytes
  ==>
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    !bd.
      (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state1 bd = (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state2 bd
End




(******************************************************************************)
(*Proof obligations related to writing back BDs.*******************************)
(******************************************************************************)

(* Declared write back addresses are a part of the BD write addresses of a BD in
 * the queue of BDs to write back.
 *)
Definition PROOF_OBLIGATION_DECLARED_WRITE_BACK_WRITES_BD_WAS:
PROOF_OBLIGATION_DECLARED_WRITE_BACK_WRITES_BD_WAS device_characteristics =
!environment internal_state channel_id bds_to_write_back write_addresses write_address.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  write_addresses = (cverification device_characteristics channel_id).write_back_bd_addresses environment internal_state bds_to_write_back /\
  MEM write_address write_addresses
  ==>
  ?bd bd_ras bd_was.
    MEM (bd, bd_ras, bd_was) bds_to_write_back /\
    MEM write_address bd_was
End

(* If a BD is written back, then the addresses to write are a subset of the
 * declared write addresses of the BD to write back.
 *)
Definition PROOF_OBLIGATION_WRITE_BACK_WRITES_DECLARED:
PROOF_OBLIGATION_WRITE_BACK_WRITES_DECLARED device_characteristics =
!channel_id internal_state1 internal_state2 write_addresses environment bds_to_write_back write_address_bytes tag released_bds.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  write_addresses = (cverification device_characteristics channel_id).write_back_bd_addresses environment internal_state1 bds_to_write_back /\
  (internal_state2, write_address_bytes, tag, released_bds) = (coperation device_characteristics channel_id).write_back_bd environment internal_state1 bds_to_write_back
  ==>
  LIST1_IN_LIST2 (MAP FST write_address_bytes) write_addresses
End

(* Writing back an internal BD that does not overlap any BD to fetch does not
 * modify the BD queue to fetch.
 *)
Definition PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL:
PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_BD_QUEUE_INTERNAL device_characteristics =
!environment internal_state1 internal_state2 channel_id memory bds_to_write_back write_addresses bytes tag released_bds.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INTERNAL_BDS device_characteristics /\
  write_addresses = (cverification device_characteristics channel_id).write_back_bd_addresses environment internal_state1 bds_to_write_back /\
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory internal_state1 write_addresses /\
  (internal_state2, bytes, tag, released_bds) = (coperation device_characteristics channel_id).write_back_bd environment internal_state1 bds_to_write_back
  ==>
  !channel_id memory.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1
End

(* Obtaining write requests for writing back an external BD does not modify the
 * BD queue to fetch.
 *)
Definition PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST:
PROOF_OBLIGATION_WRITING_BACK_DISJOINT_BD_PRESERVES_EXTERNAL_BD_QUEUES_REQUEST device_characteristics =
!environment internal_state1 internal_state2 channel_id bds_to_write_back write_address_bytes tag released_bds.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  EXTERNAL_BDS device_characteristics /\
  (internal_state2, write_address_bytes, tag, released_bds) = (coperation device_characteristics channel_id).write_back_bd environment internal_state1 bds_to_write_back
  ==>
  !channel_id memory.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1
End



(* Proof obligation of the scheduler: The scheduler selects a channel that is
 * considered valid.
 *)
Definition PROOF_OBLIGATION_SCHEDULER:
PROOF_OBLIGATION_SCHEDULER device_characteristics =
!environment function_state internal_state1 internal_state2 channels channel_id dma_operation.
  (internal_state2, channel_id, dma_operation) = device_characteristics.dma_characteristics.scheduler environment function_state internal_state1 channels
  ==>
  VALID_CHANNEL_ID device_characteristics channel_id
End

(* The scheduler does not change the queues of BDs to fetch. *)
Definition PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH:
PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH device_characteristics =
!environment function_state internal_state1 internal_state2 channels channel_id dma_operation.
  (internal_state2, channel_id, dma_operation) = device_characteristics.dma_characteristics.scheduler environment function_state internal_state1 channels
  ==>
  !channel_id memory.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1
End

(* The scheduler does not change the addresses of the next BDs to fetch. *)
Definition PROOF_OBLIGATION_SCHEDULER_PRESERVES_FETCH_BD_ADDRESSES:
PROOF_OBLIGATION_SCHEDULER_PRESERVES_FETCH_BD_ADDRESSES device_characteristics =
!environment function_state internal_state1 internal_state2 channels channel_id dma_operation.
  (internal_state2, channel_id, dma_operation) = device_characteristics.dma_characteristics.scheduler environment function_state internal_state1 channels
  ==>
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (coperation device_characteristics channel_id).fetch_bd_addresses internal_state2 = (coperation device_characteristics channel_id).fetch_bd_addresses internal_state1
End









(******************************************************************************)
(*Proof obligations related to processing memory request replies due to the****)
(*CPU accessing a DMA register.************************************************)
(******************************************************************************)

(* Processing memory request replies due to requests from DMA register accesses
 * do not affect BDs to fetch.
 *)
Definition PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLY_PRESERVES_BDS_TO_FETCH:
PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLY_PRESERVES_BDS_TO_FETCH device_characteristics =
!internal_state1 internal_state2 pending_memory_requests pending_memory_replies processed_pending_memory_replies memory.
  (internal_state2, processed_pending_memory_replies) = device_characteristics.dma_characteristics.process_register_related_memory_replies internal_state1 pending_memory_requests pending_memory_replies
  ==>
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1
End









(******************************************************************************)
(*Proof obligations related to scratchpad.*************************************)
(******************************************************************************)

Definition PROOF_OBLIGATION_SCHEDULER_PRESERVES_SCRATCHPAD:
PROOF_OBLIGATION_SCHEDULER_PRESERVES_SCRATCHPAD device_characteristics =
!environment function_state internal_state1 internal_state2 channels channel_id dma_operation.
  (internal_state2, channel_id, dma_operation) = device_characteristics.dma_characteristics.scheduler environment function_state internal_state1 channels
  ==>
  device_characteristics.dma_characteristics.scratchpad_addresses internal_state2 = device_characteristics.dma_characteristics.scratchpad_addresses internal_state1
End

Definition PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_SCRATCHPAD:
PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_SCRATCHPAD device_characteristics =
!internal_state1 internal_state2 completed_pending_memory_replies pending_memory_requests pending_memory_replies.
  (internal_state2, completed_pending_memory_replies) = device_characteristics.dma_characteristics.process_register_related_memory_replies internal_state1 pending_memory_requests pending_memory_replies
  ==>
  device_characteristics.dma_characteristics.scratchpad_addresses internal_state2 = device_characteristics.dma_characteristics.scratchpad_addresses internal_state1
End

Definition PROOF_OBLIGATION_FETCH_BD_PRESERVES_SCRATCHPAD:
PROOF_OBLIGATION_FETCH_BD_PRESERVES_SCRATCHPAD device_characteristics =
!internal_state1 internal_state2 fetch_result channel_id reply_option.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, fetch_result) = (coperation device_characteristics channel_id).fetch_bd internal_state1 reply_option
  ==>
  device_characteristics.dma_characteristics.scratchpad_addresses internal_state2 = device_characteristics.dma_characteristics.scratchpad_addresses internal_state1
End

Definition PROOF_OBLIGATION_UPDATE_BD_PRESERVES_SCRATCHPAD:
PROOF_OBLIGATION_UPDATE_BD_PRESERVES_SCRATCHPAD device_characteristics =
!bytes tag update_status internal_state1 internal_state2 channel_id bd_ras_was.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, bytes, tag, update_status) = (coperation device_characteristics channel_id).update_bd internal_state1 bd_ras_was
  ==>
  device_characteristics.dma_characteristics.scratchpad_addresses internal_state2 = device_characteristics.dma_characteristics.scratchpad_addresses internal_state1
End

Definition PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_SCRATCHPAD:
PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_SCRATCHPAD device_characteristics =
!channel_id internal_state1 bd replies internal_state2 new_requests complete.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, new_requests, complete) = (coperation device_characteristics channel_id).process_replies_generate_requests internal_state1 bd replies
  ==>
  device_characteristics.dma_characteristics.scratchpad_addresses internal_state2 = device_characteristics.dma_characteristics.scratchpad_addresses internal_state1
End

Definition PROOF_OBLIGATION_WRITE_BACK_BD_PRESERVES_SCRATCHPAD:
PROOF_OBLIGATION_WRITE_BACK_BD_PRESERVES_SCRATCHPAD device_characteristics =
!channel_id internal_state1 internal_state2 bytes tag bds_released environment bds_to_write_back.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, bytes, tag, bds_released) = (coperation device_characteristics channel_id).write_back_bd environment internal_state1 bds_to_write_back
  ==>
  device_characteristics.dma_characteristics.scratchpad_addresses internal_state2 = device_characteristics.dma_characteristics.scratchpad_addresses internal_state1
End

Definition PROOF_OBLIGATION_REGISTER_READ_PRESERVES_SCRATCHPAD:
PROOF_OBLIGATION_REGISTER_READ_PRESERVES_SCRATCHPAD device_characteristics =
!internal_state1 internal_state2 register_addresses read_bytes requests.
  (internal_state2, read_bytes, requests) = device_characteristics.dma_characteristics.register_read internal_state1 register_addresses
  ==>
  device_characteristics.dma_characteristics.scratchpad_addresses internal_state2 = device_characteristics.dma_characteristics.scratchpad_addresses internal_state1
End

Definition PROOF_OBLIGATION_REGISTER_READ_MEMORY_READ_REQUESTS_ADDRESS_SCRATCHPAD:
PROOF_OBLIGATION_REGISTER_READ_MEMORY_READ_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics =
!internal_state1 internal_state2 scratchpad_addresses read_bytes requests register_addresses addresses tag.
  scratchpad_addresses = device_characteristics.dma_characteristics.scratchpad_addresses internal_state1 /\
  (internal_state2, read_bytes, requests) = device_characteristics.dma_characteristics.register_read internal_state1 register_addresses /\
  MEM (request_read addresses tag) requests
  ==>
  LIST1_IN_LIST2 addresses scratchpad_addresses
End

Definition PROOF_OBLIGATION_REGISTER_READ_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD:
PROOF_OBLIGATION_REGISTER_READ_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics =
!internal_state1 internal_state2 scratchpad_addresses read_bytes requests register_addresses address_bytes tag.
  scratchpad_addresses = device_characteristics.dma_characteristics.scratchpad_addresses internal_state1 /\
  (internal_state2, read_bytes, requests) = device_characteristics.dma_characteristics.register_read internal_state1 register_addresses /\
  MEM (request_write address_bytes tag) requests
  ==>
  LIST1_IN_LIST2 (MAP FST address_bytes) scratchpad_addresses
End

Definition PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_READ_REQUESTS_ADDRESS_SCRATCHPAD:
PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_READ_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics =
!internal_state1 internal_state2 register_address_bytes scratchpad_addresses requests addresses tag.
  scratchpad_addresses = device_characteristics.dma_characteristics.scratchpad_addresses internal_state1 /\
  (internal_state2, requests) = device_characteristics.dma_characteristics.register_write internal_state1 register_address_bytes /\
  MEM (request_read addresses tag) requests
  ==>
  LIST1_IN_LIST2 addresses scratchpad_addresses
End

Definition PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD:
PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics =
!internal_state1 internal_state2 register_address_bytes scratchpad_addresses requests address_bytes tag.
  scratchpad_addresses = device_characteristics.dma_characteristics.scratchpad_addresses internal_state1 /\
  (internal_state2, requests) = device_characteristics.dma_characteristics.register_write internal_state1 register_address_bytes /\
  MEM (request_write address_bytes tag) requests
  ==>
  LIST1_IN_LIST2 (MAP FST address_bytes) scratchpad_addresses
End

(* BD queue may depend on only BDs to fetch and scratchpad.
 *)
Definition PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE:
PROOF_OBLIGATION_SAME_BD_QUEUE_LOCATIONS_PRESERVE_BD_QUEUE device_characteristics =
!channel_id memory1 memory2 internal_state bds_to_fetch1 bds_to_fetch_ras1.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory1 internal_state /\
  bds_to_fetch_ras1 = bds_to_fetch_ras bds_to_fetch1 /\
  (!address. MEM address bds_to_fetch_ras1 ==> memory1 address = memory2 address)
  ==>
  (cverification device_characteristics channel_id).bds_to_fetch memory2 internal_state = bds_to_fetch1
End

(* Register reads preserve BDs to fetch.
 *)
Definition PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH:
PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics =
!internal_state1 internal_state2 read_bytes requests register_read_addresses.
  (internal_state2, read_bytes, requests) = device_characteristics.dma_characteristics.register_read internal_state1 register_read_addresses
  ==>
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    !memory.
      (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2 =
      (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1
End

(* Register reads preserves addresses of next BD to fetch.
 *)
Definition PROOF_OBLIGATION_REGISTER_READ_PRESERVES_FETCH_BD_ADDRESSES:
PROOF_OBLIGATION_REGISTER_READ_PRESERVES_FETCH_BD_ADDRESSES device_characteristics =
!internal_state1 internal_state2 addresses bytes requests.
  (internal_state2, bytes, requests) = device_characteristics.dma_characteristics.register_read internal_state1 addresses
  ==>
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (coperation device_characteristics channel_id).fetch_bd_addresses internal_state2 =
    (coperation device_characteristics channel_id).fetch_bd_addresses internal_state1
End

(*
Definition PROOF_OBLIGATION_CPU_DOES_NOT_WRITE_SCRATCH_PAD:
PROOF_OBLIGATION_CPU_DOES_NOT_WRITE_SCRATCH_PAD INVARIANT_CPU cpu_transition device_characteristics =
!memory cpu1 cpu2 internal_state register_address_bytes scratchpad_addresses.
  INVARIANT_CPU memory cpu1 /\																		(* Needed to restrict written values to DMAC registers. *)
  cpu_transition cpu1 (cpu_memory_write register_address_bytes) cpu2 /\
  scratchpad_addresses = device_characteristics.dma_characteristics.scratchpad_addresses internal_state
  ==>
  DISJOINT_LISTS (MAP FST register_address_bytes) scratchpad_addresses
End
*)

Definition SCRATCHPAD_R:
SCRATCHPAD_R device_characteristics memory internal_state =
!scratchpad_addresses.
  scratchpad_addresses = device_characteristics.dma_characteristics.scratchpad_addresses internal_state
  ==>
  EVERY (device_characteristics.dma_characteristics.R memory) scratchpad_addresses
End

Definition SCRATCHPAD_W:
SCRATCHPAD_W device_characteristics memory internal_state =
!scratchpad_addresses.
  scratchpad_addresses = device_characteristics.dma_characteristics.scratchpad_addresses internal_state
  ==>
  EVERY (device_characteristics.dma_characteristics.W memory) scratchpad_addresses
End

Definition SCRATCHPAD_R_W:
SCRATCHPAD_R_W device_characteristics memory internal_state = (
  SCRATCHPAD_R device_characteristics memory internal_state /\
  SCRATCHPAD_W device_characteristics memory internal_state
)
End







(******************************************************************************)
(*Proof obligation stating that the what is readable and writable does not    *)
(*depend on writable memory region.                                           *)
(******************************************************************************)

Definition PROOF_OBLIGATION_READABLE_WRITABLE:
PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics =
!memory1 memory2.
  (!address. ~device_characteristics.dma_characteristics.W memory1 address ==> memory1 address = memory2 address)
  ==>
  device_characteristics.dma_characteristics.R memory1 = device_characteristics.dma_characteristics.R memory2 /\
  device_characteristics.dma_characteristics.W memory1 = device_characteristics.dma_characteristics.W memory2
End



(******************************************************************************
 *Proof obligations and predicates related to the proof obligation related to *
 *the CPU.                                                                    *
 ******************************************************************************)

(*
Definition PROOF_OBLIGATION_CPU_PRESERVES_INVARIANT_CPU:
PROOF_OBLIGATION_CPU_PRESERVES_INVARIANT_CPU INVARIANT_CPU cpu_transition =
!cpu1 cpu2 memory1 memory2 operation address_bytes.
  cpu_transition cpu1 operation cpu2 /\
  (operation =  cpu_memory_write address_bytes ==> memory2 = update_memory memory1 address_bytes) /\
  (operation <> cpu_memory_write address_bytes ==> memory2 = memory1) /\
  INVARIANT_CPU memory1 cpu1
  ==>
  INVARIANT_CPU memory2 cpu2
End
*)

Definition MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W:
MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W device_characteristics internal_state1 memory1 memory2 =
!channel_id EXTERNAL_MEMORY_BDS R W bds_to_fetch1 bds_to_fetch2 bd_transfer_ras_was.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  EXTERNAL_MEMORY_BDS = EXTERNAL_BDS device_characteristics /\
  R = device_characteristics.dma_characteristics.R memory2 /\
  W = device_characteristics.dma_characteristics.W memory2 /\
  bds_to_fetch1 = (cverification device_characteristics channel_id).bds_to_fetch memory1 internal_state1 /\
  bds_to_fetch2 = (cverification device_characteristics channel_id).bds_to_fetch memory2 internal_state1 /\
  bd_transfer_ras_was = (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state1
  ==>
  ?bd_ras_was_us.
    bds_to_fetch2 = bds_to_fetch1 ++ bd_ras_was_us /\
    (!bd bd_ras bd_was u ras_was. MEM ((bd, bd_ras, bd_was), u) bd_ras_was_us /\ ras_was = bd_transfer_ras_was bd ==> BD_READ R EXTERNAL_MEMORY_BDS bd_ras /\ BD_WRITE W EXTERNAL_MEMORY_BDS bd_was /\ BD_DATA R W ras_was)
End

Definition IDLE_DMAC:
IDLE_DMAC device_characteristics device =
!channel_id bds_to_fetch bds_to_update bds_to_process bds_to_write_back.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  bds_to_fetch = (schannel device channel_id).queue.bds_to_fetch /\
  bds_to_update = (schannel device channel_id).queue.bds_to_update /\
  bds_to_process = (schannel device channel_id).queue.bds_to_process /\
  bds_to_write_back = (schannel device channel_id).queue.bds_to_write_back
  ==>
  bds_to_fetch = [] /\
  bds_to_update = [] /\
  bds_to_process = [] /\
  bds_to_write_back = []
End

Definition NO_CHANNEL_MEMORY_REQUESTS:
NO_CHANNEL_MEMORY_REQUESTS device_characteristics device =
!channel_id fetch_requests update_requests process_requests write_back_requests.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  fetch_requests = (schannel device channel_id).pending_accesses.requests.fetching_bd /\
  update_requests = (schannel device channel_id).pending_accesses.requests.updating_bd /\
  process_requests = (schannel device channel_id).pending_accesses.requests.transferring_data /\
  write_back_requests = (schannel device channel_id).pending_accesses.requests.writing_back_bd
  ==>
  fetch_requests = NONE /\
  update_requests = [] /\
  process_requests = [] /\
  write_back_requests = []
End

Definition NO_REGISTER_RELATED_MEMORY_REQUEST:
NO_REGISTER_RELATED_MEMORY_REQUEST device = (
  device.dma_state.pending_register_related_memory_requests = []
)
End

(* DMAC is in a state in which it may access memory. *)
Definition DMAC_CAN_ACCESS_MEMORY:
DMAC_CAN_ACCESS_MEMORY device_characteristics device = (
  ~IDLE_DMAC device_characteristics device \/
  ~NO_CHANNEL_MEMORY_REQUESTS device_characteristics device \/
  ~NO_REGISTER_RELATED_MEMORY_REQUEST device
)
End

val _ = export_theory();
