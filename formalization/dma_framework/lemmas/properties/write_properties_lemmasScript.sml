open HolKernel Parse boolLib bossLib helper_tactics;
open operationsTheory write_propertiesTheory access_propertiesTheory proof_obligationsTheory;

val _ = new_theory "write_properties_lemmas";

Theorem FETCHING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES_IMPLY_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA:
!W memory channel addresses address_bytes tag.
  FETCHING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel /\
  addresses = MAP FST address_bytes /\
  MEM (request_write address_bytes tag) (collect_pending_fetch_bd_request channel.pending_accesses.requests.fetching_bd)
  ==>
  EVERY (W memory) addresses
Proof
INTRO_TAC THEN
PTAC FETCHING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
PTAC collect_pending_fetch_bd_request THENL
[
 ETAC listTheory.MEM THEN
 SOLVE_F_ASM_TAC
 ,
 ETAC listTheory.MEM THEN
 REMOVE_F_DISJUNCTS_TAC THEN
 AITAC THEN
 STAC
]
QED

Theorem UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES_IMPLY_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA:
!W memory channel addresses address_bytes tag.
  UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel /\
  addresses = MAP FST address_bytes /\
  MEM (request_write address_bytes tag) channel.pending_accesses.requests.updating_bd
  ==>
  EVERY (W memory) addresses
Proof
INTRO_TAC THEN
PTAC UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
AIRTAC THEN
STAC
QED

Theorem TRANSFERRING_DATA_CHANNEL_REQUESTING_WRITE_ADDRESSES_IMPLY_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA:
!W memory channel addresses address_bytes tag.
  TRANSFERRING_DATA_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel /\
  addresses = MAP FST address_bytes /\
  MEM (request_write address_bytes tag) channel.pending_accesses.requests.transferring_data
  ==>
  EVERY (W memory) addresses
Proof
INTRO_TAC THEN
PTAC TRANSFERRING_DATA_CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
AIRTAC THEN
STAC
QED

Theorem WRITING_BACK_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES_IMPLY_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA:
!W memory channel addresses address_bytes tag.
  WRITING_BACK_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel /\
  addresses = MAP FST address_bytes /\
  MEM (request_write address_bytes tag) channel.pending_accesses.requests.writing_back_bd
  ==>
  EVERY (W memory) addresses
Proof
INTRO_TAC THEN
PTAC WRITING_BACK_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
AIRTAC THEN
STAC
QED

Theorem OPERATIONS_CHANNEL_REQUESTING_WRITE_ADDRESSES_IMPLY_CHANNEL_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA:
!W memory channel.
  FETCHING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel /\
  UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel /\
  TRANSFERRING_DATA_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel /\
  WRITING_BACK_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel
  ==>
  CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel
Proof
INTRO_TAC THEN
PTAC CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
INTRO_TAC THEN
PTAC channel_pending_requests THEN
ETAC listTheory.MEM_APPEND THEN
REPEAT SPLIT_ASM_DISJS_TAC THENL
[
 IRTAC FETCHING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES_IMPLY_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA THEN STAC
 ,
 IRTAC UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES_IMPLY_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA THEN STAC
 ,
 IRTAC TRANSFERRING_DATA_CHANNEL_REQUESTING_WRITE_ADDRESSES_IMPLY_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA THEN STAC
 ,
 IRTAC WRITING_BACK_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES_IMPLY_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA THEN STAC
]
QED



Theorem EQUAL_FETCHING_BD_REQUESTS_PRESERVES_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA:
!W memory channel1 channel2.
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  FETCHING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel1
  ==>
  FETCHING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel2
Proof
INTRO_TAC THEN
ETAC FETCHING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
STAC
QED

Theorem EQUAL_UPDATING_BD_REQUESTS_PRESERVES_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA:
!W memory channel1 channel2.
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel1
  ==>
  UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel2
Proof
INTRO_TAC THEN
ETAC UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
STAC
QED

Theorem EQUAL_TRANSFERRING_DATA_REQUESTS_PRESERVES_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA:
!W memory channel1 channel2.
  channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data /\
  TRANSFERRING_DATA_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel1
  ==>
  TRANSFERRING_DATA_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel2
Proof
INTRO_TAC THEN
ETAC TRANSFERRING_DATA_CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
STAC
QED

Theorem EQUAL_WRITING_BACK_BD_REQUESTS_PRESERVES_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA:
!W memory channel1 channel2.
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd /\
  WRITING_BACK_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel1
  ==>
  WRITING_BACK_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel2
Proof
INTRO_TAC THEN
ETAC WRITING_BACK_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
STAC
QED

Theorem CHANNEL_REQUESTING_WRITE_ADDRESSES_IMPLY_FETCHING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA:
!W memory channel.
  CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel
  ==>
  FETCHING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel
Proof
INTRO_TAC THEN
PTAC FETCHING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
INTRO_TAC THEN
PTAC CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
PTAC channel_pending_requests THEN
PTAC collect_pending_fetch_bd_request THENL
[
 LRTAC THEN HYP_CONTR_NEQ_LEMMA_TAC optionTheory.NOT_SOME_NONE
 ,
 RW_HYPS_TAC listTheory.MEM_APPEND THEN
 RW_HYPS_TAC listTheory.MEM THEN
 INST_IMP_ASM_GOAL_TAC THEN
 LRTAC THEN
 ETAC optionTheory.option_CLAUSES THEN
 STAC
]
QED

Theorem CHANNEL_REQUESTING_WRITE_ADDRESSES_IMPLY_UPDATIING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA:
!W memory channel.
  CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel
  ==>
  UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel
Proof
INTRO_TAC THEN
PTAC UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
INTRO_TAC THEN
PTAC CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
PTAC channel_pending_requests THEN
INST_IMP_ASM_GOAL_TAC THEN
REWRITE_TAC [listTheory.MEM_APPEND] THEN
STAC
QED

Theorem CHANNEL_REQUESTING_WRITE_ADDRESSES_IMPLY_TRANSFERRING_DATA_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA:
!W memory channel.
  CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel
  ==>
  TRANSFERRING_DATA_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel
Proof
INTRO_TAC THEN
PTAC TRANSFERRING_DATA_CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
INTRO_TAC THEN
PTAC CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
PTAC channel_pending_requests THEN
INST_IMP_ASM_GOAL_TAC THEN
REWRITE_TAC [listTheory.MEM_APPEND] THEN
STAC
QED

Theorem CHANNEL_REQUESTING_WRITE_ADDRESSES_IMPLY_WRITING_BACK_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA:
!W memory channel.
  CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel
  ==>
  WRITING_BACK_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel
Proof
INTRO_TAC THEN
PTAC WRITING_BACK_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
INTRO_TAC THEN
PTAC CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
PTAC channel_pending_requests THEN
INST_IMP_ASM_GOAL_TAC THEN
REWRITE_TAC [listTheory.MEM_APPEND] THEN
STAC
QED

Theorem CHANNEL_REQUESTING_WRITE_ADDRESSES_IMPLY_OPERATIONS_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA:
!W memory channel.
  CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel
  ==>
  FETCHING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel /\
  UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel /\
  TRANSFERRING_DATA_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel /\
  WRITING_BACK_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel
Proof
INTRO_TAC THEN
ITAC CHANNEL_REQUESTING_WRITE_ADDRESSES_IMPLY_FETCHING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA THEN
ITAC CHANNEL_REQUESTING_WRITE_ADDRESSES_IMPLY_UPDATIING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA THEN
ITAC CHANNEL_REQUESTING_WRITE_ADDRESSES_IMPLY_TRANSFERRING_DATA_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA THEN
ITAC CHANNEL_REQUESTING_WRITE_ADDRESSES_IMPLY_WRITING_BACK_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA THEN
STAC
QED

Theorem CHANNEL_REQUESTING_WRITE_ADDRESSES_EQ_OPERATIONS_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA:
!W memory channel.
  CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel
  =
  (FETCHING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel /\
   UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel /\
   TRANSFERRING_DATA_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel /\
   WRITING_BACK_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel)
Proof
REPEAT GEN_TAC THEN
EQ_TAC THENL
[
 REWRITE_TAC [CHANNEL_REQUESTING_WRITE_ADDRESSES_IMPLY_OPERATIONS_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA]
 ,
 REWRITE_TAC [OPERATIONS_CHANNEL_REQUESTING_WRITE_ADDRESSES_IMPLY_CHANNEL_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA]
]
QED

Theorem APPENDING_WRITABLE_WRITE_REQUEST_PRESERVES_UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA:
!write_address_bytes write_addresses W memory channel1 channel2 tag.
  EVERY (W memory) write_addresses /\
  LIST1_IN_LIST2 (MAP FST write_address_bytes) write_addresses /\
  channel2.pending_accesses.requests.updating_bd =
  channel1.pending_accesses.requests.updating_bd ++ [request_write write_address_bytes tag] /\
  UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel1
  ==>
  UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel2
Proof
INTRO_TAC THEN
ETAC UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
INTRO_TAC THEN
ALL_LRTAC THEN
RW_HYP_LEMMA_TAC listTheory.MEM_APPEND THEN
RW_HYP_LEMMA_TAC listTheory.MEM THEN
RW_HYP_LEMMA_TAC listTheory.MEM THEN
REMOVE_F_DISJUNCTS_TAC THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AITAC THEN STAC
 ,
 RW_HYP_LEMMA_TAC stateTheory.interconnect_request_type_11 THEN LRTAC THEN ITAC lists_lemmasTheory.EVERY_SUBLIST_LEMMA THEN STAC
]
QED

Theorem EQUAL_PENDING_ACCESSES_PRESERVES_UPDATING_BD_WRITE_REQUESTS_ONLY_LEMMA:
!channel1 channel2.
  channel2.pending_accesses = channel1.pending_accesses /\
  UPDATING_BD_WRITE_REQUESTS_ONLY channel1
  ==>
  UPDATING_BD_WRITE_REQUESTS_ONLY channel2
Proof
INTRO_TAC THEN
ETAC UPDATING_BD_WRITE_REQUESTS_ONLY THEN
STAC
QED

Theorem EQUAL_PENDING_ACCESSES_PRESERVES_WRITING_BACK_BD_WRITE_REQUESTS_ONLY_LEMMA:
!channel1 channel2.
  channel2.pending_accesses.requests = channel1.pending_accesses.requests /\
  WRITING_BACK_BD_WRITE_REQUESTS_ONLY channel1
  ==>
  WRITING_BACK_BD_WRITE_REQUESTS_ONLY channel2
Proof
INTRO_TAC THEN
ETAC WRITING_BACK_BD_WRITE_REQUESTS_ONLY THEN
STAC
QED

Theorem REGISTER_REQUESTING_WRITE_ADDRESSES_IMPLIES_WRITABLE_REQUEST_LEMMA:
!device_characteristics memory device address_bytes tag.
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device /\
  MEM (request_write address_bytes tag) device.dma_state.pending_register_related_memory_requests
  ==>
  EVERY (device_characteristics.dma_characteristics.W memory) (MAP FST address_bytes)
Proof
INTRO_TAC THEN
PTAC REGISTER_REQUESTING_WRITE_ADDRESSES THEN
AITAC THEN
STAC
QED

Theorem EQ_PENDING_REGIESTER_RELATED_MEMORY_REQUESTS_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA:
!device_characteristics memory device1 device2.
  device2.dma_state.pending_register_related_memory_requests = device1.dma_state.pending_register_related_memory_requests /\
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device1
  ==>
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC REGISTER_REQUESTING_WRITE_ADDRESSES THEN
STAC
QED

Theorem PENDING_ACCESSES_UNMODIFIED_REGISTER_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA:
!device_characteristics memory device1 device2.
  PENDING_ACCESSES_UNMODIFIED_REGISTER device1 device2 /\
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device1
  ==>
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC REGISTER_REQUESTING_WRITE_ADDRESSES THEN
PTAC PENDING_ACCESSES_UNMODIFIED_REGISTER THEN
STAC
QED

Theorem PENDING_ACCESSES_UNEXPANDED_REGISTER_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA:
!device_characteristics memory device1 device2.
  PENDING_ACCESSES_UNEXPANDED_REGISTER device1 device2 /\
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device1
  ==>
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC REGISTER_REQUESTING_WRITE_ADDRESSES THEN
INTRO_TAC THEN
PTAC PENDING_ACCESSES_UNEXPANDED_REGISTER THEN
AITAC THEN
AITAC THEN
STAC
QED

Theorem PENDING_ACCESSES_CONDITIONALLY_EXPANDED_REGISTER_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA:
!R W memory device_characteristics device1 device2.
  R = device_characteristics.dma_characteristics.R /\
  W = device_characteristics.dma_characteristics.W /\
  PENDING_ACCESSES_CONDITIONALLY_EXPANDED_REGISTER R W memory device1 device2 /\
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device1
  ==>
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC REGISTER_REQUESTING_WRITE_ADDRESSES THEN
INTRO_TAC THEN
PTAC PENDING_ACCESSES_CONDITIONALLY_EXPANDED_REGISTER THEN
AITAC THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AITAC THEN
 STAC
 ,
 PTAC REQUEST_CONDITION_R_W THEN
 PTAC REQUEST_CONDITION_W THEN
 STAC
]
QED

Theorem PENDING_ACCESSES_RESTRICTED_REGISTER_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA:
!R W memory device_characteristics device1 device2.
  R = device_characteristics.dma_characteristics.R /\
  W = device_characteristics.dma_characteristics.W /\
  PENDING_ACCESSES_RESTRICTED_REGISTER R W memory device1 device2 /\
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device1
  ==>
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC PENDING_ACCESSES_RESTRICTED_REGISTER THEN
SPLIT_ASM_DISJS_TAC THENL
[
 ITAC PENDING_ACCESSES_UNMODIFIED_REGISTER_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA THEN STAC
 ,
 ITAC PENDING_ACCESSES_UNEXPANDED_REGISTER_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA THEN STAC
 ,
 ITAC PENDING_ACCESSES_CONDITIONALLY_EXPANDED_REGISTER_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA THEN STAC
]
QED

Theorem PENDING_REGISTER_RELATED_MEMORY_REQUESTS_UNEXPANDED_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA:
!device_characteristics device1 device2 memory.
  LIST1_IN_LIST2 device2.dma_state.pending_register_related_memory_requests device1.dma_state.pending_register_related_memory_requests /\
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device1
  ==>
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC REGISTER_REQUESTING_WRITE_ADDRESSES THEN
INTRO_TAC THEN
PTAC listsTheory.LIST1_IN_LIST2 THEN
RW_HYP_LEMMA_TAC listTheory.EVERY_MEM THEN
AITAC THEN
APP_SCALAR_TAC THEN
AITAC THEN
STAC
QED
























Theorem WRITE_REQUEST_W_LEMMA:
!W memory is_valid new_requests requests write_requests address_bytes tag.
  REQUEST_VALIDATION_WRITABLE W memory is_valid /\
  requests = FILTER is_valid new_requests /\
  write_requests = FILTER WRITE_REQUEST requests /\
  MEM (request_write address_bytes tag) write_requests
  ==>
  EVERY (W memory) (MAP FST address_bytes)
Proof
INTRO_TAC THEN
LRTAC THEN
LRTAC THEN
ETAC listTheory.MEM_FILTER THEN
ETAC REQUEST_VALIDATION_WRITABLE THEN
AIRTAC THEN
STAC
QED

(*
Theorem APPENDING_VALID_REQUESTS_IMPLIES_OLD_OR_WRITABLE_REQUEST_LEMMA:
!extended_requests old_requests new_requests W memory is_valid address_bytes tag.
  extended_requests = old_requests ++ FILTER is_valid new_requests /\
  REQEUST_VALIDATION_WRITABLE W memory is_valid /\
  MEM (request_write address_bytes tag) extended_requests
  ==>
  MEM (request_write address_bytes tag) old_requests \/
  EVERY (W memory) (MAP FST address_bytes)
Proof
INTRO_TAC THEN
LRTAC THEN
ETAC listTheory.MEM_APPEND THEN
SPLIT_ASM_DISJS_TAC THENL
[
 STAC
 ,
 PTAC REQUEST_VALIDATION_WRITABLE THEN
 ETAC listTheory.MEM_FILTER THEN
 AITAC THEN
 STAC
]
QED
*)

Theorem EQ_READABLE_PRESERVES_DEVICE_REQUESTING_WRITE_ADDRESSES_LEMMA:
!W memory1 memory2 device_characteristics device.
  W = device_characteristics.dma_characteristics.W /\
  W memory2 = W memory1 /\
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory1 device
  ==>
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC DEVICE_REQUESTING_WRITE_ADDRESSES THEN
CONJ_TAC THENL
[
 ETAC DMA_REQUESTING_WRITE_ADDRESSES THEN
 INTRO_TAC THEN
 AITAC THEN
 ETAC CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
 INTRO_TAC THEN
 AITAC THEN
 STAC
 ,
 ETAC REGISTER_REQUESTING_WRITE_ADDRESSES THEN
 INTRO_TAC THEN
 AITAC THEN
 STAC
]
QED

Theorem UNWRITTEN_MEMORY_LOCATIONS_PRESERVED_LEMMA:
!memory1 memory2 write_address byte.
  memory2 = (write_address =+ byte) memory1
  ==>
  (!address. address <> write_address ==> memory1 address = memory2 address)
Proof
INTRO_TAC THEN
INTRO_TAC THEN
LRTAC THEN
REWRITE_TAC [combinTheory.UPDATE_def] THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 LRTAC THEN
 CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
 ,
 REWRITE_TAC []
]
QED

Theorem UPDATE_MEMORY_UNFOLD_LEMMA:
!memory1 memory2 address byte address_bytes.
  memory2 = update_memory memory1 ((address, byte)::address_bytes)
  ==>
  memory2 = update_memory ((address =+ byte) memory1) address_bytes
Proof
INTRO_TAC THEN
ETAC update_memory THEN
STAC
QED

Theorem MEMORY_WRITE_PRESERVES_OTHER_LOCATIONS_LEMMA:
!memory1 memory2 write_address byte.
  memory2 = (write_address =+ byte) memory1
  ==>
  !address. address <> write_address ==> memory1 address = memory2 address
Proof
INTRO_TAC THEN
INTRO_TAC THEN
LRTAC THEN
REWRITE_TAC [combinTheory.UPDATE_def] THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 LRTAC THEN
 CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
 ,
 REWRITE_TAC []
]
QED

Theorem WRITABLE_UNWRITABLE_ADDRESSES_DISTINCT_LEMMA:
!W memory write_address address.
  W memory write_address /\
  ~W memory address
  ==>
  address <> write_address
Proof
INTRO_TAC THEN
CCONTR_TAC THEN
ETAC boolTheory.NOT_CLAUSES THEN
LRTAC THEN
CONTR_ASMS_TAC
QED

Theorem WRITING_WRITABLE_MEMORY_PRESERVES_OTHER_LOCATIONS_LEMMA:
!W memory1 memory2 write_address byte.
  W memory1 write_address /\
  memory2 = (write_address =+ byte) memory1
  ==>
  !address. ~W memory1 address ==> memory1 address = memory2 address
Proof
INTRO_TAC THEN
INTRO_TAC THEN
ITAC MEMORY_WRITE_PRESERVES_OTHER_LOCATIONS_LEMMA THEN
INST_IMP_ASM_GOAL_TAC THEN
ITAC WRITABLE_UNWRITABLE_ADDRESSES_DISTINCT_LEMMA THEN
STAC
QED

Theorem WRITING_FIRST_WRITABLE_LOCATION_IMPLIES_REMAINING_WRITABLE_LOCATIONS_LEMMA:
!W memory1 memory2 device_characteristics address byte address_bytes.
  W = device_characteristics.dma_characteristics.W /\
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  EVERY (W memory1) (MAP FST ((address, byte)::address_bytes)) /\
  memory2 = (address =+ byte) memory1
  ==>
  EVERY (W memory2) (MAP FST address_bytes)
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATION_READABLE_WRITABLE THEN
ETAC listTheory.MAP THEN
ETAC listTheory.EVERY_DEF THEN
ETAC pairTheory.FST THEN
ITAC WRITING_WRITABLE_MEMORY_PRESERVES_OTHER_LOCATIONS_LEMMA THEN
FAITAC THEN
STAC
QED

Theorem PRESERVING_UNWRITABLE_MEMORY_PRESERVES_WRITABLE_MEMORY_LEMMA:
!W memory device_characteristics write_address byte.
  W = device_characteristics.dma_characteristics.W /\
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  (!address. ~W memory address ==> memory address = ((write_address =+ byte) memory) address)
  ==>
  W memory = W ((write_address =+ byte) memory)
Proof
INTRO_TAC THEN
ETAC PROOF_OBLIGATION_READABLE_WRITABLE THEN
FAITAC THEN
STAC
QED

Theorem WRITING_WRITABLE_MEMORY_LOCATION_PRESERVES_UNWRITABLE_LOCATIONS_LEMMA:
!W device_characteristics memory write_address address byte.
  W = device_characteristics.dma_characteristics.W /\
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  W memory write_address /\
  ~W memory address
  ==>
  ~W ((write_address =+ byte) memory) address
Proof
INTRO_TAC THEN
FITAC WRITING_WRITABLE_MEMORY_PRESERVES_OTHER_LOCATIONS_LEMMA THEN
(fn (A, t) => ASSUME_TAC (((SPEC “byte : word8”) o ASSUME o valOf o (List.find is_forall)) A) (filter (not o is_forall) A, t)) THEN
FIRTAC PRESERVING_UNWRITABLE_MEMORY_PRESERVES_WRITABLE_MEMORY_LEMMA THEN
WEAKEN_TAC (fn asm => (not o is_eq) asm andalso (not o is_neg) asm) THEN
(fn (A, t) =>
 ASSUME_TAC (
   ((fn thm => AP_THM thm (let val address = mk_var ("address", (hd o #2 o dest_type o type_of o lhs o concl) thm) in address end)) o
    ASSUME o valOf o (List.find is_eq)) A)
   (A, t)) THEN
STAC
QED

Theorem WRITING_WRITABLE_MEMORY_PRESERVES_UNWRITABLE_MEMORY_LEMMA:
!address_bytes W device_characteristics memory1 memory2.
  W = device_characteristics.dma_characteristics.W /\
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  EVERY (W memory1) (MAP FST address_bytes) /\
  memory2 = update_memory memory1 address_bytes
  ==>
  (!address. ~W memory1 address ==> memory1 address = memory2 address)
Proof
Induct THENL
[
 REWRITE_TAC [update_memory] THEN
 INTRO_TAC THEN
 INTRO_TAC THEN
 STAC
 ,
 INTRO_TAC THEN
 INTRO_TAC THEN
 IRTAC UPDATE_MEMORY_UNFOLD_LEMMA THEN
 FITAC WRITING_FIRST_WRITABLE_LOCATION_IMPLIES_REMAINING_WRITABLE_LOCATIONS_LEMMA THEN
 AITAC THEN
 ETAC listTheory.MAP THEN
 ETAC listTheory.EVERY_DEF THEN
 ETAC pairTheory.FST THEN
 ITAC WRITING_WRITABLE_MEMORY_LOCATION_PRESERVES_UNWRITABLE_LOCATIONS_LEMMA THEN
 AITAC THEN
 RLTAC THEN
 FITAC WRITABLE_UNWRITABLE_ADDRESSES_DISTINCT_LEMMA THEN
 REWRITE_TAC [combinTheory.UPDATE_def] THEN
 APP_SCALAR_TAC THEN
 IF_SPLIT_TAC THENL
 [
  LRTAC THEN
  CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
  ,
  REWRITE_TAC []
 ]
]
QED

Theorem WRITING_WRITABLE_MEMORY_PRESERVES_WRITABLE_READABLE_LEMMA:
!address_bytes device_characteristics R W memory1 memory2.
  R = device_characteristics.dma_characteristics.R /\
  W = device_characteristics.dma_characteristics.W /\
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  EVERY (W memory1) (MAP FST address_bytes) /\
  memory2 = update_memory memory1 address_bytes
  ==>
  R memory2 = R memory1 /\
  W memory2 = W memory1
Proof
INTRO_TAC THEN
ITAC WRITING_WRITABLE_MEMORY_PRESERVES_UNWRITABLE_MEMORY_LEMMA THEN
PTAC PROOF_OBLIGATION_READABLE_WRITABLE THEN
AIRTAC THEN
STAC
QED

Theorem PENDING_ACCESSES_RESTRICTED_PRESERVES_CHANNEL_W_LEMMA:
!R W memory channel1 channel2.
  PENDING_ACCESSES_RESTRICTED R W memory channel1 channel2 /\
  CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel1
  ==>
  CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel2
Proof
INTRO_TAC THEN
ETAC CHANNEL_REQUESTING_WRITE_ADDRESSES_EQ_OPERATIONS_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA THEN
ETAC access_propertiesTheory.PENDING_ACCESSES_RESTRICTED THEN
ITAC access_properties_fetching_bd_lemmasTheory.PENDING_ACCESSES_RESTRICTED_FETCHING_BD_PRESERVES_CHANNEL_W_LEMMA THEN
ITAC access_properties_updating_bd_lemmasTheory.PENDING_ACCESSES_RESTRICTED_UPDATING_BD_PRESERVES_CHANNEL_W_LEMMA THEN
ITAC access_properties_transferring_data_lemmasTheory.PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA_PRESERVES_CHANNEL_W_LEMMA THEN
ITAC access_properties_writing_back_bd_lemmasTheory.PENDING_ACCESSES_RESTRICTED_WRITING_BACK_BD_PRESERVES_CHANNEL_W_LEMMA THEN
STAC
QED

Theorem ALL_DMA_CHANNELS_EQ_PENDING_ACCESSES_IMPLIES_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA:
!W memory (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
          (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type) channel_id.
  (!channel_id. (schannel device2 channel_id).pending_accesses = (schannel device1 channel_id).pending_accesses) /\
  CHANNEL_REQUESTING_WRITE_ADDRESSES W memory (schannel device1 channel_id)
  ==>
  CHANNEL_REQUESTING_WRITE_ADDRESSES W memory (schannel device2 channel_id)
Proof
INTRO_TAC THEN
IRTAC access_properties_lemmasTheory.ALL_DMA_CHANNELS_EQ_PENDING_ACCESSES_IMPLIES_PENDING_ACCESSES_RESTRICTED_LEMMA THEN
IRTAC PENDING_ACCESSES_RESTRICTED_PRESERVES_CHANNEL_W_LEMMA THEN
STAC
QED

Theorem ALL_DMA_CHANNELS_EQ_PENDING_ACCESSES_PRESERVES_DEVICE_REQUESTING_WRITE_ADDRESSES_LEMMA:
!device_characteristics memory (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
                               (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  (!channel_id.
     (schannel device2 channel_id).pending_accesses = (schannel device1 channel_id).pending_accesses) /\
     device2.dma_state.pending_register_related_memory_requests = device1.dma_state.pending_register_related_memory_requests /\
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device1
  ==>
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC DEVICE_REQUESTING_WRITE_ADDRESSES THEN
CONJ_TAC THENL
[
 ETAC DMA_REQUESTING_WRITE_ADDRESSES THEN
 INTRO_TAC THEN
 LRTAC THEN
 AIRTAC THEN
 IRTAC ALL_DMA_CHANNELS_EQ_PENDING_ACCESSES_IMPLIES_CHANNEL_REQUESTING_WRITE_ADDRESSES_LEMMA THEN
 STAC
 ,
 IRTAC EQ_PENDING_REGIESTER_RELATED_MEMORY_REQUESTS_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA THEN
 STAC
]
QED

Theorem UPDATING_INTERNAL_STATE_PRESERVES_DEVICE_REQUESTING_WRITE_ADDRESSES_LEMMA:
!device1 device2 internal_state2 memory device_characteristics.
  device2 = device1 with dma_state := device1.dma_state with internal_state := internal_state2 /\
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device1
  ==>
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
IRTAC state_lemmasTheory.UPDATING_INTERNAL_STATE_PRESERVES_CHANNEL_STATES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA THEN
ETAC write_propertiesTheory.DEVICE_REQUESTING_WRITE_ADDRESSES THEN
CONJ_TAC THENL
[
 ETAC write_propertiesTheory.DMA_REQUESTING_WRITE_ADDRESSES THEN
 RW_HYPS_TAC stateTheory.schannel THEN
 REWRITE_TAC [stateTheory.schannel] THEN
 RLTAC THEN
 STAC
 ,
 ETAC write_propertiesTheory.REGISTER_REQUESTING_WRITE_ADDRESSES THEN RLTAC THEN STAC
]
QED

Theorem PATTERN_FST_SND_FST_EQ_LEMMA:
(\((_, ras, _), _, _). ras) = FST o SND o FST
Proof
MATCH_MP_TAC boolTheory.EQ_EXT THEN
GEN_TAC THEN
Cases_on ‘x’ THEN
ETAC combinTheory.o_DEF THEN
PairRules.PBETA_TAC THEN
Cases_on ‘q’ THEN
STAC
QED

Theorem UPDATING_UNREAD_MEMORY_IMPLIES_SAME_MEMORY_LEMMA:
!address_bytes memory1 memory2 address addresses.
  memory2 = update_memory memory1 address_bytes /\
  MEM address addresses /\
  EVERY (\e. ~MEM e addresses) (MAP FST address_bytes)
  ==>
  memory1 address = memory2 address
Proof
Induct THENL
[
 INTRO_TAC THEN
 ETAC operationsTheory.update_memory THEN
 STAC
 ,
 INTRO_TAC THEN
 IRTAC UPDATE_MEMORY_UNFOLD_LEMMA THEN
 ETAC listTheory.MAP THEN
 ETAC pairTheory.FST THEN
 ETAC listTheory.EVERY_DEF THEN
 APP_SCALAR_TAC THEN
 AITAC THEN
 ITAC UNWRITTEN_MEMORY_LOCATIONS_PRESERVED_LEMMA THEN
 RLTAC THEN
 REWRITE_TAC [combinTheory.UPDATE_def] THEN
 APP_SCALAR_TAC THEN
 IF_SPLIT_TAC THENL
 [
  LRTAC THEN
  CONTR_ASMS_TAC
  ,
  AITAC THEN
  LRTAC THEN
  REWRITE_TAC [combinTheory.UPDATE_def]
 ]
]
QED

Theorem DISJOINT_ADDRESSES_IMPLIES_SAME_MEMORY_LEMMA:
!addresses address_bytes memory1 memory2.
  DISJOINT_LISTS addresses (MAP FST address_bytes) /\
  memory2 = update_memory memory1 address_bytes
  ==>
  MAP memory2 addresses = MAP memory1 addresses
Proof
INTRO_TAC THEN
REWRITE_TAC [listTheory.MAP_EQ_f] THEN
INTRO_TAC THEN
ETAC listsTheory.DISJOINT_LISTS THEN
IRTAC (ONCE_REWRITE_RULE [lists_lemmasTheory.EVERY_NOT_MEM_SYM_LEMMA] UPDATING_UNREAD_MEMORY_IMPLIES_SAME_MEMORY_LEMMA) THEN
STAC
QED

Theorem WRITE_REQUESTS_IMPLIES_EMPTY_DMA_ADDRESSES_OR_WRITE_REQUEST_LEMMA:
!new_requests write_requests dma_address_bytes.
  write_requests = FILTER WRITE_REQUEST new_requests /\
  dma_address_bytes = FLAT (MAP request_to_address_bytes write_requests)
  ==>
  dma_address_bytes = [] \/
  !address_byte.
    MEM address_byte dma_address_bytes
    ==>
    ?address_bytes tag.
      MEM (request_write address_bytes tag) new_requests /\ MEM address_byte address_bytes
Proof
INTRO_TAC THEN
Cases_on ‘write_requests = []’ THENL
[
 LRTAC THEN ETAC listTheory.MAP THEN ETAC listTheory.FLAT THEN STAC
 ,
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 INTRO_TAC THEN
 ALL_LRTAC THEN
 ETAC listTheory.MEM_FLAT THEN
 AXTAC THEN
 ETAC listTheory.MEM_MAP THEN
 AXTAC THEN
 LRTAC THEN
 ETAC listTheory.MEM_FILTER THEN
 PTAC stateTheory.WRITE_REQUEST THEN TRY SOLVE_F_ASM_TAC THEN
 LRTAC THEN
 ETAC operationsTheory.request_to_address_bytes THEN
 PAXTAC THEN
 STAC
]
QED

Theorem WRITE_REQUESTS_IMPLIES_WRITE_REQUEST_LEMMA:
!new_requests write_requests dma_address_bytes.
  write_requests = FILTER WRITE_REQUEST new_requests /\
  dma_address_bytes = FLAT (MAP request_to_address_bytes write_requests)
  ==>
  !address_byte.
    MEM address_byte dma_address_bytes
    ==>
    ?address_bytes tag.
      MEM (request_write address_bytes tag) new_requests /\ MEM address_byte address_bytes
Proof
INTRO_TAC THEN
INTRO_TAC THEN
ALL_LRTAC THEN
ETAC listTheory.MEM_FLAT THEN
AXTAC THEN
ETAC listTheory.MEM_MAP THEN
AXTAC THEN
LRTAC THEN
ETAC listTheory.MEM_FILTER THEN
PTAC stateTheory.WRITE_REQUEST THEN TRY SOLVE_F_ASM_TAC THEN
LRTAC THEN
ETAC operationsTheory.request_to_address_bytes THEN
PAXTAC THEN
STAC
QED

Theorem EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA:
!dma_address_bytes memory1 memory2.
  dma_address_bytes = [] /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  memory2 = memory1
Proof
INTRO_TAC THEN
LRTAC THEN
ETAC operationsTheory.update_memory THEN
STAC
QED

val _ = export_theory();
