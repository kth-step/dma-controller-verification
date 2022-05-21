open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory operationsTheory read_propertiesTheory write_propertiesTheory;

val _ = new_theory "dma_pending_requests_properties_lemmas";

Theorem CHANNEL_REQESTING_READ_ADDRESSES_IMPLIES_FETCHING_BD_REQEUSTS_READ_ADDRESSES_LEMMA:
!R memory channel addresses tag.
  CHANNEL_REQUESTING_READ_ADDRESSES R memory channel /\
  MEM (request_read addresses tag) (collect_pending_fetch_bd_request channel.pending_accesses.requests.fetching_bd)
  ==>
  EVERY (R memory) addresses
Proof
INTRO_TAC THEN
RW_HYP_LEMMA_TAC read_properties_lemmasTheory.CHANNEL_REQUESTING_READ_ADDRESSES_EQ_OPERATIONS_CHANNEL_REQUESTING_READ_ADDRESSES_LEMMA THEN
ITAC read_properties_lemmasTheory.FETCHING_BD_CHANNEL_REQUESTING_READ_ADDRESSES_IMPLY_CHANNEL_REQUESTING_READ_ADDRESSES_LEMMA THEN
STAC
QED

Theorem CHANNEL_REQUESTING_READ_ADDRESSES_IMPLY_READABLE_READ_REQUESTS_ONLY_LEMMA:
!R memory channel channel_pending_accesses addresses tag.
  CHANNEL_REQUESTING_READ_ADDRESSES R memory channel /\
  channel_pending_accesses = channel_pending_requests channel.pending_accesses.requests /\
  MEM (request_read addresses tag) channel_pending_accesses
  ==>
  EVERY (R memory) addresses
Proof
INTRO_TAC THEN
PTAC channel_pending_requests THEN
LRTAC THEN
ETAC listTheory.MEM_APPEND THEN
SPLIT_ASM_DISJS_TAC THENL
[
 ITAC CHANNEL_REQESTING_READ_ADDRESSES_IMPLIES_FETCHING_BD_REQEUSTS_READ_ADDRESSES_LEMMA THEN STAC
 ,
 ITAC read_properties_lemmasTheory.CHANNEL_REQESTING_READ_ADDRESSES_IMPLIES_UPDATING_BD_REQEUSTS_READ_ADDRESSES_LEMMA THEN STAC
 ,
 ITAC read_properties_lemmasTheory.CHANNEL_REQESTING_READ_ADDRESSES_IMPLIES_TRANSFERRING_DATA_REQEUSTS_READ_ADDRESSES_LEMMA THEN STAC
 ,
 ITAC read_properties_lemmasTheory.CHANNEL_REQESTING_READ_ADDRESSES_IMPLIES_WRITING_BACK_BD_REQEUSTS_READ_ADDRESSES_LEMMA THEN STAC
]
QED

Theorem VALID_CHANNEL_ID_DMA_REQUESTING_READ_ADDRESSES_IMPLY_READ_REQUESTS_READABLE_LEMMA:
!device_characteristics device memory channel_id channel channel_pending_accesses addresses tag.
  DMA_REQUESTING_READ_ADDRESSES device_characteristics memory device /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channel = schannel device channel_id /\
  channel_pending_accesses = channel_pending_requests channel.pending_accesses.requests /\
  MEM (request_read addresses tag) channel_pending_accesses
  ==>
  EVERY (device_characteristics.dma_characteristics.R memory) addresses
Proof
INTRO_TAC THEN
ETAC DMA_REQUESTING_READ_ADDRESSES THEN
AITAC THEN
ITAC CHANNEL_REQUESTING_READ_ADDRESSES_IMPLY_READABLE_READ_REQUESTS_ONLY_LEMMA THEN
STAC
QED



Theorem DEVICE_REQUESTING_READ_ADDRESSES_IMPLIES_READABLE_REQUEST_LEMMA:
!device_characteristics device addresses tag memory.
  MEM (request_read addresses tag) (dma_pending_requests device_characteristics device) /\
  DEVICE_REQUESTING_READ_ADDRESSES device_characteristics memory device
  ==>
  EVERY (device_characteristics.dma_characteristics.R memory) addresses
Proof
INTRO_TAC THEN
ETAC DEVICE_REQUESTING_READ_ADDRESSES THEN
ETAC DMA_REQUESTING_READ_ADDRESSES THEN
PTAC dma_pending_requests THEN
ETAC listTheory.MEM_APPEND THEN
SPLIT_ASM_DISJS_TAC THENL
[
 IRTAC dma_pending_requests_lemmasTheory.MEM_DMA_PENDING_REQUESTS_CHANNELS_IMP_SOME_VALID_CHANNEL_LEMMA THEN
 AXTAC THEN
 FAITAC THEN
 ETAC stateTheory.schannel THEN
 ETAC CHANNEL_REQUESTING_READ_ADDRESSES THEN
 PTAC channel_pending_requests THEN
 PTAC collect_pending_requests THEN
 EQ_PAIR_ASM_TAC THEN
 ALL_LRTAC THEN
 AIRTAC THEN
 STAC
 ,
 ITAC read_properties_lemmasTheory.REGISTER_REQUESTING_READ_ADDRESSES_IMPLIES_READABLE_REQUEST_LEMMA THEN STAC
]
QED

Theorem DEVICE_REQUESTING_WRITE_ADDRESSES_IMPLIES_WRITABLE_REQUEST_LEMMA:
!device_characteristics device address_bytes tag memory.
  MEM (request_write address_bytes tag) (dma_pending_requests device_characteristics device) /\
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device
  ==>
  EVERY (device_characteristics.dma_characteristics.W memory) (MAP FST address_bytes)
Proof
INTRO_TAC THEN
ETAC DEVICE_REQUESTING_WRITE_ADDRESSES THEN
ETAC DMA_REQUESTING_WRITE_ADDRESSES THEN
PTAC dma_pending_requests THEN
ETAC listTheory.MEM_APPEND THEN
SPLIT_ASM_DISJS_TAC THENL
[
 IRTAC dma_pending_requests_lemmasTheory.MEM_DMA_PENDING_REQUESTS_CHANNELS_IMP_SOME_VALID_CHANNEL_LEMMA THEN
 AXTAC THEN
 FAITAC THEN
 ETAC stateTheory.schannel THEN
 ETAC CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
 PTAC channel_pending_requests THEN
 PTAC collect_pending_requests THEN
 EQ_PAIR_ASM_TAC THEN
 ALL_LRTAC THEN
 AIRTAC THEN
 STAC
 ,
 ITAC write_properties_lemmasTheory.REGISTER_REQUESTING_WRITE_ADDRESSES_IMPLIES_WRITABLE_REQUEST_LEMMA THEN STAC
]
QED



Theorem WRITABLE_MEMORY_REQUEST_PRESERVES_NOT_WRITABLE_MEMORY_LEMMA:
!device_characteristics address_bytes tag device memory1 memory2.
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  MEM (request_write address_bytes tag) (dma_pending_requests device_characteristics device) /\
  memory2 = update_memory memory1 address_bytes /\
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory1 device
  ==>
  (!address. ~device_characteristics.dma_characteristics.W memory1 address ==> memory1 address = memory2 address)
Proof
INTRO_TAC THEN
ITAC DEVICE_REQUESTING_WRITE_ADDRESSES_IMPLIES_WRITABLE_REQUEST_LEMMA THEN
ITAC write_properties_lemmasTheory.WRITING_WRITABLE_MEMORY_PRESERVES_UNWRITABLE_MEMORY_LEMMA THEN
STAC
QED

Theorem PROOF_OBLIGATION_READABLE_WRITABLE_DEVICE_REQUESTING_WRITE_ADDRESSES_IMPLIES_MEMORY_WRITES_PRESERVE_R_W_LEMMA:
!R W device_characteristics address_bytes tag device memory1 memory2.
  R = device_characteristics.dma_characteristics.R /\
  W = device_characteristics.dma_characteristics.W /\
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  MEM (request_write address_bytes tag) (dma_pending_requests device_characteristics device) /\
  memory2 = update_memory memory1 address_bytes /\
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory1 device
  ==>
  R memory2 = R memory1 /\
  W memory2 = W memory1
Proof
INTRO_TAC THEN
ITAC WRITABLE_MEMORY_REQUEST_PRESERVES_NOT_WRITABLE_MEMORY_LEMMA THEN
ETAC proof_obligationsTheory.PROOF_OBLIGATION_READABLE_WRITABLE THEN
FAITAC THEN
STAC
QED

val _ = export_theory();

