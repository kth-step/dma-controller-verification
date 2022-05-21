open HolKernel Parse boolLib bossLib helper_tactics;
open operationsTheory read_propertiesTheory write_propertiesTheory access_propertiesTheory;

val _ = new_theory "dma_register_read_properties_lemmas";

Theorem DMA_REGISTER_READ_IMPLIES_PENDING_ACCESSES_RESTRICTED_LEMMA:
!R W memory device_characteristics is_valid device1 device2 addresses byte.
  (device2, byte) = dma_register_read device_characteristics is_valid device1 addresses
  ==>
  !channel_id.
    PENDING_ACCESSES_RESTRICTED R W memory (schannel device1 channel_id) (schannel device2 channel_id)
Proof
INTRO_TAC THEN
GEN_TAC THEN
REWRITE_TAC [PENDING_ACCESSES_RESTRICTED] THEN
REWRITE_TAC [PENDING_ACCESSES_RESTRICTED_FETCHING_BD] THEN
REWRITE_TAC [PENDING_ACCESSES_RESTRICTED_UPDATING_BD] THEN
REWRITE_TAC [PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA] THEN
REWRITE_TAC [PENDING_ACCESSES_RESTRICTED_WRITING_BACK_BD] THEN
REWRITE_TAC [PENDING_ACCESSES_UNMODIFIED_FETCHING_BD] THEN
REWRITE_TAC [PENDING_ACCESSES_UNMODIFIED_UPDATING_BD] THEN
REWRITE_TAC [PENDING_ACCESSES_UNMODIFIED_TRANSFERRING_DATA] THEN
REWRITE_TAC [PENDING_ACCESSES_UNMODIFIED_WRITING_BACK_BD] THEN
ITAC device_register_read_lemmasTheory.DMA_REGISTER_READ_PRESERVES_ALL_DMA_CHANNEL_PENDING_ACCESSES_LEMMA THEN
STAC
QED

Theorem DMA_REGISTER_READ_REQUEST_VALIDATION_READABLE_IMPLIES_OLD_REQUEST_OR_READABLE_LEMMA:
!device_characteristics is_valid device1 device2 memory register_read_addresses addresses tag byte.
  (device2, byte) = dma_register_read device_characteristics is_valid device1 register_read_addresses /\
  REQUEST_VALIDATION_READABLE device_characteristics.dma_characteristics.R memory is_valid /\
  MEM (request_read addresses tag) device2.dma_state.pending_register_related_memory_requests
  ==>
  MEM (request_read addresses tag) device1.dma_state.pending_register_related_memory_requests \/
  EVERY (device_characteristics.dma_characteristics.R memory) addresses
Proof
INTRO_TAC THEN
PTAC dma_register_read THEN
EQ_PAIR_ASM_TAC THEN
LRTAC THEN
LRTAC THEN
RECORD_TAC THEN
RLTAC THEN
ETAC listTheory.MEM_APPEND THEN
SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
IRTAC read_properties_lemmasTheory.READ_REQUEST_R_LEMMA THEN
STAC
QED

Theorem MEM_WRITE_REQUEST_IMPLIES_PENDING_REQUESTS_LEMMA:
!requests read_requests address_bytes tag pending_requests.
  read_requests = FILTER READ_REQUEST requests /\
  MEM (request_write address_bytes tag) (pending_requests ++ read_requests)
  ==>
  MEM (request_write address_bytes tag) pending_requests
Proof
INTRO_TAC THEN
LRTAC THEN
ETAC listTheory.MEM_APPEND THEN
SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
ETAC listTheory.MEM_FILTER THEN
PTAC stateTheory.READ_REQUEST THEN
SOLVE_F_ASM_TAC
QED

Theorem DMA_REGISTER_READ_REQUEST_VALIDATION_READABLE_IMPLIES_OLD_REQUEST_OR_WRITABLE_LEMMA:
!device_characteristics is_valid device1 device2 memory register_read_addresses address_bytes tag byte.
  (device2, byte) = dma_register_read device_characteristics is_valid device1 register_read_addresses /\
  REQUEST_VALIDATION_WRITABLE device_characteristics.dma_characteristics.W memory is_valid /\
  MEM (request_write address_bytes tag) device2.dma_state.pending_register_related_memory_requests
  ==>
  MEM (request_write address_bytes tag) device1.dma_state.pending_register_related_memory_requests \/
  EVERY (device_characteristics.dma_characteristics.W memory) (MAP FST address_bytes)
Proof
INTRO_TAC THEN
PTAC dma_register_read THEN
EQ_PAIR_ASM_TAC THEN
RLTAC THEN
LRTAC THEN
RECORD_TAC THEN
IRTAC MEM_WRITE_REQUEST_IMPLIES_PENDING_REQUESTS_LEMMA THEN
STAC
QED

Theorem DMA_REGISTER_READ_PRESERVES_REGISTER_REQUESTING_READ_ADDRESSES_LEMMA:
!device_characteristics is_valid device1 device2 memory addresses byte.
  (device2, byte) = dma_register_read device_characteristics is_valid device1 addresses /\
  REQUEST_VALIDATION_READABLE device_characteristics.dma_characteristics.R memory is_valid /\
  REGISTER_REQUESTING_READ_ADDRESSES device_characteristics memory device1
  ==>
  REGISTER_REQUESTING_READ_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC read_propertiesTheory.REGISTER_REQUESTING_READ_ADDRESSES THEN
INTRO_TAC THEN
FIRTAC DMA_REGISTER_READ_REQUEST_VALIDATION_READABLE_IMPLIES_OLD_REQUEST_OR_READABLE_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AIRTAC THEN STAC
 ,
 STAC
]
QED

Theorem DMA_REGISTER_READ_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA:
!device_characteristics is_valid device1 device2 memory addresses byte.
  (device2, byte) = dma_register_read device_characteristics is_valid device1 addresses /\
  REQUEST_VALIDATION_WRITABLE device_characteristics.dma_characteristics.W memory is_valid /\
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device1
  ==>
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC write_propertiesTheory.REGISTER_REQUESTING_WRITE_ADDRESSES THEN
INTRO_TAC THEN
FIRTAC DMA_REGISTER_READ_REQUEST_VALIDATION_READABLE_IMPLIES_OLD_REQUEST_OR_WRITABLE_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AIRTAC THEN STAC
 ,
 STAC
]
QED

Theorem DMA_REGISTER_READ_PRESERVES_DEVICE_REQUESTING_READ_ADDRESSES_LEMMA:
!device_characteristics is_valid device1 device2 memory addresses byte.
  (device2, byte) = dma_register_read device_characteristics is_valid device1 addresses /\
  REQUEST_VALIDATION_READABLE device_characteristics.dma_characteristics.R memory is_valid /\
  DEVICE_REQUESTING_READ_ADDRESSES device_characteristics memory device1
  ==>
  DEVICE_REQUESTING_READ_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC read_propertiesTheory.DEVICE_REQUESTING_READ_ADDRESSES THEN
CONJ_TAC THENL
[
 ETAC read_propertiesTheory.DMA_REQUESTING_READ_ADDRESSES THEN
 INTRO_TAC THEN
 AIRTAC THEN
 IRTAC DMA_REGISTER_READ_IMPLIES_PENDING_ACCESSES_RESTRICTED_LEMMA THEN
 ITAC read_properties_lemmasTheory.PENDING_ACCESSES_RESTRICTED_PRESERVES_CHANNEL_R_LEMMA THEN
 STAC
 ,
 IRTAC DMA_REGISTER_READ_PRESERVES_REGISTER_REQUESTING_READ_ADDRESSES_LEMMA THEN
 STAC
]
QED

Theorem DMA_REGISTER_READ_PRESERVES_DEVICE_REQUESTING_WRITE_ADDRESSES_LEMMA:
!device_characteristics is_valid device1 device2 memory addresses byte.
  (device2, byte) = dma_register_read device_characteristics is_valid device1 addresses /\
  REQUEST_VALIDATION_WRITABLE device_characteristics.dma_characteristics.W memory is_valid /\
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device1
  ==>
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC write_propertiesTheory.DEVICE_REQUESTING_WRITE_ADDRESSES THEN
CONJ_TAC THENL
[
 ETAC write_propertiesTheory.DMA_REQUESTING_WRITE_ADDRESSES THEN
 INTRO_TAC THEN
 AIRTAC THEN
 IRTAC DMA_REGISTER_READ_IMPLIES_PENDING_ACCESSES_RESTRICTED_LEMMA THEN
 ITAC write_properties_lemmasTheory.PENDING_ACCESSES_RESTRICTED_PRESERVES_CHANNEL_W_LEMMA THEN
 STAC
 ,
 IRTAC DMA_REGISTER_READ_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA THEN
 STAC
]
QED

Theorem DMA_REGISTER_READ_PRESERVES_DEVICE_REQUESTING_READ_WRITE_ADDRESSES_LEMMA:
!device_characteristics is_valid device1 device2 memory addresses byte.
  REQUEST_VALIDATION_READABLE device_characteristics.dma_characteristics.R memory is_valid /\
  REQUEST_VALIDATION_WRITABLE device_characteristics.dma_characteristics.W memory is_valid /\
  (device2, byte) = dma_register_read device_characteristics is_valid device1 addresses /\
  DEVICE_REQUESTING_READ_ADDRESSES device_characteristics memory device1 /\
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device1
  ==>
  DEVICE_REQUESTING_READ_ADDRESSES device_characteristics memory device2 /\
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ITAC DMA_REGISTER_READ_PRESERVES_DEVICE_REQUESTING_READ_ADDRESSES_LEMMA THEN
ITAC DMA_REGISTER_READ_PRESERVES_DEVICE_REQUESTING_WRITE_ADDRESSES_LEMMA THEN
STAC
QED

val _ = export_theory();

