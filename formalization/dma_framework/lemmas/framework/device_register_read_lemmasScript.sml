open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory operationsTheory;

val _ = new_theory "device_register_read_lemmas";

Theorem DMA_REGISTER_READ_PRESERVES_ALL_DMA_CHANNEL_PENDING_ACCESSES_LEMMA:
!device_characteristics is_valid device1 device2 addresses byte.
  (device2, byte) = dma_register_read device_characteristics is_valid device1 addresses
  ==>
  !channel_id.
    (schannel device2 channel_id).pending_accesses = (schannel device1 channel_id).pending_accesses
Proof
INTRO_TAC THEN
GEN_TAC THEN
PTAC dma_register_read THEN
EQ_PAIR_ASM_TAC THEN
LRTAC THEN
LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
STAC
QED

Theorem FUNCTION_REGISTER_READ_PRESERVES_ALL_DMA_CHANNEL_PENDING_ACCESSES_LEMMA:
!device_characteristics device1 device2 addresses byte.
  (device2, byte) = function_register_read device_characteristics device1 addresses
  ==>
  !channel_id.
    (schannel device2 channel_id).pending_accesses = (schannel device1 channel_id).pending_accesses
Proof
INTRO_TAC THEN
GEN_TAC THEN
PTAC function_register_read THEN
EQ_PAIR_ASM_TAC THEN
LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
STAC
QED

Theorem FUNCTION_REGISTER_READ_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA:
!device_characteristics device1 device2 addresses byte.
  (device2, byte) = function_register_read device_characteristics device1 addresses
  ==>
  device2.dma_state.pending_register_related_memory_requests = device1.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
PTAC function_register_read THEN
EQ_PAIR_ASM_TAC THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_REGISTER_READ_PRESERVES_CHANNELS_LEMMA:
!device_characteristics device1 device2 addresses bytes is_valid.
  (device2, bytes) = dma_register_read device_characteristics is_valid device1 addresses
  ==>
  device2.dma_state.channels = device1.dma_state.channels
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_register_read THEN
EQ_PAIR_ASM_TAC THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem FUNCTION_REGISTER_READ_PRESERVES_DMA_STATE_LEMMA:
!device_characteristics device1 device2 addresses bytes.
  (device2, bytes) = function_register_read device_characteristics device1 addresses
  ==>
  device2.dma_state = device1.dma_state
Proof
INTRO_TAC THEN
PTAC operationsTheory.function_register_read THEN
EQ_PAIR_ASM_TAC THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_REGISTER_READ_IMPLIES_REGISTER_READ_LEMMA:
!device_characteristics device1 device2 bytes addresses write_requests validity_filter.
  (device2, write_requests, bytes) = dma_register_read device_characteristics validity_filter device1 addresses
  ==>
  ?requests.
    (device2.dma_state.internal_state, bytes, requests) = device_characteristics.dma_characteristics.register_read device1.dma_state.internal_state addresses
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_register_read THEN
EQ_PAIR_ASM_TAC THEN
RLTAC THEN
RLTAC THEN
PAXTAC THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

val _ = export_theory();

