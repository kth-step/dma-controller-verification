open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory operationsTheory;

val _ = new_theory "device_register_write_lemmas";

Theorem DMA_CHARACTERISTICS_REGISTER_WRITE_PRESERVES_ALL_DMA_CHANNEL_PENDING_ACCESSES_LEMMA:
!device1 device2 internal_state pending_requests.
  device2 = device1 with dma_state := device1.dma_state with
          <|internal_state := internal_state;
            pending_register_related_memory_requests := pending_requests|>
  ==>
  !channel_id.
    (schannel device2 channel_id).pending_accesses = (schannel device1 channel_id).pending_accesses
Proof
INTRO_TAC THEN
GEN_TAC THEN
LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVE_ALL_DMA_CHANNEL_PENDING_ACCESSES_LEMMA:
!device_characteristics memory device1 device2.
  device2 = dma_append_internal_abstract_bds device_characteristics memory device1
  ==>
  !channel_id.
    (schannel device2 channel_id).pending_accesses = (schannel device1 channel_id).pending_accesses
Proof
INTRO_TAC THEN
GEN_TAC THEN
PTAC dma_append_internal_abstract_bds THEN TRY STAC THEN
ETAC dma_append_external_abstract_bds THEN
ETAC stateTheory.schannel THEN
MATCH_MP_TAC append_bds_lemmasTheory.APPEND_BDS_CHANNELS_PRESERVES_PENDING_ACCESSES_LEMMA THEN
LRTAC THEN
RECORD_TAC THEN
EXISTS_EQ_TAC
QED

(*
Theorem CHANNEL_ID_START_ABSTRACT_PRESERVES_ALL_DMA_CHANNEL_PENDING_ACCESSES_LEMMA:
!dma_state1 dma_state2 dma_characteristics memory channel_assign_bds_to_fetch.
  dma_state2 = channel_id_start_abstract dma_characteristics memory dma_state1 channel_assign_bds_to_fetch
  ==>
  !channel_id.
    (THE (dma_state2.channels channel_id)).pending_accesses =
    (THE (dma_state1.channels channel_id)).pending_accesses
Proof
INTRO_TAC THEN
GEN_TAC THEN
PTAC channel_id_start_abstract THENL
[
 STAC
 ,
 STAC
 ,
 LRTAC THEN
 RECORD_TAC THEN
 ETAC combinTheory.UPDATE_def THEN
 APP_SCALAR_TAC THEN
 IF_SPLIT_TAC THENL
 [
  ALL_LRTAC THEN
  ETAC optionTheory.option_CLAUSES THEN
  RECORD_TAC THEN
  STAC
  ,
  STAC
 ]
]
QED

Theorem CHANNEL_ID_STOP_ABSTRACT_PRESERVES_ALL_DMA_CHANNEL_PENDING_ACCESSES_LEMMA:
!dma_state1 dma_state2 channel_stop.
  dma_state2 = channel_id_stop_abstract dma_state1 channel_stop
  ==>
  !channel_id.
    (THE (dma_state2.channels channel_id)).pending_accesses =
    (THE (dma_state1.channels channel_id)).pending_accesses
Proof
INTRO_TAC THEN
GEN_TAC THEN
PTAC channel_id_stop_abstract THENL
[
 STAC
 ,
 LRTAC THEN
 ETAC combinTheory.UPDATE_def THEN
 RECORD_TAC THEN
 APP_SCALAR_TAC THEN
 IF_SPLIT_TAC THENL
 [
  ALL_LRTAC THEN
  ETAC optionTheory.option_CLAUSES THEN
  RECORD_TAC THEN
  STAC
  ,
  STAC
 ]
]
QED
*)

Theorem DMA_REGISTER_WRITE_PRESERVES_ALL_DMA_CHANNEL_PENDING_ACCESSES_LEMMA:
!device_characteristics is_valid memory device1 device2 dma_address_bytes addresses.
  (device2, dma_address_bytes) = dma_register_write device_characteristics is_valid memory device1 addresses
  ==>
  !channel_id.
    (schannel device2 channel_id).pending_accesses = (schannel device1 channel_id).pending_accesses
Proof
INTRO_TAC THEN
GEN_TAC THEN
PTAC dma_register_write THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 2 THEN
IRTAC DMA_CHARACTERISTICS_REGISTER_WRITE_PRESERVES_ALL_DMA_CHANNEL_PENDING_ACCESSES_LEMMA THEN
IRTAC DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVE_ALL_DMA_CHANNEL_PENDING_ACCESSES_LEMMA THEN
LRTAC THEN
RECORD_TAC THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem FUNCTION_REGISTER_WRITE_PRESERVES_ALL_DMA_CHANNEL_PENDING_ACCESSES_LEMMA:
!device_characteristics device1 device2 address_bytes.
  device2 = function_register_write device_characteristics device1 address_bytes
  ==>
  !channel_id.
    (schannel device2 channel_id).pending_accesses = (schannel device1 channel_id).pending_accesses
Proof
INTRO_TAC THEN
GEN_TAC THEN
PTAC function_register_write THEN
LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
STAC
QED




(*
Theorem CHANNEL_ID_START_ABSTRACT_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA:
!dma_characteristics memory_option dma_state1 dma_state2 channel_assign_bds_to_fetch.
  dma_state2 = channel_id_start_abstract dma_characteristics memory_option dma_state1 channel_assign_bds_to_fetch
  ==>
  dma_state2.pending_register_related_memory_requests = dma_state1.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
PTAC channel_id_start_abstract THENL
[
 STAC
 ,
 STAC
 ,
 LRTAC THEN RECORD_TAC THEN STAC
]
QED

Theorem CHANNEL_ID_STOP_ABSTRACT_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA:
!dma_state1 dma_state2 channel_stop.
  dma_state2 = channel_id_stop_abstract dma_state1 channel_stop
  ==>
  dma_state2.pending_register_related_memory_requests = dma_state1.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
PTAC channel_id_stop_abstract THENL
[
 STAC
 ,
 LRTAC THEN RECORD_TAC THEN STAC
]
QED
*)

Theorem FUNCTION_REGISTER_WRITE_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA:
!device_characteristics device1 device2 address_bytes.
  device2 = function_register_write device_characteristics device1 address_bytes
  ==>
  device2.dma_state.pending_register_related_memory_requests = device1.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
PTAC function_register_write THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

val _ = export_theory();

