open HolKernel Parse boolLib bossLib helper_tactics;
open operationsTheory invariant_l1Theory access_propertiesTheory;

val _ = new_theory "device_register_read_l1";

Theorem DMA_REGISTER_READ_PRESERVES_INVARIANT_L1_LEMMA:
!device_characteristics is_valid device1 device2 memory addresses byte.
  REQUEST_VALIDATION_READABLE device_characteristics.dma_characteristics.R memory is_valid /\
  REQUEST_VALIDATION_WRITABLE device_characteristics.dma_characteristics.W memory is_valid /\
  (device2, byte) = dma_register_read device_characteristics is_valid device1 addresses /\
  INVARIANT_L1 device_characteristics memory device1
  ==>
  INVARIANT_L1 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_L1 THEN
ITAC dma_register_read_properties_lemmasTheory.DMA_REGISTER_READ_PRESERVES_DEVICE_REQUESTING_READ_WRITE_ADDRESSES_LEMMA THEN
STAC
QED

Theorem FUNCTION_REGISTER_READ_PRESERVES_INVARIANT_L1_LEMMA:
!device_characteristics device1 device2 memory addresses byte.
  (device2, byte) = function_register_read device_characteristics device1 addresses /\
  INVARIANT_L1 device_characteristics memory device1
  ==>
  INVARIANT_L1 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_L1 THEN
ITAC function_register_read_properties_lemmasTheory.FUNCTION_REGISTER_READ_PRESERVES_DEVICE_REQUESTING_READ_WRITE_ADDRESSES_LEMMA THEN
STAC
QED

Theorem DEVICE_REGISTER_READ_L1_PRESERVES_INVARIANT_L1_LEMMA:
!device_characteristics device1 device2 memory addresses address_bytes.
  (device2, address_bytes) = device_register_read_l1 device_characteristics memory device1 addresses /\
  INVARIANT_L1 device_characteristics memory device1
  ==>
  INVARIANT_L1 device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC l1Theory.device_register_read_l1 THEN
PTAC operationsTheory.device_register_read THENL
[
 MATCH_MP_TAC DMA_REGISTER_READ_PRESERVES_INVARIANT_L1_LEMMA THEN
 PAXTAC THEN
 ASM_REWRITE_TAC [l1_dma_lemmasTheory.IS_VALID_IMPLIES_REQUEST_VALIDATION_READABLE_LEMMA, l1_dma_lemmasTheory.IS_VALID_IMPLIES_REQUEST_VALIDATION_WRITABLE_LEMMA]
 ,
 ITAC FUNCTION_REGISTER_READ_PRESERVES_INVARIANT_L1_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

val _ = export_theory();

