open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory invariant_l2Theory l1Theory l2Theory proof_obligationsTheory;

val _ = new_theory "device_register_write_l2_lemmas";

Theorem REGISTER_WRITE_IMPLIES_READ_REQUEST_R_LEMMA:
!device_characteristics memory device internal_state1 internal_state2 requests register_address_bytes addresses tag.
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_READ_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  SCRATCHPAD_R device_characteristics memory device.dma_state.internal_state /\
  internal_state1 = device.dma_state.internal_state /\
  (internal_state2, requests) = device_characteristics.dma_characteristics.register_write internal_state1 register_address_bytes /\
  MEM (request_read addresses tag) requests
  ==>
  EVERY (device_characteristics.dma_characteristics.R memory) addresses
Proof
INTRO_TAC THEN
PTAC SCRATCHPAD_R THEN
AITAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_READ_REQUESTS_ADDRESS_SCRATCHPAD THEN
AITAC THEN
ITAC lists_lemmasTheory.EVERY_SUBLIST_LEMMA THEN
STAC
QED

Theorem REGISTER_WRITE_IMPLIES_WRITE_REQUEST_W_LEMMA:
!device_characteristics memory device internal_state1 internal_state2 requests register_address_bytes address_bytes tag.
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  SCRATCHPAD_W device_characteristics memory device.dma_state.internal_state /\
  internal_state1 = device.dma_state.internal_state /\
  (internal_state2, requests) = device_characteristics.dma_characteristics.register_write internal_state1 register_address_bytes /\
  MEM (request_write address_bytes tag) requests
  ==>
  EVERY (device_characteristics.dma_characteristics.W memory) (MAP FST address_bytes)
Proof
INTRO_TAC THEN
PTAC SCRATCHPAD_W THEN
AITAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD THEN
AITAC THEN
ITAC lists_lemmasTheory.EVERY_SUBLIST_LEMMA THEN
STAC
QED

Theorem REGISTER_WRITE_IMPLIES_REQUEST_R_W_LEMMA:
!device_characteristics memory device internal_state1 internal_state2 request requests register_address_bytes.
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_READ_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  SCRATCHPAD_R_W device_characteristics memory device.dma_state.internal_state /\
  internal_state1 = device.dma_state.internal_state /\
  (internal_state2, requests) = device_characteristics.dma_characteristics.register_write internal_state1 register_address_bytes /\
  MEM request requests
  ==>
  is_valid_readable_writable device_characteristics memory device request
Proof
INTRO_TAC THEN
PTAC SCRATCHPAD_R_W THEN
PTAC access_propertiesTheory.is_valid_readable_writable THEN LRTAC THENL
[
 IRTAC REGISTER_WRITE_IMPLIES_READ_REQUEST_R_LEMMA THEN STAC
 ,
 IRTAC REGISTER_WRITE_IMPLIES_WRITE_REQUEST_W_LEMMA THEN STAC
]
QED

Theorem REGISER_WRITE_IMPLIES_IS_VALID_L1_EQ_IS_VALID_L2_LEMMA:
!device_characteristics memory device internal_state1 internal_state2 request requests register_address_bytes.
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_READ_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  SCRATCHPAD_R_W device_characteristics memory device.dma_state.internal_state /\
  internal_state1 = device.dma_state.internal_state /\
  (internal_state2, requests) = device_characteristics.dma_characteristics.register_write internal_state1 register_address_bytes /\
  MEM request requests
  ==>
  is_valid_l1 device_characteristics memory device request = is_valid_l2 request
Proof
INTRO_TAC THEN
PTAC is_valid_l1 THEN
PTAC is_valid_l2 THEN
IRTAC REGISTER_WRITE_IMPLIES_REQUEST_R_W_LEMMA THEN
STAC
QED

Theorem REGISTER_WRITE_IMPLIES_FILTER_IS_VALID_L1_EQ_FILTER_IS_VALID_L2_LEMMA:
!device_characteristics memory device internal_state1 internal_state2 requests register_address_bytes.
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_READ_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  SCRATCHPAD_R_W device_characteristics memory device.dma_state.internal_state /\
  internal_state1 = device.dma_state.internal_state /\
  (internal_state2, requests) = device_characteristics.dma_characteristics.register_write internal_state1 register_address_bytes
  ==>
  FILTER (is_valid_l1 device_characteristics memory device) requests =
  FILTER is_valid_l2 requests
Proof
INTRO_TAC THEN
REWRITE_TAC [rich_listTheory.FILTER_EQ] THEN
INTRO_TAC THEN
IRTAC REGISER_WRITE_IMPLIES_IS_VALID_L1_EQ_IS_VALID_L2_LEMMA THEN
STAC
QED

(*
Theorem FILTER_IS_VALID12_EQ_READ_REQUESTS_IMPLIES_FILTER_IS_VALID12_READ_REQUESTS_EQ_LEMMA:
!is_valid1 is_valid2 new_requests read_requests.
  FILTER is_valid1 new_requests = FILTER is_valid2 new_requests /\
  read_requests = FILTER READ_REQUEST new_requests
  ==>
  FILTER is_valid1 read_requests = FILTER is_valid2 read_requests
Proof
INTRO_TAC THEN
LRTAC THEN
ONCE_REWRITE_TAC [rich_listTheory.FILTER_COMM] THEN
LRTAC THEN
STAC
QED
*)

Theorem DMA_REGISTER_WRITE_L1_EQ_L2_LEMMA:
!is_valid1 is_valid2 device_characteristics memory memory_option device register_address_bytes.
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_READ_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  SCRATCHPAD_R_W device_characteristics memory device.dma_state.internal_state /\
  is_valid1 = is_valid_l1 device_characteristics memory device /\
  is_valid2 = is_valid_l2
  ==>
  dma_register_write device_characteristics is_valid2 memory_option device register_address_bytes =
  dma_register_write device_characteristics is_valid1 memory_option device register_address_bytes
Proof
INTRO_TAC THEN
ETAC operationsTheory.dma_register_write THEN
ONCE_LETS_TAC THEN
ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
ONCE_LETS_TAC THEN
LRTAC THEN
ONCE_LETS_TAC THEN RLTAC THEN
ONCE_LETS_TAC THEN RLTAC THEN
ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
ONCE_LETS_TAC THEN
ONCE_LETS_TAC THEN
ONCE_LETS_TAC THEN
ITAC REGISTER_WRITE_IMPLIES_FILTER_IS_VALID_L1_EQ_FILTER_IS_VALID_L2_LEMMA THEN
LRTAC THEN
LRTAC THEN
LRTAC THEN
RLTAC THEN
ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
ONCE_LETS_TAC THEN
STAC
QED

Theorem DEVICE_REGISTER_WRITE_IS_VALID_L1_EQ_L2_LEMMA:
!is_valid1 is_valid2 device_characteristics memory memory_option device register_address_bytes.
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_READ_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  SCRATCHPAD_R_W device_characteristics memory device.dma_state.internal_state /\
  is_valid1 = is_valid_l1 device_characteristics memory device /\
  is_valid2 = is_valid_l2
  ==>
  device_register_write device_characteristics is_valid2 memory_option device register_address_bytes =
  device_register_write device_characteristics is_valid1 memory_option device register_address_bytes
Proof
INTRO_TAC THEN
REPEAT GEN_TAC THEN
ETAC operationsTheory.device_register_write THEN
IF_SPLIT_TAC THENL
[
 ITAC DMA_REGISTER_WRITE_L1_EQ_L2_LEMMA THEN STAC
 ,
 IF_SPLIT_TAC THENL
 [
  IF_SPLIT_TAC THEN STAC
  ,
  STAC
 ]
]
QED

Theorem DEVICE_REGISTER_WRITE_L1_EQ_L2_LEMMA:
!device_characteristics memory device register_address_bytes.
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_READ_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_REGISTER_WRITE_MEMORY_WRITE_REQUESTS_ADDRESS_SCRATCHPAD device_characteristics /\
  SCRATCHPAD_R_W device_characteristics memory device.dma_state.internal_state
  ==>
  device_register_write_l2 device_characteristics memory device register_address_bytes =
  device_register_write_l1 device_characteristics memory device register_address_bytes
Proof
INTRO_TAC THEN
PTAC device_register_write_l2 THEN
PTAC device_register_write_l1 THEN
ITAC DEVICE_REGISTER_WRITE_IS_VALID_L1_EQ_L2_LEMMA THEN
STAC
QED

val _ = export_theory();

