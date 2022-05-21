open HolKernel Parse boolLib bossLib helper_tactics;
open invariant_l1Theory invariant_l2Theory;

val _ = new_theory "dma_write_invariant2_preservation_lemmas";

Theorem INVARIANT_L1_IMPLIES_PENDING_MEMORY_WRITE_REQUEST_W_LEMMA:
!device_characteristics memory device address_bytes tag.
  INVARIANT_L1 device_characteristics memory device /\
  MEM (request_write address_bytes tag) (dma_pending_requests_l2 device_characteristics device)
  ==>
  EVERY (device_characteristics.dma_characteristics.W memory) (MAP FST address_bytes)
Proof
INTRO_TAC THEN
PTAC INVARIANT_L1 THEN
PTAC write_propertiesTheory.DEVICE_REQUESTING_WRITE_ADDRESSES THEN
PTAC l2Theory.dma_pending_requests_l2 THEN
IRTAC dma_pending_requests_lemmasTheory.DMA_PENDING_REQUEST_FROM_VALID_CHANNEL_LEMMA THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AXTAC THEN
 PTAC write_propertiesTheory.DMA_REQUESTING_WRITE_ADDRESSES THEN
 AIRTAC THEN
 ETAC (GSYM stateTheory.schannel) THEN
 PTAC write_propertiesTheory.CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
 PTAC operationsTheory.channel_pending_requests THEN
 PTAC operationsTheory.collect_pending_requests THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 4 THEN
 AIRTAC THEN
 STAC
 ,
 PTAC write_propertiesTheory.REGISTER_REQUESTING_WRITE_ADDRESSES THEN
 AIRTAC THEN
 STAC
]
QED

Theorem WRITING_WRITABLE_MEMORY_ADDRESS_PRESERVES_R_W_LEMMA:
!device_characteristics address_bytes memory1 memory2.
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  EVERY (device_characteristics.dma_characteristics.W memory1) (MAP FST address_bytes) /\
  memory2 = update_memory memory1 address_bytes
  ==>
  device_characteristics.dma_characteristics.R memory2 = device_characteristics.dma_characteristics.R memory1 /\
  device_characteristics.dma_characteristics.W memory2 = device_characteristics.dma_characteristics.W memory1
Proof
INTRO_TAC THEN
ITAC write_properties_lemmasTheory.WRITING_WRITABLE_MEMORY_PRESERVES_UNWRITABLE_MEMORY_LEMMA THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_READABLE_WRITABLE THEN
AIRTAC THEN
STAC
QED

Theorem R_W_EQ_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA:
!device_characteristics memory1 memory2 device.
  device_characteristics.dma_characteristics.R memory2 = device_characteristics.dma_characteristics.R memory1 /\
  device_characteristics.dma_characteristics.W memory2 = device_characteristics.dma_characteristics.W memory1 /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory1 device
  ==>
  INVARIANT_FETCH_BD_L2 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC INVARIANT_FETCH_BD_L2 THEN
STAC
QED

Theorem R_W_EQ_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA:
!device_characteristics memory1 memory2 device.
  device_characteristics.dma_characteristics.R memory2 = device_characteristics.dma_characteristics.R memory1 /\
  device_characteristics.dma_characteristics.W memory2 = device_characteristics.dma_characteristics.W memory1 /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory1 device
  ==>
  INVARIANT_UPDATE_BD_L2 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC INVARIANT_UPDATE_BD_L2 THEN
STAC
QED

Theorem R_W_EQ_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA:
!device_characteristics memory1 memory2 device.
  device_characteristics.dma_characteristics.R memory2 = device_characteristics.dma_characteristics.R memory1 /\
  device_characteristics.dma_characteristics.W memory2 = device_characteristics.dma_characteristics.W memory1 /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory1 device
  ==>
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC INVARIANT_TRANSFER_DATA_L2 THEN
STAC
QED

Theorem R_W_EQ_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA:
!device_characteristics memory1 memory2 device.
  device_characteristics.dma_characteristics.R memory2 = device_characteristics.dma_characteristics.R memory1 /\
  device_characteristics.dma_characteristics.W memory2 = device_characteristics.dma_characteristics.W memory1 /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory1 device
  ==>
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC INVARIANT_WRITE_BACK_BD_L2 THEN
STAC
QED

Theorem R_W_EQ_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA:
!device_characteristics memory1 memory2 device.
  device_characteristics.dma_characteristics.R memory2 = device_characteristics.dma_characteristics.R memory1 /\
  device_characteristics.dma_characteristics.W memory2 = device_characteristics.dma_characteristics.W memory1 /\
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory1 device
  ==>
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC INVARIANT_SCRATCHPAD_R_L2 THEN
STAC
QED

Theorem R_W_EQ_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA:
!device_characteristics memory1 memory2 device.
  device_characteristics.dma_characteristics.R memory2 = device_characteristics.dma_characteristics.R memory1 /\
  device_characteristics.dma_characteristics.W memory2 = device_characteristics.dma_characteristics.W memory1 /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory1 device
  ==>
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC INVARIANT_SCRATCHPAD_W_L2 THEN
STAC
QED

Theorem DEVICE_MEMORY_WRITE_DEVICE_PRESERVES_INVARIANT_L2_LEMMA:
!device_characteristics device1 device2 address_bytes memory.
  device_transition_l2 device_characteristics device1 (memory, device_memory_write address_bytes) device2 /\
  INVARIANT_L2 device_characteristics memory device1
  ==>
  INVARIANT_L2 device_characteristics memory device2
Proof
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
ETAC stateTheory.device_transition_labels_type_11 THEN
NRLTAC 2 THEN
IRTAC dma_request_served_invariant_l2_preservation_lemmasTheory.DMA_REQUEST_SERVED_L2_PRESERVES_INVARIANT_L2_LEMMA THEN
STAC
QED

Theorem DEVICE_MEMORY_WRITE_MEMORY_PRESERVES_INVARIANT_L2_LEMMA:
!device_characteristics device1 device2 address_bytes memory1 memory2.
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics /\
  device_transition_l2 device_characteristics device1 (memory1, device_memory_write address_bytes) device2 /\
  memory2 = update_memory memory1 address_bytes /\
  INVARIANT_L1 device_characteristics memory1 device1 /\
  INVARIANT_L2 device_characteristics memory1 device2
  ==>
  INVARIANT_L2 device_characteristics memory2 device2
Proof
REWRITE_TAC [l2Theory.device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
INTRO_TAC THEN
AXTAC THEN
ETAC stateTheory.device_transition_labels_type_11 THEN
NRLTAC 2 THEN
IRTAC INVARIANT_L1_IMPLIES_PENDING_MEMORY_WRITE_REQUEST_W_LEMMA THEN
IRTAC WRITING_WRITABLE_MEMORY_ADDRESS_PRESERVES_R_W_LEMMA THEN
ETAC INVARIANT_L2 THEN
ITAC R_W_EQ_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA THEN
ITAC R_W_EQ_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA THEN
ITAC R_W_EQ_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA THEN
ITAC R_W_EQ_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA THEN
ITAC R_W_EQ_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA THEN
ITAC R_W_EQ_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA THEN
STAC
QED

val _ = export_theory();

