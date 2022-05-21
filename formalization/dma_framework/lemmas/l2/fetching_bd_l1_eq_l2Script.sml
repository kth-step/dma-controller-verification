open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory proof_obligations_dma_l2Theory invariant_l2Theory l1Theory l2Theory;

val _ = new_theory "fetching_bd_l1_eq_l2";

Theorem INVARIANT_L2_IMPLIES_BD_RAS_R_LEMMA:
!device_characteristics memory device bd bd_ras bd_was update_cycle_flags
 bds_to_fetch channel_id.
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INVARIANT_L2 device_characteristics memory device /\
  ((bd, bd_ras, bd_was), update_cycle_flags)::bds_to_fetch = (schannel device channel_id).queue.bds_to_fetch
  ==>
  EVERY (device_characteristics.dma_characteristics.R memory) bd_ras
Proof
INTRO_TAC THEN
PTAC INVARIANT_L2 THEN
PTAC INVARIANT_FETCH_BD_L2 THEN
INST_IMP_TAC lists_lemmasTheory.MEM_HD_LEMMA THEN
ITAC lists_lemmasTheory.MEM_HD_LEMMA THEN
AIRTAC THEN
PTAC BD_READ THEN
AIRTAC THEN
STAC
QED

Theorem FILTERED_READABLE_ADDRESSES_IMPLIES_READABLE_ADDRESSES_LEMMA:
!device_characteristics memory readable_addresses addresses filtered_addresses.
  EVERY (device_characteristics.dma_characteristics.R memory) readable_addresses /\
  filtered_addresses = FILTER (λaddress. MEM address readable_addresses) addresses
  ==>
  EVERY (device_characteristics.dma_characteristics.R memory) filtered_addresses
Proof
INTRO_TAC THEN
ETAC listTheory.EVERY_MEM THEN
INTRO_TAC THEN
LRTAC THEN
ETAC listTheory.MEM_FILTER THEN
APP_SCALAR_TAC THEN
AIRTAC THEN
STAC
QED

Theorem BD_READ_ADDRESSES_ABSTRACT_IMPLIES_READABLE_ADDRESSES_LEMMA:
!device_characteristics channel_id memory device channel fetch_bd_addresses fetch_bd_read_addresses.
  EXTERNAL_BDS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INVARIANT_L2 device_characteristics memory device /\
  channel = schannel device channel_id /\
  fetch_bd_read_addresses = bd_read_addresses channel.queue.bds_to_fetch fetch_bd_addresses
  ==>
  EVERY (device_characteristics.dma_characteristics.R memory) fetch_bd_read_addresses
Proof
INTRO_TAC THEN
PTAC bd_queuesTheory.bd_read_addresses THENL
[
 ASM_REWRITE_TAC [listTheory.EVERY_DEF]
 ,
 IRTAC INVARIANT_L2_IMPLIES_BD_RAS_R_LEMMA THEN
 ALL_LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 ALL_RLTAC THEN
 ITAC FILTERED_READABLE_ADDRESSES_IMPLIES_READABLE_ADDRESSES_LEMMA THEN
 STAC
]
QED

Theorem FETCHING_BD_L2_EQ_L1_LEMMA:
!device_characteristics environment device internal_state_pre_scheduling
 internal_state channel function_state scheduler pipelines
 pending_register_memory_accesses channel_id dma_channel_operation memory.
  PROOF_OBLIGATIONS_DMA_L2 device_characteristics /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device internal_state_pre_scheduling
    internal_state channel function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation /\
  INVARIANT_L2 device_characteristics memory device
  ==>
  (fetching_bd_l2 device_characteristics channel_id        internal_state channel =
   fetching_bd_l1 device_characteristics channel_id memory internal_state channel)
Proof
INTRO_TAC THEN
PTAC fetching_bd_l2 THEN PTAC fetching_bd_l1 THENL
[
 STAC
 ,
 STAC
 ,
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN
 ITAC proof_obligations_dma_l2_lemmasTheory.PROOF_OBLIGATIONS_DMA_L2_INTERNAL_DMA_OPERATION_IMPLIES_VALID_CHANNEL_ID_LEMMA THEN
 ITAC internal_operation_lemmasTheory.INTERNAL_DMA_OPERATION_IMPLIES_CHANNEL_STATE_LEMMA THEN
 IRTAC state_lemmasTheory.NOT_INTERNAL_BDS_IMPLIES_EXTERNAL_BDS_LEMMA THEN
 ITAC BD_READ_ADDRESSES_ABSTRACT_IMPLIES_READABLE_ADDRESSES_LEMMA THEN
 CONTR_ASMS_TAC
 ,
 STAC
]
QED

val _ = export_theory();
