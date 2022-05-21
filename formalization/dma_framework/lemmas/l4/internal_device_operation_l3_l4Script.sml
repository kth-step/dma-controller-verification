open HolKernel Parse boolLib bossLib helper_tactics;
open operationsTheory proof_obligationsTheory;
open l3Theory l4Theory invariant_l4Theory proof_obligations_dma_l4Theory;

val _ = new_theory "internal_device_operation_l3_l4";

Theorem PROOF_OBLIGATIONS_DMA_L4_FETCH_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics
  ==>
  PROOF_OBLIGATION_SCHEDULER device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ device_characteristics /\
  PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS device_characteristics
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATIONS_DMA_L4 THEN
STAC
QED

Theorem PROOF_OBLIGATIONS_DMA_L4_UPDATE_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics
  ==>
  PROOF_OBLIGATION_SCHEDULER device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_DECLARED_UPDATE_WRITES_BD_WAS device_characteristics
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATIONS_DMA_L4 THEN
STAC
QED

Theorem PROOF_OBLIGATIONS_DMA_L4_PROCESS_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics
  ==>
  PROOF_OBLIGATION_SCHEDULER device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_WRITE_REQUESTS_CONSISTENT_WITH_BD device_characteristics
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATIONS_DMA_L4 THEN
STAC
QED

Theorem PROOF_OBLIGATIONS_DMA_L4_WRITE_BACK_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics
  ==>
  PROOF_OBLIGATION_SCHEDULER device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_DECLARED_WRITE_BACK_WRITES_BD_WAS device_characteristics
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATIONS_DMA_L4 THEN
STAC
QED

Theorem CHANNEL_OPERATION_L4_EQ_L3_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (memory : 'interconnect_address_width memory_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 internal_state channel_id pipelines
 dma_channel_operation environment channel
 scheduler internal_state_pre_scheduling pending_register_memory_accesses function_state.
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device internal_state_pre_scheduling
    internal_state channel function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation /\
  INVARIANT_UPDATE_BD_BD_WRITE_L4 device_characteristics memory device /\
  INVARIANT_PROCESS_BD_DMA_WRITE_L4 device_characteristics memory device /\
  INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 device_characteristics memory device
  ==>
  (channel_operation_l4 device_characteristics channel_id dma_channel_operation (NONE : 'interconnect_address_width memory_type option) environment internal_state channel =
   channel_operation_l3 device_characteristics channel_id dma_channel_operation (SOME memory) environment internal_state channel)
Proof
REPEAT INTRO_TAC THEN
PTAC channel_operation_l4 THEN PTAC channel_operation_l3 THEN
PTAC channel_operation_case_l4 THEN PTAC channel_operation_case_l3 THENL
[
 IRTAC PROOF_OBLIGATIONS_DMA_L4_FETCH_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.INTERNAL_DMA_OPERATION_IMPLIES_VALID_CHANNEL_ID_LEMMA THEN
 ITAC fetching_bd_l3_eq_l4Theory.FETCHING_BD_L4_EQ_L3_LEMMA THEN QRLTAC THEN LRTAC THEN STAC
 ,
 IRTAC PROOF_OBLIGATIONS_DMA_L4_UPDATE_LEMMA THEN
 ITAC internal_operation_lemmasTheory.INTERNAL_DMA_OPERATION_SCHEDULER_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
 ITAC internal_operation_lemmasTheory.INTERNAL_DMA_OPERATION_SCHEDULER_IMPLIES_PIPELINES_LEMMA THEN
 ITAC internal_operation_lemmasTheory.INTERNAL_DMA_OPERATION_IMPLIES_CHANNEL_STATE_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.INTERNAL_DMA_OPERATION_IMPLIES_VALID_CHANNEL_ID_LEMMA THEN
 ITAC updating_bd_l3_eq_l4Theory.UPDATING_BD_L4_EQ_L3_LEMMA THEN
 LRTAC THEN
 LRTAC THEN
 STAC
 ,
 IRTAC PROOF_OBLIGATIONS_DMA_L4_PROCESS_LEMMA THEN
 ITAC internal_operation_lemmasTheory.INTERNAL_DMA_OPERATION_SCHEDULER_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
 ITAC internal_operation_lemmasTheory.INTERNAL_DMA_OPERATION_SCHEDULER_IMPLIES_SCRATCHPAD_ADDRESSES_EQ_LEMMA THEN
 ITAC internal_operation_lemmasTheory.INTERNAL_DMA_OPERATION_SCHEDULER_IMPLIES_BD_RAS_WAS_EQ_LEMMA THEN
 ITAC internal_operation_lemmasTheory.INTERNAL_DMA_OPERATION_SCHEDULER_IMPLIES_PIPELINES_LEMMA THEN
 ITAC internal_operation_lemmasTheory.INTERNAL_DMA_OPERATION_IMPLIES_CHANNEL_STATE_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.INTERNAL_DMA_OPERATION_IMPLIES_VALID_CHANNEL_ID_LEMMA THEN
 ITAC transferring_data_l3_eq_l4Theory.PROCESSING_BD_L4_EQ_L3_LEMMA THEN
 STAC
 ,
 IRTAC PROOF_OBLIGATIONS_DMA_L4_WRITE_BACK_LEMMA THEN
 ITAC internal_operation_lemmasTheory.INTERNAL_DMA_OPERATION_SCHEDULER_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
 ITAC internal_operation_lemmasTheory.INTERNAL_DMA_OPERATION_SCHEDULER_IMPLIES_PIPELINES_LEMMA THEN
 ITAC internal_operation_lemmasTheory.INTERNAL_DMA_OPERATION_IMPLIES_CHANNEL_STATE_LEMMA THEN
 IRTAC internal_operation_lemmasTheory.INTERNAL_DMA_OPERATION_IMPLIES_VALID_CHANNEL_ID_LEMMA THEN
 ITAC writing_back_bd_l3_eq_l4Theory.WRITING_BACK_BD_L4_EQ_L3_LEMMA THEN
 QLRTAC THEN
 LRTAC THEN
 LRTAC THEN
 STAC
]
QED

Theorem DEVICE_BSIM_L3_L4_INTERNAL_DEVICE_OPERATION_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (memory : 'interconnect_address_width memory_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 environment.
  PROOF_OBLIGATIONS_DMA_L4 device_characteristics /\
  INVARIANT_UPDATE_BD_BD_WRITE_L4 device_characteristics memory device /\
  INVARIANT_PROCESS_BD_DMA_WRITE_L4 device_characteristics memory device /\
  INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 device_characteristics memory device
  ==>
  internal_device_operation device_characteristics channel_operation_l3 (SOME memory) environment device =
  internal_device_operation device_characteristics channel_operation_l4 (NONE : 'interconnect_address_width memory_type option) environment device
Proof
INTRO_TAC THEN
REPEAT (PTAC internal_device_operation) THEN TRY STAC THEN
REPEAT (PTAC internal_dma_operation) THEN
ITAC state_lemmasTheory.DEVICE_CHANNELS_CHANNEL_ID_IMPLIES_SCHANNEL_LEMMA THEN
IRTAC ((GEN_ALL o #2 o EQ_IMP_RULE o SPEC_ALL) INTERNAL_DMA_OPERATION) THEN
ITAC CHANNEL_OPERATION_L4_EQ_L3_LEMMA THEN
ALL_LRTAC THEN
EQ_PAIR_ASM_TAC THEN
STAC
QED

val _ = export_theory();

