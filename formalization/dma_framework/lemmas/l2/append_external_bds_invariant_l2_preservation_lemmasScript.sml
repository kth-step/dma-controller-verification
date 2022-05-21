open HolKernel Parse boolLib bossLib helper_tactics;
open proof_obligations_cpu_l1Theory invariant_l2Theory;

val _ = new_theory "append_external_bds_invariant_l2_preservation_lemmas";

Theorem EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_UPDATE_LEMMA:
!channel1 channel2 bds_to_fetch.
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL channel1 channel2 bds_to_fetch
  ==>
  channel2.queue.bds_to_update = channel1.queue.bds_to_update
Proof
INTRO_TAC THEN
PTAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL THEN
SPLIT_ASM_DISJS_TAC THENL
[
 PTAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH THEN
 PTAC operationsTheory.APPENDED_BDS THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 PTAC operationsTheory.NOT_EXTENDED_ABSTRACT_BDS_TO_FETCH_AND_UNCHANGED_CHANNEL THEN
 STAC
]
QED

Theorem EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_PROCESS_LEMMA:
!channel1 channel2 bds_to_fetch.
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL channel1 channel2 bds_to_fetch
  ==>
  channel2.queue.bds_to_process = channel1.queue.bds_to_process
Proof
INTRO_TAC THEN
PTAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL THEN
SPLIT_ASM_DISJS_TAC THENL
[
 PTAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH THEN
 PTAC operationsTheory.APPENDED_BDS THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 PTAC operationsTheory.NOT_EXTENDED_ABSTRACT_BDS_TO_FETCH_AND_UNCHANGED_CHANNEL THEN
 STAC
]
QED

Theorem EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_WRITE_BACK_LEMMA:
!channel1 channel2 bds_to_fetch.
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL channel1 channel2 bds_to_fetch
  ==>
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
PTAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL THEN
SPLIT_ASM_DISJS_TAC THENL
[
 PTAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH THEN
 PTAC operationsTheory.APPENDED_BDS THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 PTAC operationsTheory.NOT_EXTENDED_ABSTRACT_BDS_TO_FETCH_AND_UNCHANGED_CHANNEL THEN
 STAC
]
QED



Theorem APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_DEFINED_CHANNELS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory.
  DEFINED_CHANNELS device_characteristics device1 /\
  device2 = append_external_abstract_bds_l2 device_characteristics memory device1
  ==>
  DEFINED_CHANNELS device_characteristics device2
Proof
INTRO_TAC THEN
ETAC stateTheory.DEFINED_CHANNELS THEN
ETAC stateTheory.VALID_CHANNELS THEN
INTRO_TAC THEN
PTAC l2Theory.append_external_abstract_bds_l2 THENL
[
 IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_SOME_LEMMA THEN STAC
 ,
 AIRTAC THEN STAC
]
QED

Theorem EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_IMPLIES_EXTENSION_OR_PRESERVATION_LEMMA:
!channel1 channel2 abstract_bds.
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL channel1 channel2 abstract_bds
  ==>
  ((?appended_bds. abstract_bds = channel1.queue.bds_to_fetch ++ appended_bds) /\
   (channel2 = channel1 with queue := channel1.queue with bds_to_fetch := abstract_bds)) \/
  (~(?appended_bds. abstract_bds = channel1.queue.bds_to_fetch ++ appended_bds) /\
   (channel2 = channel1))
Proof
INTRO_TAC THEN
ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL THEN
ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH THEN
ETAC operationsTheory.NOT_EXTENDED_ABSTRACT_BDS_TO_FETCH_AND_UNCHANGED_CHANNEL THEN
ETAC operationsTheory.EXTENDED_BDS THEN
ETAC operationsTheory.APPENDED_BDS THEN
STAC
QED

Theorem CHANNEL2_EQ_APPENDED_CHANNEL1_IMPLIES_EQ_EXTENSIONS_LEMMA:
!channel1 channel2 appended_bds bd_ras_was_u_cs.
  channel2 = channel1 with queue := channel1.queue with bds_to_fetch := channel1.queue.bds_to_fetch ++ appended_bds /\
  channel2.queue.bds_to_fetch = channel1.queue.bds_to_fetch ++ bd_ras_was_u_cs
  ==>
  appended_bds = bd_ras_was_u_cs
Proof
INTRO_TAC THEN
LRTAC THEN
RECORD_TAC THEN
ETAC listTheory.APPEND_11 THEN
STAC
QED

Theorem APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory1 memory2.
  DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ device_characteristics memory1 memory2 device1 /\
  MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W device_characteristics device1.dma_state.internal_state memory1 memory2 /\
  device2 = append_external_abstract_bds_l2 device_characteristics memory2 device1 /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory1 device1 device1 /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory1 device1
  ==>
  INVARIANT_FETCH_BD_L2 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
PTAC l2Theory.append_external_abstract_bds_l2 THENL
[
 ITAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
 ETAC INVARIANT_FETCH_BD_L2 THEN
 INTRO_TAC THEN
 ITAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_IMPLIES_EXTENDED_ABSTRACT_BDS_OR_PRESERVED_CHANNEL_LEMMA THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  AXTAC THEN
  ITAC internal_operation_lemmasTheory.MEM_APPENDED_CHANNEL2_BDS_TO_FETCH_IMPLIES_MEM_CHANNEL1_BDS_TO_FETCH_OR_APPENDED_BDS_LEMMA THEN
  SPLIT_ASM_DISJS_TAC THENL
  [
   AITAC THEN
   ITAC cpu_invariant_l2_preservation_lemmasTheory.BD_TO_FETCH_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA THEN
   PTAC DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
   AITAC THEN
   ETAC stateTheory.R_W_EQ THEN
   NLRTAC 2 THEN
   RLTAC THEN
   RLTAC THEN
   STAC
   ,
   WEAKEN_TAC is_forall THEN
   ETAC proof_obligationsTheory.MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W THEN
   AITAC THEN
   AXTAC THEN
   PTAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
   AITAC THEN
   IRTAC CHANNEL2_EQ_APPENDED_CHANNEL1_IMPLIES_EQ_EXTENSIONS_LEMMA THEN
   AIRTAC THEN
   ALL_LRTAC THEN
   STAC
  ]
  ,
  LRTAC THEN
  AITAC THEN
  ITAC cpu_invariant_l2_preservation_lemmasTheory.BD_TO_FETCH_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA THEN
  PTAC DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
  AIRTAC THEN
  ETAC stateTheory.R_W_EQ THEN
  NRLTAC 2 THEN
  STAC
 ]
 ,
 RLTAC THEN
 ETAC INVARIANT_FETCH_BD_L2 THEN
 INTRO_TAC THEN
 AITAC THEN
 CONJS_TAC THEN TRY (REWRITE_TAC [stateTheory.BD_READ, stateTheory.BD_WRITE] THEN STAC) THEN
 ITAC cpu_invariant_l2_preservation_lemmasTheory.BD_TO_FETCH_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA THEN
 PTAC DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
 AIRTAC THEN
 ETAC stateTheory.R_W_EQ THEN
 ALL_LRTAC THEN
 STAC
]
QED

Theorem APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_BDS_TO_UPDATE_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id memory channel1 channel2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  device2 = dma_append_external_abstract_bds device_characteristics memory device1 /\
  channel1 = schannel device1 channel_id /\
  channel2 = schannel device2 channel_id
  ==>
  channel2.queue.bds_to_update = channel1.queue.bds_to_update
Proof
INTRO_TAC THEN
IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
IRTAC internal_operation_lemmasTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_UPDATE_LEMMA THEN
STAC
QED

Theorem APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_BDS_TO_PROCESS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id memory channel1 channel2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  device2 = dma_append_external_abstract_bds device_characteristics memory device1 /\
  channel1 = schannel device1 channel_id /\
  channel2 = schannel device2 channel_id
  ==>
  channel2.queue.bds_to_process = channel1.queue.bds_to_process
Proof
INTRO_TAC THEN
IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
IRTAC internal_operation_lemmasTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_PROCESS_LEMMA THEN
STAC
QED

Theorem APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_BDS_TO_WRITE_BACK_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id memory channel1 channel2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  device2 = dma_append_external_abstract_bds device_characteristics memory device1 /\
  channel1 = schannel device1 channel_id /\
  channel2 = schannel device2 channel_id
  ==>
  channel2.queue.bds_to_write_back = channel1.queue.bds_to_write_back
Proof
INTRO_TAC THEN
IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
IRTAC internal_operation_lemmasTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_WRITE_BACK_LEMMA THEN
STAC
QED

Theorem APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA:
!device_characteristics device1 device2 memory1 memory2.
  DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ device_characteristics memory1 memory2 device1 /\
  device2 = append_external_abstract_bds_l2 device_characteristics memory2 device1 /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory1 device1
  ==>
  INVARIANT_UPDATE_BD_L2 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
PTAC l2Theory.append_external_abstract_bds_l2 THENL
[
 ITAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
 ETAC INVARIANT_UPDATE_BD_L2 THEN
 INTRO_TAC THEN
 ITAC APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_BDS_TO_UPDATE_LEMMA THEN
 LRTAC THEN
 AITAC THEN
 ITAC cpu_invariant_l2_preservation_lemmasTheory.BD_TO_UPDATE_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA THEN
 PTAC DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
 AIRTAC THEN
 ETAC stateTheory.R_W_EQ THEN
 NRLTAC 2 THEN
 STAC
 ,
 ETAC INVARIANT_UPDATE_BD_L2 THEN
 RLTAC THEN
 INTRO_TAC THEN
 AITAC THEN
 ITAC cpu_invariant_l2_preservation_lemmasTheory.BD_TO_UPDATE_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA THEN
 PTAC DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
 AIRTAC THEN
 ETAC stateTheory.R_W_EQ THEN
 NRLTAC 2 THEN
 STAC
]
QED

Theorem APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA:
!device_characteristics device1 device2 memory1 memory2.
  DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ device_characteristics memory1 memory2 device1 /\
  device2 = append_external_abstract_bds_l2 device_characteristics memory2 device1 /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory1 device1
  ==>
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
PTAC l2Theory.append_external_abstract_bds_l2 THENL
[
 ITAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
 ETAC INVARIANT_TRANSFER_DATA_L2 THEN
 INTRO_TAC THEN
 ITAC APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_BDS_TO_PROCESS_LEMMA THEN
 LRTAC THEN
 AITAC THEN
 ITAC cpu_invariant_l2_preservation_lemmasTheory.BD_TO_PROCESS_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA THEN
 PTAC DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
 AIRTAC THEN
 ETAC stateTheory.R_W_EQ THEN
 NRLTAC 2 THEN
 STAC
 ,
 ETAC INVARIANT_TRANSFER_DATA_L2 THEN
 RLTAC THEN
 INTRO_TAC THEN
 AITAC THEN
 ITAC cpu_invariant_l2_preservation_lemmasTheory.BD_TO_PROCESS_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA THEN
 PTAC DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
 AIRTAC THEN
 ETAC stateTheory.R_W_EQ THEN
 NRLTAC 2 THEN
 STAC
]
QED

Theorem APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA:
!device_characteristics device1 device2 memory1 memory2.
  DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ device_characteristics memory1 memory2 device1 /\
  device2 = append_external_abstract_bds_l2 device_characteristics memory2 device1 /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory1 device1
  ==>
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
PTAC l2Theory.append_external_abstract_bds_l2 THENL
[
 ETAC INVARIANT_WRITE_BACK_BD_L2 THEN
 INTRO_TAC THEN
 ITAC APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_BDS_TO_WRITE_BACK_LEMMA THEN
 LRTAC THEN
 AITAC THEN
 ITAC cpu_invariant_l2_preservation_lemmasTheory.BD_TO_WRITE_BACK_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA THEN
 PTAC DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
 AIRTAC THEN
 ETAC stateTheory.R_W_EQ THEN
 NRLTAC 2 THEN
 STAC
 ,
 RLTAC THEN
 ETAC INVARIANT_WRITE_BACK_BD_L2 THEN
 INTRO_TAC THEN
 AITAC THEN
 ITAC cpu_invariant_l2_preservation_lemmasTheory.BD_TO_WRITE_BACK_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA THEN
 PTAC DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
 AIRTAC THEN
 ETAC stateTheory.R_W_EQ THEN
 NRLTAC 2 THEN
 STAC
]
QED

Theorem APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA:
!device_characteristics device1 device2 memory1 memory2.
  DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ device_characteristics memory1 memory2 device1 /\
  NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W device_characteristics device1 memory1 memory2 /\
  device2 = append_external_abstract_bds_l2 device_characteristics memory2 device1 /\
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory1 device1
  ==>
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
PTAC l2Theory.append_external_abstract_bds_l2 THENL
[
 IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
 ETAC INVARIANT_SCRATCHPAD_R_L2 THEN
 LRTAC THEN
 INTRO_TAC THEN
 Cases_on ‘DMAC_CAN_ACCESS_MEMORY device_characteristics device1’ THENL
 [
  PTAC DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
  AIRTAC THEN
  AIRTAC THEN
  ETAC stateTheory.R_W_EQ THEN
  NRLTAC 2 THEN
  STAC
  ,
  PTAC proof_obligations_cpu_l2Theory.NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W THEN
  AITAC THEN
  AIRTAC THEN
  SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
  PTAC proof_obligationsTheory.SCRATCHPAD_R THEN
  AIRTAC THEN
  STAC
 ]
 ,
 RLTAC THEN
 Cases_on ‘DMAC_CAN_ACCESS_MEMORY device_characteristics device2’ THENL
 [
  PTAC DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
  AIRTAC THEN
  ETAC INVARIANT_SCRATCHPAD_R_L2 THEN
  INTRO_TAC THEN
  AITAC THEN
  PTAC stateTheory.R_W_EQ THEN
  NRLTAC 2 THEN
  STAC
  ,
  PTAC proof_obligations_cpu_l2Theory.NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W THEN
  AITAC THEN
  SPLIT_ASM_DISJS_TAC THENL
  [
   ETAC INVARIANT_SCRATCHPAD_R_L2 THEN
   INTRO_TAC THEN
   AITAC THEN
   STAC
   ,
   REWRITE_TAC [INVARIANT_SCRATCHPAD_R_L2] THEN
   INTRO_TAC THEN
   PTAC proof_obligationsTheory.SCRATCHPAD_R THEN
   AITAC THEN
   STAC
  ]
 ]
]
QED

Theorem APPEND_EXTERNAL_ABSTRACT_BDS_L2_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA:
!device_characteristics device1 device2 memory1 memory2.
  DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ device_characteristics memory1 memory2 device1 /\
  NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W device_characteristics device1 memory1 memory2 /\
  device2 = append_external_abstract_bds_l2 device_characteristics memory2 device1 /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory1 device1
  ==>
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
PTAC l2Theory.append_external_abstract_bds_l2 THENL
[
 IRTAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
 ETAC INVARIANT_SCRATCHPAD_W_L2 THEN
 LRTAC THEN
 INTRO_TAC THEN
 Cases_on ‘DMAC_CAN_ACCESS_MEMORY device_characteristics device1’ THENL
 [
  PTAC DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
  AIRTAC THEN
  AIRTAC THEN
  ETAC stateTheory.R_W_EQ THEN
  NRLTAC 2 THEN
  STAC
  ,
  PTAC proof_obligations_cpu_l2Theory.NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W THEN
  AITAC THEN
  AIRTAC THEN
  SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
  PTAC proof_obligationsTheory.SCRATCHPAD_W THEN
  AIRTAC THEN
  STAC
 ]
 ,
 RLTAC THEN
 Cases_on ‘DMAC_CAN_ACCESS_MEMORY device_characteristics device2’ THENL
 [
  PTAC DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
  AIRTAC THEN
  ETAC INVARIANT_SCRATCHPAD_W_L2 THEN
  INTRO_TAC THEN
  AITAC THEN
  PTAC stateTheory.R_W_EQ THEN
  NRLTAC 2 THEN
  STAC
  ,
  PTAC proof_obligations_cpu_l2Theory.NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W THEN
  AITAC THEN
  SPLIT_ASM_DISJS_TAC THENL
  [
   ETAC INVARIANT_SCRATCHPAD_W_L2 THEN
   INTRO_TAC THEN
   AITAC THEN
   STAC
   ,
   REWRITE_TAC [INVARIANT_SCRATCHPAD_W_L2] THEN
   INTRO_TAC THEN
   PTAC proof_obligationsTheory.SCRATCHPAD_W THEN
   AITAC THEN
   STAC
  ]
 ]
]
QED

(*
Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_IMPLIES_APPEND_BDS_CHANNELS_LEMMA:
!device_characteristics memory device1 device2.
  device2 = dma_append_external_abstract_bds device_characteristics memory device1
  ==>
  device2.dma_state.channels = append_bds_channels device_characteristics.dma_characteristics memory device1.dma_state.channels device1.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_append_external_abstract_bds THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem APPEND_BDS_CHANNELS_IMPLIES_CHANNEL_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channels1 channels2 memory channel_id.
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device device /\
  channels1 = device.dma_state.channels /\
  channels2 = append_bds_channels device_characteristics.dma_characteristics memory channels1 device.dma_state.internal_state
  ==>
  (THE (channels2 channel_id)) = (THE (channels1 channel_id))
Proof
INTRO_TAC THEN
PTAC operationsTheory.append_bds_channels THEN
IRTAC (REWRITE_RULE [operationsTheory.APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS] append_bds_lemmasTheory.APPEND_BDS_CHANNELS_INDEX_EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS_LEMMA) THEN
Cases_on ‘VALID_CHANNEL_ID device_characteristics channel_id’ THENL
[
 ETAC stateTheory.channel_state_type_component_equality THEN
 ETAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
 AITAC THEN
 ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNELS THEN
 ETAC stateTheory.VALID_CHANNEL_ID THEN
 AIRTAC THEN
 ETAC stateTheory.schannel THEN
 RLTAC THEN
 ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH THEN
  ETAC operationsTheory.APPENDED_BDS THEN
  LRTAC THEN
  RECORD_TAC THEN
  REWRITE_TAC [] THEN
  ETAC stateTheory.queue_type_component_equality THEN
  RECORD_TAC THEN
  STAC
  ,
  ETAC operationsTheory.NOT_EXTENDED_ABSTRACT_BDS_TO_FETCH_AND_UNCHANGED_CHANNEL THEN STAC
 ]
 ,
 ETAC stateTheory.VALID_CHANNEL_ID THEN
 ETAC wordsTheory.WORD_NOT_LOWER_EQUAL THEN
 ETAC wordsTheory.WORD_HIGHER THEN
 ETAC operationsTheory.PRESERVED_CHANNELS THEN
 AIRTAC THEN
 STAC
]
QED

Theorem APPEND_BDS_CHANNELS_IMPLIES_CHANNEL_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 memory.
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device1 device1 /\
  device2 = dma_append_external_abstract_bds device_characteristics memory device1
  ==>
  !channel_id.
    schannel device2 channel_id = schannel device1 channel_id
Proof
INTRO_TAC THEN
IRTAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_IMPLIES_APPEND_BDS_CHANNELS_LEMMA THEN
IRTAC APPEND_BDS_CHANNELS_IMPLIES_CHANNEL_EQ_LEMMA THEN
REWRITE_TAC [stateTheory.schannel] THEN
STAC
QED

Theorem DEFINED_CHANNELS_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_IMPLIES_DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_CHANNELS_LEMMA:
!device_characteristics memory device1 device2.
  DEFINED_CHANNELS device_characteristics device1 /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device1 device1 /\
  device2 = dma_append_external_abstract_bds device_characteristics memory device1
  ==>
  device2.dma_state.channels = device1.dma_state.channels
Proof
INTRO_TAC THEN
ITAC APPEND_BDS_CHANNELS_IMPLIES_CHANNEL_EQ_LEMMA THEN
REWRITE_TAC [boolTheory.FUN_EQ_THM] THEN
GEN_TAC THEN
Cases_on ‘VALID_CHANNEL_ID device_characteristics x’ THENL
[
 ITAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_SOME_LEMMA THEN
 ETAC stateTheory.DEFINED_CHANNELS THEN
 ETAC stateTheory.VALID_CHANNELS THEN
 AIRTAC THEN
 PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
 PTAC optionTheory.IS_SOME_DEF THEN TRY SOLVE_F_ASM_TAC THEN
 RW_HYPS_TAC stateTheory.schannel THEN
 PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (Q.SPEC ‘x’ thm)) THEN
 LRTAC THEN
 LRTAC THEN
 ETAC optionTheory.THE_DEF THEN
 STAC
 ,
 IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_SOME_PRESERVED_LEMMA THEN
 PTAC optionTheory.IS_SOME_DEF THEN PTAC optionTheory.IS_SOME_DEF THEN TRY STAC THENL
 [
  ASSUME_TAC boolTheory.BOOL_EQ_DISTINCT THEN SPLIT_ASM_TAC THEN CONTR_ASMS_TAC
  ,
  ASSUME_TAC boolTheory.BOOL_EQ_DISTINCT THEN SPLIT_ASM_TAC THEN CONTR_ASMS_TAC
  ,
  RW_HYPS_TAC stateTheory.schannel THEN
  PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (Q.SPEC ‘x’ thm)) THEN
  LRTAC THEN
  LRTAC THEN
  ETAC optionTheory.THE_DEF THEN
  STAC
 ]
]
QED

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA:
!device_characteristics memory device1 device2.
  device2 = dma_append_external_abstract_bds device_characteristics memory device1
  ==>
  device2.dma_state.pending_register_related_memory_requests = device1.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_append_external_abstract_bds THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REPLIES_LEMMA:
!device_characteristics memory device1 device2.
  device2 = dma_append_external_abstract_bds device_characteristics memory device1
  ==>
  device2.dma_state.pending_register_related_memory_replies = device1.dma_state.pending_register_related_memory_replies
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_append_external_abstract_bds THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_FUNCTION_STATE_LEMMA:
!device_characteristics memory device1 device2.
  device2 = dma_append_external_abstract_bds device_characteristics memory device1
  ==>
  device2.function_state = device1.function_state
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_append_external_abstract_bds THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem DEFINED_CHANNELS_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_IMPLIES_DMA_APPEND_EXTERNAL_ABSTRACT_BDS_IMPLIES_DEVICE_EQ_LEMMA:
!device_characteristics memory device1 device2.
  DEFINED_CHANNELS device_characteristics device1 /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device1 device1 /\
  device2 = dma_append_external_abstract_bds device_characteristics memory device1
  ==>
  device1 = device2
Proof
INTRO_TAC THEN
ITAC DEFINED_CHANNELS_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_IMPLIES_DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_CHANNELS_LEMMA THEN
ITAC dma_append_external_abstract_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
ITAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA THEN
ITAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REPLIES_LEMMA THEN
IRTAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_FUNCTION_STATE_LEMMA THEN
ETAC stateTheory.device_state_type_component_equality THEN
ETAC stateTheory.dma_state_type_component_equality THEN
STAC
QED

Theorem DMA_STATE_EQ_TRANS_LEMMA:
!device1 device2 device3.
  DMA_STATE_EQ device1 device2 /\
  DMA_STATE_EQ device2 device3
  ==>
  DMA_STATE_EQ device1 device3
Proof
REWRITE_TAC [DMA_STATE_EQ] THEN
INTRO_TAC THEN
STAC
QED

Theorem DMA_STATE_EQ_PRESERVES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics memory device1 device2.
  DMA_STATE_EQ device1 device2 /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device1 device1
  ==>
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device2 device2
Proof
REWRITE_TAC [stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ, stateTheory.schannel, DMA_STATE_EQ] THEN
INTRO_TAC THEN
STAC
QED

Theorem DMA_STATE_EQ_PRESERVES_DEFINED_CHANNELS_LEMMA:
!device_characteristics device1 device2.
  DMA_STATE_EQ device1 device2 /\
  DEFINED_CHANNELS device_characteristics device1
  ==>
  DEFINED_CHANNELS device_characteristics device2
Proof
REWRITE_TAC [stateTheory.DEFINED_CHANNELS, stateTheory.schannel, DMA_STATE_EQ] THEN
INTRO_TAC THEN
STAC
QED

Theorem ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_REFL_IMPLIES_DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVE_ID_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (memory : 'interconnect_address_width memory_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  DEFINED_CHANNELS device_characteristics device1 /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device1 device1 /\
  DMA_STATE_EQ device1 device /\
  device2 = dma_append_external_abstract_bds device_characteristics memory device
  ==>
  device2 = device
Proof
INTRO_TAC THEN
ITAC DMA_STATE_EQ_PRESERVES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA THEN
ITAC DMA_STATE_EQ_PRESERVES_DEFINED_CHANNELS_LEMMA THEN
IRTAC DEFINED_CHANNELS_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_IMPLIES_DMA_APPEND_EXTERNAL_ABSTRACT_BDS_IMPLIES_DEVICE_EQ_LEMMA THEN
STAC
QED

Theorem DEVICE_EQ_IMPLIES_DMA_STATE_EQ_SYM_LEMMA:
!device1 device2.
  device1 = device2
  ==>
  DMA_STATE_EQ device2 device1
Proof
INTRO_TAC THEN
ETAC DMA_STATE_EQ THEN
STAC
QED

Theorem DEVICE_REGISTER_WRITE_L2_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_EXTERNAL_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics cpu1 cpu2 memory1 memory2 device1 device device2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_MEMORY_WRITE_APPENDS_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  DEFINED_CHANNELS device_characteristics device1 /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory1 device1 device1 /\
  EXTERNAL_BDS device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write cpu_address_bytes) cpu2 /\
  (device, dma_address_bytes) = device_register_write_l2 device_characteristics memory1 device1 cpu_address_bytes /\
  device2 = dma_append_external_abstract_bds device_characteristics memory2 device /\
  memory2 = update_memory memory1 dma_address_bytes
  ==>
  APPENDED_ABSTRACT_BDS_R_W device_characteristics memory1 memory2 device1 device2
Proof
INTRO_TAC THEN
PTAC l2Theory.device_register_write_l2 THEN
PTAC operationsTheory.device_register_write THENL
[
 IRTAC DMA_REGISTER_WRITE_L2_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
 RLTAC THEN
 IRTAC FUNCTION_REGISTER_WRITE_IMPLIES_DMA_STATE_EQ_LEMMA THEN
 ITAC ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_REFL_IMPLIES_DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVE_ID_LEMMA THEN
 RLTAC THEN
 IRTAC ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_DMA_STATE_EQ_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
 RLTAC THEN
 IRTAC DEVICE_EQ_IMPLIES_DMA_STATE_EQ_SYM_LEMMA THEN
 ITAC ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_REFL_IMPLIES_DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVE_ID_LEMMA THEN
 RLTAC THEN
 IRTAC ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_DMA_STATE_EQ_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
 RLTAC THEN
 IRTAC DEVICE_EQ_IMPLIES_DMA_STATE_EQ_SYM_LEMMA THEN
 ITAC ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_REFL_IMPLIES_DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVE_ID_LEMMA THEN
 RLTAC THEN
 IRTAC ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_DMA_STATE_EQ_IMPLIES_APPENDED_ABSTRACT_BDS_R_W_LEMMA THEN
 STAC
]
QED



Theorem DEVICE_REGISTER_WRITE_PRESERVES_INVARIANT_L2_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics device1 device2 cpu_address_bytes dma_address_bytes memory cpu1 cpu2.
  PROOF_OBLIGATION_REGISTER_WRITE_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_APPENDS_CONCRETE_BDS_EXTERNAL_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_REGISTER_WRITE_SCRATCHPAD_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory cpu1 /\
  cpu_transition cpu1 (cpu_memory_write cpu_address_bytes) cpu2 /\
  device_transition_l2 device_characteristics device1 (memory, device_register_write (cpu_address_bytes, dma_address_bytes)) device2 /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device1 device1 /\
  INVARIANT_L2 device_characteristics memory device1
  ==>
  INVARIANT_L2 device_characteristics memory device2
Proof
REWRITE_TAC [device_transitions_l2_cases] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [GSYM stateTheory.device_transition_labels_type_distinct] THEN
REWRITE_TAC [stateTheory.device_transition_labels_type_11] THEN
REWRITE_TAC [pairTheory.PAIR_EQ] THEN
INTRO_TAC THEN
AXTAC THEN
NRLTAC 3 THEN
WEAKEN_TAC is_disj THEN
PTAC l2Theory.device_register_write_l2 THEN
PTAC operationsTheory.device_register_write THENL
[
 PTAC operationsTheory.dma_register_write THEN
 EQ_PAIR_ASM_TAC THEN
 NLRTAC 2 THEN

här
 LRTAC THEN
 PTAC operationsTheory.dma_append_internal_abstract_bds THEN
 ETAC device_register_write_invariant_l2_preservation_lemmasTheory.ASSIGN_INTERNAL_STATE_PENDING_REGISTER_RELATED_MEMORY_REQUESTS THEN
 ITAC device_register_write_invariant_l2_preservation_lemmasTheory.REGISTER_WRITE_IMPLIES_SCRATCHPAD_R_W_L2_LEMMA THEN
 ITAC device_register_write_invariant_l2_preservation_lemmasTheory.REGISTER_WRITE_SCRATCHPAD_R_W_L2_IMPLIES_SCRATCHPAD_R_W_LEMMA THEN
 ITAC device_register_write_invariant_l2_preservation_lemmasTheory.REGISTER_WRITE_PRESERVES_INVARIANT_L2_LEMMA THEN
 ITAC device_register_write_invariant_l2_preservation_lemmasTheory.REGISTER_WRITE_IMPLIES_APPENDS_CONCRETE_BDS_EXTERNAL_R_W_LEMMA THEN
 EQ_PAIR_ASM_TAC THEN
 IRTAC device_register_write_invariant_l2_preservation_lemmasTheory.REGISTER_WRITE_APPEND_BDS_PRESERVES_INVARIANT_L2_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 PTAC operationsTheory.function_register_write THEN
 RLTAC THEN
 ETAC INVARIANT_L2 THEN
 ETAC stateTheory.DEFINED_CHANNELS THEN
 ETAC stateTheory.VALID_CHANNELS THEN
 ETAC INVARIANT_FETCH_BD_L2 THEN
 ETAC INVARIANT_UPDATE_BD_L2 THEN
 ETAC INVARIANT_TRANSFER_DATA_L2 THEN
 ETAC INVARIANT_WRITE_BACK_BD_L2 THEN
 ETAC INVARIANT_SCRATCHPAD_R_L2 THEN
 ETAC INVARIANT_SCRATCHPAD_W_L2 THEN
 RW_HYPS_TAC stateTheory.schannel THEN
 REWRITE_TAC [stateTheory.schannel] THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

*)

Theorem APPEND_NOT_EXTERNAL_BDS_PRESERVES_INVARIANT_L2_LEMMA:
!device_characteristics device1 device2 memory.
  ~EXTERNAL_BDS device_characteristics /\
  device_transition_l2 device_characteristics device1 (memory, external_bds_appended) device2 /\
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
RLTAC THEN
ETAC l2Theory.append_external_abstract_bds_l2 THEN
IF_SPLIT_TAC THENL
[
 CONTR_ASMS_TAC
 ,
 STAC
]
QED

Theorem PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY_IMPLIES_DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ_LEMMA:
!INVARIANT_CPU cpu_transition cpu1 address_bytes cpu2 memory1 memory2
 (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type) 
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes
  ==>
  DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ device_characteristics memory1 memory2 device1
Proof
INTRO_TAC THEN
ETAC proof_obligations_cpu_l1Theory.PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY THEN
AIRTAC THEN
STAC
QED

Theorem PROOF_OBLIGATION_CPU_PRESERVES_R_W_OR_SUPERSET_OF_SCRATCHPAD_IMPLIES_NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W_LEMMA:
!INVARIANT_CPU cpu_transition cpu1 address_bytes cpu2 memory1 memory2
 (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type) 
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_OR_SUPERSET_OF_SCRATCHPAD INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes
  ==>
  NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W device_characteristics device1 memory1 memory2
Proof
INTRO_TAC THEN
ETAC proof_obligations_cpu_l2Theory.PROOF_OBLIGATION_CPU_PRESERVES_R_W_OR_SUPERSET_OF_SCRATCHPAD THEN
AIRTAC THEN
STAC
QED

Theorem PROOF_OBLIGATION_CPU_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W_IMPLIES_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W_LEMMA:
!INVARIANT_CPU cpu_transition cpu1 address_bytes cpu2 memory1 memory2
 (device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type) 
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  PROOF_OBLIGATION_CPU_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  EXTERNAL_BDS device_characteristics /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes
  ==>
  MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W device_characteristics device1.dma_state.internal_state memory1 memory2
Proof
INTRO_TAC THEN
PTAC proof_obligations_cpu_l2Theory.PROOF_OBLIGATION_CPU_MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W THEN
AIRTAC THEN
STAC
QED

val _ = export_theory();

