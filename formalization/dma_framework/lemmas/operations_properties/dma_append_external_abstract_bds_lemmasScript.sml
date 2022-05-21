open HolKernel Parse boolLib bossLib helper_tactics;
open read_propertiesTheory access_propertiesTheory;

val _ = new_theory "dma_append_external_abstract_bds_lemmas";

Theorem APPEND_BDS_CHANNELS_IMPLIES_PENDING_ACCESSES_RESTRICTED_LEMMA:
!R W memory dma_characteristics channels1 channels2 internal_state.
  channels2 = append_bds_channels dma_characteristics memory channels1 internal_state
  ==>
  !channel_id. PENDING_ACCESSES_RESTRICTED R W memory (THE (channels1 channel_id)) (THE (channels2 channel_id))
Proof
INTRO_TAC THEN
GEN_TAC THEN
ETAC PENDING_ACCESSES_RESTRICTED THEN
REWRITE_TAC [PENDING_ACCESSES_RESTRICTED_FETCHING_BD, PENDING_ACCESSES_RESTRICTED_UPDATING_BD] THEN
REWRITE_TAC [PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA, PENDING_ACCESSES_RESTRICTED_WRITING_BACK_BD] THEN
REWRITE_TAC [PENDING_ACCESSES_UNMODIFIED_FETCHING_BD, PENDING_ACCESSES_UNMODIFIED_UPDATING_BD] THEN
REWRITE_TAC [PENDING_ACCESSES_UNMODIFIED_TRANSFERRING_DATA, PENDING_ACCESSES_UNMODIFIED_WRITING_BACK_BD] THEN
ITAC append_bds_lemmasTheory.APPEND_BDS_CHANNELS_PRESERVES_PENDING_ACCESSES_LEMMA THEN
STAC
QED

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_IMPLIES_PENDING_ACCESSES_RESTRICTED_LEMMA:
!memory device_characteristics device1 device2.
  device2 = dma_append_external_abstract_bds device_characteristics memory device1
  ==>
  !R W channel_id.
    PENDING_ACCESSES_RESTRICTED R W memory (schannel device1 channel_id) (schannel device2 channel_id)
Proof
INTRO_TAC THEN
REPEAT GEN_TAC THEN
PTAC operationsTheory.dma_append_external_abstract_bds THEN
ETAC stateTheory.schannel THEN
LRTAC THEN
RECORD_TAC THEN
ITAC APPEND_BDS_CHANNELS_IMPLIES_PENDING_ACCESSES_RESTRICTED_LEMMA THEN
STAC
QED







Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_IMPLIES_PENDING_ACCESSES_UNMODIFIED_REGISTER_LEMMA:
!device_characteristics memory device1 device2.
  device2 = dma_append_external_abstract_bds device_characteristics memory device1
  ==>
  PENDING_ACCESSES_UNMODIFIED_REGISTER device1 device2
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_append_external_abstract_bds THEN
PTAC PENDING_ACCESSES_UNMODIFIED_REGISTER THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_DEVICE_REQUESTING_R_ADDRESSES_LEMMA:
!device_characteristics memory device1 device2.
  device2 = dma_append_external_abstract_bds device_characteristics memory device1 /\
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
 IRTAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_IMPLIES_PENDING_ACCESSES_RESTRICTED_LEMMA THEN
 ITAC read_properties_lemmasTheory.PENDING_ACCESSES_RESTRICTED_PRESERVES_CHANNEL_R_LEMMA THEN
 STAC
 ,
 ITAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_IMPLIES_PENDING_ACCESSES_UNMODIFIED_REGISTER_LEMMA THEN
 ITAC read_properties_lemmasTheory.PENDING_ACCESSES_UNMODIFIED_REGISTER_PRESERVES_REGISTER_REQUESTING_READ_ADDRESSES_LEMMA THEN
 STAC
]
QED

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_DEVICE_REQUESTING_W_ADDRESSES_LEMMA:
!device_characteristics memory device1 device2.
  device2 = dma_append_external_abstract_bds device_characteristics memory device1 /\
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
 IRTAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_IMPLIES_PENDING_ACCESSES_RESTRICTED_LEMMA THEN
 ITAC write_properties_lemmasTheory.PENDING_ACCESSES_RESTRICTED_PRESERVES_CHANNEL_W_LEMMA THEN
 STAC
 ,
 ITAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_IMPLIES_PENDING_ACCESSES_UNMODIFIED_REGISTER_LEMMA THEN
 ITAC write_properties_lemmasTheory.PENDING_ACCESSES_UNMODIFIED_REGISTER_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA THEN
 STAC
]
QED

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_DEVICE_REQUESTING_R_W_ADDRESSES_LEMMA:
!device_characteristics memory device1 device2.
  device2 = dma_append_external_abstract_bds device_characteristics memory device1 /\
  DEVICE_REQUESTING_READ_ADDRESSES device_characteristics memory device1 /\
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device1
  ==>
  DEVICE_REQUESTING_READ_ADDRESSES device_characteristics memory device2 /\
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ITAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_DEVICE_REQUESTING_R_ADDRESSES_LEMMA THEN
ITAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_DEVICE_REQUESTING_W_ADDRESSES_LEMMA THEN
STAC
QED






Theorem PRESERVED_CHANNEL_OR_EXTENDED_ABSTRACT_BDS_TO_FETCH_PRESERVED_CONCRETE_QUEUE_LEMMA:
!device_characteristics channel_id bds_to_fetch memory1 memory2 channel1 channel2 device.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch /\
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL channel1 channel2 (bds_to_fetch memory2 device.dma_state.internal_state) /\
  MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W device_characteristics device.dma_state.internal_state memory1 memory2 /\
  channel1.queue.bds_to_fetch = bds_to_fetch memory1 device.dma_state.internal_state
  ==>
  channel2.queue.bds_to_fetch = bds_to_fetch memory2 device.dma_state.internal_state
Proof
INTRO_TAC THEN
ETAC proof_obligationsTheory.MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W THEN
AIRTAC THEN
AXTAC THEN
WEAKEN_TAC is_forall THEN
RLTAC THEN
ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL THEN
SPLIT_ASM_DISJS_TAC THENL
[
 ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH THEN
 ETAC operationsTheory.APPENDED_BDS THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 ETAC operationsTheory.NOT_EXTENDED_ABSTRACT_BDS_TO_FETCH_AND_UNCHANGED_CHANNEL THEN
 ETAC operationsTheory.EXTENDED_BDS THEN
 LRTAC THEN
 LRTAC THEN
 ETAC ((GEN_ALL o last o CONJUNCTS o SPEC_ALL) boolTheory.IMP_CLAUSES) THEN
 RW_HYPS_TAC listTheory.APPEND_11 THEN
 ETAC ((GEN_ALL o last o CONJUNCTS o SPEC_ALL) boolTheory.IMP_CLAUSES) THEN
 RW_HYPS_TAC (GSYM boolTheory.EXISTS_REFL) THEN
 SOLVE_F_ASM_TAC
]
QED

Theorem MEMORY_WRITE_APPENDS_EXTERNAL_BDS_AND_DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_EQ_ABSTRACT_EXTERNAL_BDS_TO_FETCH_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device31 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id bds_to_fetch memory1 memory2 channel1 channel2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch /\
  MEMORY_WRITE_APPENDS_EXTERNAL_CONCRETE_BDS_R_W device_characteristics device31.dma_state.internal_state memory1 memory2 /\
  device22 = dma_append_external_abstract_bds device_characteristics memory2 device21 /\
  channel1 = schannel device21 channel_id /\
  channel2 = schannel device22 channel_id /\
  device21.dma_state.internal_state = device31.dma_state.internal_state /\
  channel1.queue.bds_to_fetch = bds_to_fetch memory1 device31.dma_state.internal_state
  ==>
  channel2.queue.bds_to_fetch = bds_to_fetch memory2 device31.dma_state.internal_state
Proof
INTRO_TAC THEN
ITAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
FITAC PRESERVED_CHANNEL_OR_EXTENDED_ABSTRACT_BDS_TO_FETCH_PRESERVED_CONCRETE_QUEUE_LEMMA THEN
STAC
QED











Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_IMPLIES_EXTENDED_ABSTRACT_BDS_OR_PRESERVED_CHANNEL_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id bds_to_fetch memory2 channel1 channel2.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory2 device1.dma_state.internal_state /\
  device2 = dma_append_external_abstract_bds device_characteristics memory2 device1 /\
  channel1 = schannel device1 channel_id /\
  channel2 = schannel device2 channel_id
  ==>
  (channel2.queue.bds_to_fetch = bds_to_fetch /\
   (?appended_bds. channel2 = channel1 with queue := channel1.queue with bds_to_fetch := channel1.queue.bds_to_fetch ++ appended_bds)) \/
  channel2 = channel1
Proof
INTRO_TAC THEN
IRTAC append_bds_lemmasTheory.DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_OR_EXTENDS_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL THEN
SPLIT_ASM_DISJS_TAC THENL
[
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
 ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH THEN
 ETAC operationsTheory.APPENDED_BDS THEN
 ETAC operationsTheory.EXTENDED_BDS THEN
 AXTAC THEN
 CONJ_TAC THENL
 [
  ALL_LRTAC THEN RECORD_TAC THEN STAC
  ,
  ALL_LRTAC THEN RECORD_TAC THEN EXISTS_EQ_TAC
 ]
 ,
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 ETAC operationsTheory.NOT_EXTENDED_ABSTRACT_BDS_TO_FETCH_AND_UNCHANGED_CHANNEL THEN
 STAC
]
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

Theorem DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA:
!device_characteristics memory device1 device2.
  device2 = dma_append_external_abstract_bds device_characteristics memory device1
  ==>
  device2.dma_state.internal_state = device1.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_append_external_abstract_bds THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_APPEND_INTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA:
!device_characteristics memory_option device1 device2.
  device2 = dma_append_internal_abstract_bds device_characteristics memory_option device1
  ==>
  device2.dma_state.internal_state = device1.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_append_internal_abstract_bds THEN TRY STAC THEN
IRTAC DMA_APPEND_EXTERNAL_ABSTRACT_BDS_PRESERVES_INTERNAL_STATE_LEMMA THEN
STAC
QED

val _ = export_theory();

