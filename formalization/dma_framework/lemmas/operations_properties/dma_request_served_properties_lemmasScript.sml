open HolKernel Parse boolLib bossLib helper_tactics;
open operationsTheory access_propertiesTheory;

val _ = new_theory "dma_request_served_properties_lemmas";

Theorem APPEND_REPLY_REMOVE_REQUEST_CHANNEL_IMPLIES_PENDING_ACCESSES_UNEXPANDED_LEMMA:
!channel1 channel2 serviced_request.
  channel2 = append_reply_remove_request_channel serviced_request channel1
  ==>
  PENDING_ACCESSES_UNEXPANDED channel1 channel2
Proof
INTRO_TAC THEN
REWRITE_TAC [access_propertiesTheory.PENDING_ACCESSES_UNEXPANDED] THEN
REWRITE_TAC [access_propertiesTheory.PENDING_ACCESSES_UNEXPANDED_FETCHING_BD] THEN
REWRITE_TAC [access_propertiesTheory.PENDING_ACCESSES_UNEXPANDED_UPDATING_BD] THEN
REWRITE_TAC [access_propertiesTheory.PENDING_ACCESSES_UNEXPANDED_TRANSFERRING_DATA] THEN
REWRITE_TAC [access_propertiesTheory.PENDING_ACCESSES_UNEXPANDED_WRITING_BACK_BD] THEN
ITAC dma_request_served_lemmasTheory.APPEND_REPLY_REMOVE_REQUEST_CHANNEL_NOT_EXPANDING_PENDING_REQUESTS_LEMMA THEN
STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_CHANNEL_IMPLIES_ALL_DMA_CHANNELS_PENDING_ACCESSES_UNEXPANDED_LEMMA:
!channels1 channels2 channel_id1 channel1 channel2 serviced_request.
  channel1 = THE (channels1 channel_id1) /\
  channel2 = append_reply_remove_request_channel serviced_request channel1 /\
  channels2 = (channel_id1 =+ SOME channel2) channels1
  ==>
  !channel_id2.
    PENDING_ACCESSES_UNEXPANDED (THE (channels1 channel_id2)) (THE (channels2 channel_id2))
Proof
INTRO_TAC THEN
GEN_TAC THEN
ITAC APPEND_REPLY_REMOVE_REQUEST_CHANNEL_IMPLIES_PENDING_ACCESSES_UNEXPANDED_LEMMA THEN
ETAC combinTheory.UPDATE_def THEN
ALL_LRTAC THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 ETAC optionTheory.option_CLAUSES THEN STAC
 ,
 REWRITE_TAC [access_properties_lemmasTheory.REFL_PENDING_ACCESSES_UNEXPANDED_LEMMA]
]
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_CHANNELS_INDEX_IMPLIES_PENDING_ACCESSES_UNEXPANDED_IND_LEMMA:
!serviced_request channels1 channel_id.
  (\serviced_request channels1 channel_id.
    !channels2.
      channels2 = append_reply_remove_request_channels_index serviced_request channels1 channel_id
      ==>
      !channel_id. PENDING_ACCESSES_UNEXPANDED (THE (channels1 channel_id)) (THE (channels2 channel_id))) serviced_request channels1 channel_id
Proof
MATCH_MP_TAC append_reply_remove_request_channels_index_ind THEN
APP_SCALAR_TAC THEN
REPEAT CONJ_TAC THEN (
 REPEAT GEN_TAC THEN
 INTRO_TAC THEN
 INTRO_TAC THEN
 PTAC append_reply_remove_request_channels_index THENL
 [
  RLTAC THEN
  LRTAC THEN
  IRTAC APPEND_REPLY_REMOVE_REQUEST_CHANNEL_IMPLIES_ALL_DMA_CHANNELS_PENDING_ACCESSES_UNEXPANDED_LEMMA THEN
  STAC
  ,
  AITAC THEN
  AITAC THEN
  IRTAC APPEND_REPLY_REMOVE_REQUEST_CHANNEL_IMPLIES_ALL_DMA_CHANNELS_PENDING_ACCESSES_UNEXPANDED_LEMMA THEN
  GEN_TAC THEN
  IRTAC access_properties_lemmasTheory.PENDING_ACCESSES_UNEXPANDED_TRANSITIVITY_LEMMA THEN
  STAC
 ])
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_CHANNELS_INDEX_IMPLIES_PENDING_ACCESSES_UNEXPANDED_LEMMA:
!channel_id channels1 channels2 serviced_request.
  channels2 = append_reply_remove_request_channels_index serviced_request channels1 channel_id
  ==>
  !channel_id. PENDING_ACCESSES_UNEXPANDED (THE (channels1 channel_id)) (THE (channels2 channel_id))
Proof
REWRITE_TAC [BETA_RULE APPEND_REPLY_REMOVE_REQUEST_CHANNELS_INDEX_IMPLIES_PENDING_ACCESSES_UNEXPANDED_IND_LEMMA]
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_CHANNELS_INDEX_IMPLIES_PENDING_ACCESSES_UNEXPANDED_LEMMA:
!channels1 channels2 some_max_index serviced_request.
  channels2 = append_reply_remove_request_channels channels1 some_max_index serviced_request
  ==>
  !channel_id. PENDING_ACCESSES_UNEXPANDED (THE (channels1 channel_id)) (THE (channels2 channel_id))
Proof
INTRO_TAC THEN
PTAC append_reply_remove_request_channels THEN
IRTAC APPEND_REPLY_REMOVE_REQUEST_CHANNELS_INDEX_IMPLIES_PENDING_ACCESSES_UNEXPANDED_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_IMPLIES_ALL_DMA_CHANNELS_PENDING_ACCESSES_UNEXPANDED_LEMMA:
!device_characteristics device1 device2 reply.
  device2 = dma_request_served device_characteristics device1 reply
  ==>
  !channel_id.
    PENDING_ACCESSES_UNEXPANDED (schannel device1 channel_id) (schannel device2 channel_id)
Proof
INTRO_TAC THEN
PTAC dma_request_served THEN
REWRITE_TAC [stateTheory.schannel] THEN
FIRTAC APPEND_REPLY_REMOVE_REQUEST_CHANNELS_INDEX_IMPLIES_PENDING_ACCESSES_UNEXPANDED_LEMMA THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_IMPLIES_ALL_DMA_CHANNELS_PENDING_ACCESSES_RESTRICTED_LEMMA:
!device_characteristics device1 device2 reply.
  device2 = dma_request_served device_characteristics device1 reply
  ==>
  !R W memory channel_id.
    PENDING_ACCESSES_RESTRICTED R W memory (schannel device1 channel_id) (schannel device2 channel_id)
Proof
INTRO_TAC THEN
REPEAT GEN_TAC THEN
ITAC DMA_REQUEST_SERVED_IMPLIES_ALL_DMA_CHANNELS_PENDING_ACCESSES_UNEXPANDED_LEMMA THEN
ITAC access_properties_lemmasTheory.PENDING_ACCESSES_UNEXPANDED_IMPLIES_RESTRICTED_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_PRESERVES_REGISTER_REQUESTING_READ_ADDRESSES_LEMMA:
!device_characteristics memory device1 device2 reply.
  device2 = dma_request_served device_characteristics device1 reply /\
  REGISTER_REQUESTING_READ_ADDRESSES device_characteristics memory device1
  ==>
  REGISTER_REQUESTING_READ_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ITAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_NOT_EXPANDING_PENDING_REQUESTS_LEMMA THEN
ITAC read_properties_lemmasTheory.PENDING_REGISTER_RELATED_MEMORY_REQUESTS_UNEXPANDED_PRESERVES_REGISTER_REQUESTING_READ_ADDRESSES_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA:
!device_characteristics memory device1 device2 reply.
  device2 = dma_request_served device_characteristics device1 reply /\
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device1
  ==>
  REGISTER_REQUESTING_WRITE_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ITAC dma_request_served_lemmasTheory.DMA_REQUEST_SERVED_NOT_EXPANDING_PENDING_REQUESTS_LEMMA THEN
ITAC write_properties_lemmasTheory.PENDING_REGISTER_RELATED_MEMORY_REQUESTS_UNEXPANDED_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_PRESERVES_DEVICE_REQUESTING_READ_ADDRESSES_LEMMA:
!memory device_characteristics device1 device2 reply.
  device2 = dma_request_served device_characteristics device1 reply /\
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
 IRTAC DMA_REQUEST_SERVED_IMPLIES_ALL_DMA_CHANNELS_PENDING_ACCESSES_RESTRICTED_LEMMA THEN
 ITAC read_properties_lemmasTheory.PENDING_ACCESSES_RESTRICTED_PRESERVES_CHANNEL_R_LEMMA THEN
 STAC
 ,
 ITAC DMA_REQUEST_SERVED_PRESERVES_REGISTER_REQUESTING_READ_ADDRESSES_LEMMA THEN STAC
]
QED

Theorem DMA_REQUEST_SERVED_PRESERVES_DEVICE_REQUESTING_WRITE_ADDRESSES_LEMMA:
!memory device_characteristics device1 device2 reply.
  device2 = dma_request_served device_characteristics device1 reply /\
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
 IRTAC DMA_REQUEST_SERVED_IMPLIES_ALL_DMA_CHANNELS_PENDING_ACCESSES_RESTRICTED_LEMMA THEN
 ITAC write_properties_lemmasTheory.PENDING_ACCESSES_RESTRICTED_PRESERVES_CHANNEL_W_LEMMA THEN
 STAC
 ,
 ITAC DMA_REQUEST_SERVED_PRESERVES_REGISTER_REQUESTING_WRITE_ADDRESSES_LEMMA THEN STAC
]
QED

Theorem DMA_REQUEST_SERVED_PRESERVES_DEVICE_REQUESTING_READ_WRITE_ADDRESSES_LEMMA:
!memory device_characteristics device1 device2 reply.
  device2 = dma_request_served device_characteristics device1 reply /\
  DEVICE_REQUESTING_READ_ADDRESSES device_characteristics memory device1 /\
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device1
  ==>
  DEVICE_REQUESTING_READ_ADDRESSES device_characteristics memory device2 /\
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ITAC DMA_REQUEST_SERVED_PRESERVES_DEVICE_REQUESTING_READ_ADDRESSES_LEMMA THEN
ITAC DMA_REQUEST_SERVED_PRESERVES_DEVICE_REQUESTING_WRITE_ADDRESSES_LEMMA THEN
STAC
QED

val _ = export_theory();

