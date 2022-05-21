open HolKernel Parse boolLib bossLib helper_tactics;
open l1Theory access_propertiesTheory;

val _ = new_theory "l1_transferring_data_lemmas";

Theorem TRANSFERRING_DATA_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = transferring_data_l1 device_characteristics channel_id memory internal_state1 channel1
  ==>
  PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA device_characteristics.dma_characteristics.R device_characteristics.dma_characteristics.W memory channel1 channel2
Proof
INTRO_TAC THEN
PTAC transferring_data_l1 THENL
[
 IF_SPLIT_TAC THENL
 [
  ITAC transferring_data_properties_lemmasTheory.TRANSFERRING_DATA_REPLIES_UPDATE_QS_IMPLIES_PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA_LEMMA THEN
  EQ_PAIR_ASM_TAC THEN
  ITAC transferring_data_properties_lemmasTheory.TRANSFERRING_DATA_APPEND_REQUESTS_R_W_IMPLIES_PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA_LEMMA THEN
  FIRTAC access_properties_lemmasTheory.PENDING_ACCESSES_RESTRICTED_ACCESSES_TRANSFERRING_DATA_TRANSITIVITY_LEMMA THEN
  STAC
  ,
  EQ_PAIR_ASM_TAC THEN
  RLTAC THEN
  ITAC transferring_data_properties_lemmasTheory.TRANSFERRING_DATA_REPLIES_REQUESTS_IMPLIES_PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA_LEMMA THEN
  ITAC transferring_data_properties_lemmasTheory.TRANSFERRING_DATA_APPEND_REQUESTS_R_W_IMPLIES_PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA_LEMMA THEN
  FIRTAC access_properties_lemmasTheory.PENDING_ACCESSES_RESTRICTED_ACCESSES_TRANSFERRING_DATA_TRANSITIVITY_LEMMA THEN
  STAC
 ]
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 RLTAC THEN
 IF_SPLIT_TAC THENL
 [
  ITAC transferring_data_properties_lemmasTheory.TRANSFERRING_DATA_REPLIES_UPDATE_QS_IMPLIES_PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA_LEMMA THEN
  STAC
  ,
  ITAC transferring_data_properties_lemmasTheory.TRANSFERRING_DATA_REPLIES_REQUESTS_IMPLIES_PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA_LEMMA THEN
  STAC
 ]
 ,
 EQ_PAIR_ASM_TAC THEN
 IF_SPLIT_TAC THENL
 [
  ITAC transferring_data_properties_lemmasTheory.TRANSFERRING_DATA_REPLIES_UPDATE_QS_IMPLIES_PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA_LEMMA THEN
  STAC
  ,
  ITAC transferring_data_properties_lemmasTheory.TRANSFERRING_DATA_REPLIES_REQUESTS_IMPLIES_PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA_LEMMA THEN
  STAC
 ]
 ,
 EQ_PAIR_ASM_TAC THEN
 PTAC PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA THEN
 PTAC PENDING_ACCESSES_UNMODIFIED_TRANSFERRING_DATA THEN
 STAC
]
QED

Theorem TRANSFERRING_DATA_L1_PRESERVES_OTHERS_PENDING_REQUESTS_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = transferring_data_l1 device_characteristics channel_id memory internal_state1 channel1
  ==>
  channel1.pending_accesses.requests.fetching_bd = channel2.pending_accesses.requests.fetching_bd /\
  channel1.pending_accesses.requests.updating_bd = channel2.pending_accesses.requests.updating_bd /\
  channel1.pending_accesses.requests.writing_back_bd = channel2.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC transferring_data_l1 THENL
[
 EQ_PAIR_ASM_TAC THEN
 IF_SPLIT_TAC THENL
 [
  ITAC transferring_data_suboperations_lemmasTheory.TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_FETCHING_UPDATING_WRITING_BACK_BD_LEMMA THEN
  ITAC transferring_data_suboperations_lemmasTheory.TRANSFERRING_DATA_UPDATE_QS_PRESERVES_FETCHING_UPDATING_WRITING_BACK_BD_LEMMA THEN
  ITAC transferring_data_suboperations_lemmasTheory.TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_FETCHING_UPDATING_WRITING_BACK_BD_LEMMA THEN
  STAC
  ,
  ITAC transferring_data_suboperations_lemmasTheory.TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_FETCHING_UPDATING_WRITING_BACK_BD_LEMMA THEN
  ITAC transferring_data_suboperations_lemmasTheory.TRANSFERRING_DATA_APPEND_REQUESTS_PRESERVES_FETCHING_UPDATING_WRITING_BACK_BD_LEMMA THEN
  STAC
 ]
 ,
 EQ_PAIR_ASM_TAC THEN
 IF_SPLIT_TAC THENL
 [
  ITAC transferring_data_suboperations_lemmasTheory.TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_FETCHING_UPDATING_WRITING_BACK_BD_LEMMA THEN
  ITAC transferring_data_suboperations_lemmasTheory.TRANSFERRING_DATA_UPDATE_QS_PRESERVES_FETCHING_UPDATING_WRITING_BACK_BD_LEMMA THEN
  REPEAT RLTAC THEN
  STAC
  ,
  ITAC transferring_data_suboperations_lemmasTheory.TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_FETCHING_UPDATING_WRITING_BACK_BD_LEMMA THEN
  STAC
 ]
 ,
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN RLTAC THEN
 IF_SPLIT_TAC THENL
 [
  IRTAC transferring_data_suboperations_lemmasTheory.TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_FETCHING_UPDATING_WRITING_BACK_BD_LEMMA THEN
  IRTAC transferring_data_suboperations_lemmasTheory.TRANSFERRING_DATA_UPDATE_QS_PRESERVES_FETCHING_UPDATING_WRITING_BACK_BD_LEMMA THEN
  STAC
  ,
  IRTAC transferring_data_suboperations_lemmasTheory.TRANSFERRING_DATA_REPLIES_REQUESTS_PRESERVES_FETCHING_UPDATING_WRITING_BACK_BD_LEMMA THEN
  STAC
 ]
 ,
 EQ_PAIR_ASM_TAC THEN
 STAC
]
QED

Theorem TRANSFERRING_DATA_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_OTHERS_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = transferring_data_l1 device_characteristics channel_id memory internal_state1 channel1
  ==>
  PENDING_ACCESSES_RESTRICTED_FETCHING_BD device_characteristics.dma_characteristics.R device_characteristics.dma_characteristics.W memory channel1 channel2 /\
  PENDING_ACCESSES_RESTRICTED_UPDATING_BD device_characteristics.dma_characteristics.R device_characteristics.dma_characteristics.W memory channel1 channel2 /\
  PENDING_ACCESSES_RESTRICTED_WRITING_BACK_BD device_characteristics.dma_characteristics.R device_characteristics.dma_characteristics.W memory channel1 channel2
Proof
INTRO_TAC THEN
ITAC TRANSFERRING_DATA_L1_PRESERVES_OTHERS_PENDING_REQUESTS_LEMMA THEN
ITAC access_properties_lemmasTheory.EQ_REQUESTS_IMPLIES_PENDING_ACCESSES_RESTRICTED_FETCHING_BD_LEMMA THEN
ITAC access_properties_lemmasTheory.EQ_REQUESTS_IMPLIES_PENDING_ACCESSES_RESTRICTED_UPDATING_BD_LEMMA THEN
ITAC access_properties_lemmasTheory.EQ_REQUESTS_IMPLIES_PENDING_ACCESSES_RESTRICTED_WRITING_BACK_BD_LEMMA THEN
STAC
QED

Theorem TRANSFERRING_DATA_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = transferring_data_l1 device_characteristics channel_id memory internal_state1 channel1
  ==>
  PENDING_ACCESSES_RESTRICTED device_characteristics.dma_characteristics.R device_characteristics.dma_characteristics.W memory channel1 channel2
Proof
INTRO_TAC THEN
ETAC PENDING_ACCESSES_RESTRICTED THEN
ITAC TRANSFERRING_DATA_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA_LEMMA THEN
ITAC TRANSFERRING_DATA_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_OTHERS_LEMMA THEN
STAC
QED

Theorem TRANSFERRING_DATA_L1_PRESERVES_CHANNEL_REQUESTING_ACCESSES_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = transferring_data_l1 device_characteristics channel_id memory internal_state1 channel1 /\
  CHANNEL_REQUESTING_READ_ADDRESSES device_characteristics.dma_characteristics.R memory channel1 /\
  CHANNEL_REQUESTING_WRITE_ADDRESSES device_characteristics.dma_characteristics.W memory channel1
  ==>
  CHANNEL_REQUESTING_READ_ADDRESSES device_characteristics.dma_characteristics.R memory channel2 /\
  CHANNEL_REQUESTING_WRITE_ADDRESSES device_characteristics.dma_characteristics.W memory channel2
Proof
INTRO_TAC THEN
ITAC TRANSFERRING_DATA_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_LEMMA THEN
ITAC read_properties_lemmasTheory.PENDING_ACCESSES_RESTRICTED_PRESERVES_CHANNEL_R_LEMMA THEN
ITAC write_properties_lemmasTheory.PENDING_ACCESSES_RESTRICTED_PRESERVES_CHANNEL_W_LEMMA THEN
STAC
QED

val _ = export_theory();
