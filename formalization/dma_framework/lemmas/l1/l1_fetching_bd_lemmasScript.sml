open HolKernel Parse boolLib bossLib helper_tactics;
open l1Theory;
open access_propertiesTheory;

val _ = new_theory "l1_fetching_bd_lemmas";

Theorem FETCHING_BD_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_FETCHING_BD_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = fetching_bd_l1 device_characteristics channel_id memory internal_state1 channel1
  ==>
  !W. PENDING_ACCESSES_RESTRICTED_FETCHING_BD device_characteristics.dma_characteristics.R W memory channel1 channel2
Proof
INTRO_TAC THEN
GEN_TAC THEN
ETAC PENDING_ACCESSES_RESTRICTED_FETCHING_BD THEN
PTAC fetching_bd_l1 THENL
[
 ITAC fetching_bd_properties_lemmasTheory.FETCHING_BD_FETCH_BD_ABSTRACT_IMPLIES_PENDING_ACCESSES_UNMODIFIED_FETCHING_BD_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ITAC fetching_bd_properties_lemmasTheory.FETCHING_BD_SET_REQUEST_R_IMPLIES_PENDING_ACCESSES_UNMODIFIED_UNEXPANDED_CONDITIONALLY_EXPANDED_FETCHING_BD_LEMMA THEN
 SPLIT_ASM_DISJS_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ETAC PENDING_ACCESSES_UNMODIFIED_FETCHING_BD THEN
 STAC
 ,
 ITAC fetching_bd_properties_lemmasTheory.FETCHING_BD_CLEAR_REPLY_IMP_PENDING_ACCESSES_UNEXPANDED_FETCHING_BD_LEMMA THEN
 ITAC fetching_bd_properties_lemmasTheory.FETCHING_BD_FETCH_BD_ABSTRACT_IMPLIES_PENDING_ACCESSES_UNMODIFIED_FETCHING_BD_LEMMA THEN
 ITAC access_properties_fetching_bd_lemmasTheory.PENDING_ACCESSES_UNEXPANDED_UNMODIFIED_FETCHING_BD_IMPLIES_PENDING_ACCESSES_UNEXPANDED_FETCHING_BD_LEMMA THEN
 STAC
]
QED

Theorem FETCHING_BD_L1_PRESERVES_OTHERS_PENDING_REQUESTS_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = fetching_bd_l1 device_characteristics channel_id memory internal_state1 channel1
  ==>
  channel2.pending_accesses.requests.updating_bd = channel1.pending_accesses.requests.updating_bd /\
  channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC fetching_bd_l1 THENL
[
 ITAC abstract_lemmasTheory.FETCHING_BD_FETCH_BD_ABSTRACT_PRESERVES_PENDING_ACCESSES_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ITAC fetching_bd_suboperations_lemmasTheory.FETCHING_BD_SET_REQUEST_PRESERVES_REQEUSTS_OR_SETS_FETCHING_BD_REQUEST_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 STAC
 ,
 ITAC fetching_bd_suboperations_lemmasTheory.FETCHING_BD_CLEAR_REPLY_PRESERVES_PENDING_REQUESTS_LEMMA THEN
 ITAC abstract_lemmasTheory.FETCHING_BD_FETCH_BD_ABSTRACT_PRESERVES_PENDING_ACCESSES_LEMMA THEN
 RLTAC THEN
 STAC
]
QED

Theorem FETCHING_BD_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_UPDATING_BD_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = fetching_bd_l1 device_characteristics channel_id memory internal_state1 channel1
  ==>
  !W. PENDING_ACCESSES_RESTRICTED_UPDATING_BD device_characteristics.dma_characteristics.R W memory channel1 channel2
Proof
INTRO_TAC THEN
GEN_TAC THEN
ETAC PENDING_ACCESSES_RESTRICTED_UPDATING_BD THEN
ITAC FETCHING_BD_L1_PRESERVES_OTHERS_PENDING_REQUESTS_LEMMA THEN
ETAC PENDING_ACCESSES_UNMODIFIED_UPDATING_BD THEN
STAC
QED

Theorem FETCHING_BD_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = fetching_bd_l1 device_characteristics channel_id memory internal_state1 channel1
  ==>
  !W. PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA device_characteristics.dma_characteristics.R W memory channel1 channel2
Proof
INTRO_TAC THEN
GEN_TAC THEN
ETAC PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA THEN
ITAC FETCHING_BD_L1_PRESERVES_OTHERS_PENDING_REQUESTS_LEMMA THEN
ETAC PENDING_ACCESSES_UNMODIFIED_TRANSFERRING_DATA THEN
STAC
QED

Theorem FETCHING_BD_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_WRITING_BACK_BD_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = fetching_bd_l1 device_characteristics channel_id memory internal_state1 channel1
  ==>
  !W. PENDING_ACCESSES_RESTRICTED_WRITING_BACK_BD device_characteristics.dma_characteristics.R W memory channel1 channel2
Proof
INTRO_TAC THEN
GEN_TAC THEN
ETAC PENDING_ACCESSES_RESTRICTED_WRITING_BACK_BD THEN
ITAC FETCHING_BD_L1_PRESERVES_OTHERS_PENDING_REQUESTS_LEMMA THEN
ETAC PENDING_ACCESSES_UNMODIFIED_WRITING_BACK_BD THEN
STAC
QED

Theorem FETCHING_BD_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = fetching_bd_l1 device_characteristics channel_id memory internal_state1 channel1
  ==>
  !W. PENDING_ACCESSES_RESTRICTED device_characteristics.dma_characteristics.R W memory channel1 channel2
Proof
INTRO_TAC THEN
GEN_TAC THEN
REWRITE_TAC [PENDING_ACCESSES_RESTRICTED] THEN
ITAC FETCHING_BD_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_FETCHING_BD_LEMMA THEN
ITAC FETCHING_BD_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_UPDATING_BD_LEMMA THEN
ITAC FETCHING_BD_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA_LEMMA THEN
ITAC FETCHING_BD_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_WRITING_BACK_BD_LEMMA THEN
STAC
QED

Theorem FETCHING_BD_L1_PRESERVES_CHANNEL_REQUESTING_ACCESSES_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2 W.
  (internal_state2, channel2) = fetching_bd_l1 device_characteristics channel_id memory internal_state1 channel1 /\
  CHANNEL_REQUESTING_READ_ADDRESSES device_characteristics.dma_characteristics.R memory channel1 /\
  CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel1
  ==>
  CHANNEL_REQUESTING_READ_ADDRESSES device_characteristics.dma_characteristics.R memory channel2 /\
  CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel2
Proof
INTRO_TAC THEN
ITAC FETCHING_BD_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_LEMMA THEN
ITAC read_properties_lemmasTheory.PENDING_ACCESSES_RESTRICTED_PRESERVES_CHANNEL_R_LEMMA THEN
ITAC write_properties_lemmasTheory.PENDING_ACCESSES_RESTRICTED_PRESERVES_CHANNEL_W_LEMMA THEN
STAC
QED

val _ = export_theory();

