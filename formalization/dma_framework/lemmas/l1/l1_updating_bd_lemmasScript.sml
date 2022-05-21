open HolKernel Parse boolLib bossLib helper_tactics;
open l1Theory;
open proof_obligationsTheory;
open access_propertiesTheory;

val _ = new_theory "l1_updating_bd_lemmas";

Theorem UPDATING_BD_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_UPDATING_BD_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  PROOF_OBLIGATION_UPDATE_WRITES_DECLARED device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = updating_bd_l1 device_characteristics channel_id memory internal_state1 channel1
  ==>
  !R. PENDING_ACCESSES_RESTRICTED_UPDATING_BD R device_characteristics.dma_characteristics.W memory channel1 channel2
Proof
INTRO_TAC THEN
GEN_TAC THEN
ETAC PENDING_ACCESSES_RESTRICTED_UPDATING_BD THEN
PTAC updating_bd_l1 THENL
[
 EQ_PAIR_ASM_TAC THEN
 ITAC updating_bd_properties_lemmasTheory.UPDATING_BD_UPDATE_QS_IMPLIES_PENDING_ACCESSES_UNMODIFIED_UPDATING_BD_LEMMA THEN
 STAC
 ,
 ETAC PROOF_OBLIGATION_UPDATE_WRITES_DECLARED THEN
 AITAC THEN
 EQ_PAIR_ASM_TAC THEN
 ITAC updating_bd_properties_lemmasTheory.UPDATING_BD_UPDATE_QS_UPDATING_BD_APPEND_REQUEST_W_IMPLIES_PENDING_ACCESSES_CONDITIONALLY_EXPANDED_UPDATING_BD_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ITAC updating_bd_properties_lemmasTheory.UPDATING_BD_UPDATE_QS_IMPLIES_PENDING_ACCESSES_UNMODIFIED_UPDATING_BD_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ETAC PENDING_ACCESSES_UNMODIFIED_UPDATING_BD THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ETAC PENDING_ACCESSES_UNMODIFIED_UPDATING_BD THEN
 STAC
]
QED

Theorem UPDATING_BD_L1_PRESERVES_OTHERS_PENDING_REQUESTS_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = updating_bd_l1 device_characteristics channel_id memory internal_state1 channel1
  ==>
  channel2.pending_accesses.requests.fetching_bd = channel1.pending_accesses.requests.fetching_bd /\
  channel2.pending_accesses.requests.transferring_data = channel1.pending_accesses.requests.transferring_data /\
  channel2.pending_accesses.requests.writing_back_bd = channel1.pending_accesses.requests.writing_back_bd
Proof
INTRO_TAC THEN
PTAC updating_bd_l1 THENL
[
 EQ_PAIR_ASM_TAC THEN
 ITAC updating_bd_suboperations_lemmasTheory.UPDATING_BD_UPDATE_QS_PRESERVES_STATE_LEMMA THEN
 ITAC updating_bd_suboperations_lemmasTheory.UPDATING_BD_APPEND_REQUEST_PRESERVES_OTHERS_REQUESTS_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ITAC updating_bd_suboperations_lemmasTheory.UPDATING_BD_UPDATE_QS_PRESERVES_STATE_LEMMA THEN
 ALL_RLTAC THEN
 ITAC updating_bd_suboperations_lemmasTheory.UPDATING_BD_APPEND_REQUEST_PRESERVES_OTHERS_REQUESTS_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ITAC updating_bd_suboperations_lemmasTheory.UPDATING_BD_UPDATE_QS_PRESERVES_STATE_LEMMA THEN
 ALL_RLTAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 STAC
]
QED

Theorem UPDATING_BD_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_FETCHING_BD_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = updating_bd_l1 device_characteristics channel_id memory internal_state1 channel1
  ==>
  !R. PENDING_ACCESSES_RESTRICTED_FETCHING_BD R device_characteristics.dma_characteristics.W memory channel1 channel2
Proof
INTRO_TAC THEN
GEN_TAC THEN
ETAC PENDING_ACCESSES_RESTRICTED_FETCHING_BD THEN
ITAC UPDATING_BD_L1_PRESERVES_OTHERS_PENDING_REQUESTS_LEMMA THEN
ETAC PENDING_ACCESSES_UNMODIFIED_FETCHING_BD THEN
STAC
QED

Theorem UPDATING_BD_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = updating_bd_l1 device_characteristics channel_id memory internal_state1 channel1
  ==>
  !R. PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA R device_characteristics.dma_characteristics.W memory channel1 channel2
Proof
INTRO_TAC THEN
GEN_TAC THEN
ETAC PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA THEN
ITAC UPDATING_BD_L1_PRESERVES_OTHERS_PENDING_REQUESTS_LEMMA THEN
ETAC PENDING_ACCESSES_UNMODIFIED_TRANSFERRING_DATA THEN
STAC
QED

Theorem UPDATING_BD_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_WRITING_BACK_BD_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  (internal_state2, channel2) = updating_bd_l1 device_characteristics channel_id memory internal_state1 channel1
  ==>
  !R. PENDING_ACCESSES_RESTRICTED_WRITING_BACK_BD R device_characteristics.dma_characteristics.W memory channel1 channel2
Proof
INTRO_TAC THEN
GEN_TAC THEN
ETAC PENDING_ACCESSES_RESTRICTED_WRITING_BACK_BD THEN
ITAC UPDATING_BD_L1_PRESERVES_OTHERS_PENDING_REQUESTS_LEMMA THEN
ETAC PENDING_ACCESSES_UNMODIFIED_WRITING_BACK_BD THEN
STAC
QED

Theorem UPDATING_BD_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state2 channel1 channel2.
  PROOF_OBLIGATION_UPDATE_WRITES_DECLARED device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = updating_bd_l1 device_characteristics channel_id memory internal_state1 channel1
  ==>
  !R. PENDING_ACCESSES_RESTRICTED R device_characteristics.dma_characteristics.W memory channel1 channel2
Proof
INTRO_TAC THEN
GEN_TAC THEN
ETAC PENDING_ACCESSES_RESTRICTED THEN
ITAC UPDATING_BD_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_FETCHING_BD_LEMMA THEN
ITAC UPDATING_BD_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_UPDATING_BD_LEMMA THEN
ITAC UPDATING_BD_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_TRANSFERRING_DATA_LEMMA THEN
ITAC UPDATING_BD_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_WRITING_BACK_BD_LEMMA THEN
STAC
QED

Theorem UPDATING_BD_L1_PRESERVES_CHANNEL_REQUESTING_ACCESSES_LEMMA:
!R memory device_characteristics channel_id internal_state1 internal_state2 channel1 channel2.
  PROOF_OBLIGATION_UPDATE_WRITES_DECLARED device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (internal_state2, channel2) = updating_bd_l1 device_characteristics channel_id memory internal_state1 channel1 /\
  CHANNEL_REQUESTING_READ_ADDRESSES R memory channel1 /\
  CHANNEL_REQUESTING_WRITE_ADDRESSES device_characteristics.dma_characteristics.W memory channel1
  ==>
  CHANNEL_REQUESTING_READ_ADDRESSES R memory channel2 /\
  CHANNEL_REQUESTING_WRITE_ADDRESSES device_characteristics.dma_characteristics.W memory channel2
Proof
INTRO_TAC THEN
ITAC UPDATING_BD_L1_IMPLIES_PENDING_ACCESSES_RESTRICTED_LEMMA THEN
ITAC read_properties_lemmasTheory.PENDING_ACCESSES_RESTRICTED_PRESERVES_CHANNEL_R_LEMMA THEN
ITAC write_properties_lemmasTheory.PENDING_ACCESSES_RESTRICTED_PRESERVES_CHANNEL_W_LEMMA THEN
STAC
QED

val _ = export_theory();

