open HolKernel Parse boolLib bossLib helper_tactics;
open l3Theory l4Theory invariant_l4Theory proof_obligationsTheory;

val _ = new_theory "writing_back_bd_l3_eq_l4";

Theorem NOT_CONSISTENT_BD_WRITE_IMPLIES_NOT_DISJOINT_BDS_TO_FETCH_AND_WRITE_BACK_ADDRESSES_LEMMA:
!device_characteristics memory internal_state write_addresses.
  ~CONSISTENT_BD_WRITE device_characteristics memory internal_state write_addresses
  ==>
  ?bds_to_fetch channel_id bd bd_ras bd_was uflag.
    VALID_CHANNEL_ID device_characteristics channel_id /\
    bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state /\
    MEM ((bd, bd_ras, bd_was), uflag) bds_to_fetch /\
    ~DISJOINT_LISTS bd_ras write_addresses
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.CONSISTENT_BD_WRITE THEN
ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
NEG_FORALL_TAC THEN
ETAC boolTheory.NOT_IMP THEN
PAXTAC THEN
STAC
QED

Theorem WRITE_ADDRESSES_NOT_DISJOINT_IMPLIES_WRITE_BACK_ADDRESS_OF_BD_TO_WRITE_BACK_AND_IN_NOT_DISJOINT_ADDRESSES_LEMMA:
!write_addresses device_characteristics channel_id environment internal_state bds_to_write_back bd_ras.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  PROOF_OBLIGATION_DECLARED_WRITE_BACK_WRITES_BD_WAS device_characteristics /\
  write_addresses = (cverification device_characteristics channel_id).write_back_bd_addresses environment internal_state bds_to_write_back /\
  ~DISJOINT_LISTS bd_ras write_addresses
  ==>
  ?write_address bd ras bd_was.
    MEM (bd, ras, bd_was) bds_to_write_back /\
    MEM write_address bd_was /\
    MEM write_address bd_ras /\
    MEM write_address write_addresses
Proof
INTRO_TAC THEN
IRTAC lists_lemmasTheory.NOT_DISJOINT_LISTS_IMPLIES_EXISTS_MUTUAL_MEM_LEMMA THEN
AXTAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_DECLARED_WRITE_BACK_WRITES_BD_WAS THEN
AITAC THEN
AXTAC THEN
PAXTAC THEN
STAC
QED

Theorem BDS_TO_FETCH2_EQ_IMPLIES_BDS_TO_FETCH1_EQ_LEMMA:
!device_characteristics channel_id memory device internal_state bds_to_fetch.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BDS_TO_FETCH_EQ device_characteristics memory device.dma_state.internal_state internal_state /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state
  ==>
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory device.dma_state.internal_state
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_FETCH_EQ THEN
AIRTAC THEN
STAC
QED

Theorem WRITING_BACK_BD_L4_EQ_L3_LEMMA:
!device_characteristics channel_id memory device environment internal_state channel.
  PROOF_OBLIGATION_DECLARED_WRITE_BACK_WRITES_BD_WAS device_characteristics /\
  INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 device_characteristics memory device /\
  BDS_TO_FETCH_EQ device_characteristics memory device.dma_state.internal_state internal_state /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channel = schannel device channel_id
  ==>
  writing_back_bd_l4 device_characteristics channel_id        environment internal_state channel =
  writing_back_bd_l3 device_characteristics channel_id memory environment internal_state channel
Proof
INTRO_TAC THEN
PTAC writing_back_bd_l4 THEN PTAC writing_back_bd_l3 THEN TRY STAC THEN
 IRTAC NOT_CONSISTENT_BD_WRITE_IMPLIES_NOT_DISJOINT_BDS_TO_FETCH_AND_WRITE_BACK_ADDRESSES_LEMMA THEN
 AXTAC THEN
 PTAC invariant_l4Theory.INVARIANT_WRITE_BACK_BD_BD_WRITE_L4 THEN
 ETAC invariant_l4Theory.BD_WRITE THEN
 FITAC WRITE_ADDRESSES_NOT_DISJOINT_IMPLIES_WRITE_BACK_ADDRESS_OF_BD_TO_WRITE_BACK_AND_IN_NOT_DISJOINT_ADDRESSES_LEMMA THEN
 AXTAC THEN
 FAITAC THEN
 ETAC bd_queuesTheory.CONSISTENT_BD_WRITE THEN
 ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
 ITAC BDS_TO_FETCH2_EQ_IMPLIES_BDS_TO_FETCH1_EQ_LEMMA THEN
 AITAC THEN
 FIRTAC lists_lemmasTheory.MEM_DISJOINT_LISTS_IMPLIES_F_LEMMA THEN
 SOLVE_F_ASM_TAC
QED

val _ = export_theory();

