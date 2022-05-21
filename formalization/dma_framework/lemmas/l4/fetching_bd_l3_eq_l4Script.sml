open HolKernel Parse boolLib bossLib helper_tactics;
open l3Theory l4Theory proof_obligationsTheory;

val _ = new_theory "fetching_bd_l3_eq_l4";

Theorem BD_READ_ADDRESSES_EQ_LEMMA:
!device_characteristics channel_id internal_state addresses tag bds_to_fetch memory fetch_bd_read_addresses.
  PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ device_characteristics /\
  PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (addresses, tag) = (coperation device_characteristics channel_id).fetch_bd_addresses internal_state /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state /\
  fetch_bd_read_addresses = bd_read_addresses bds_to_fetch addresses
  ==>
  fetch_bd_read_addresses = addresses
Proof
INTRO_TAC THEN
PTAC bd_queuesTheory.bd_read_addresses THENL
[
 PTAC PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ THEN
 AIRTAC THEN
 STAC
 ,
 ALL_LRTAC THEN
 PTAC PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS THEN
 AIRTAC THEN
 ETAC listsTheory.LIST1_IN_LIST2 THEN
 ETAC listTheory.FILTER_EQ_ID THEN
 STAC
]
QED

Theorem FETCHING_BD_L4_EQ_L3_LEMMA:
!device_characteristics channel_id memory internal_state channel.
  PROOF_OBLIGATION_NO_BD_ADDRESSES_TO_READ device_characteristics /\
  PROOF_OBLIGATION_FETCH_BD_ADDRESSES_IN_FIRST_BD_RAS device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  fetching_bd_l4 device_characteristics channel_id        internal_state channel =
  fetching_bd_l3 device_characteristics channel_id memory internal_state channel
Proof
INTRO_TAC THEN
PTAC fetching_bd_l4 THEN PTAC fetching_bd_l3 THENL
[
 STAC
 ,
 IRTAC BD_READ_ADDRESSES_EQ_LEMMA THEN
 ASM_REWRITE_TAC [pairTheory.PAIR_EQ]
 ,
 STAC
]
QED

val _ = export_theory();

