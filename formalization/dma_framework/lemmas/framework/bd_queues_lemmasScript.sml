open HolKernel Parse boolLib bossLib helper_tactics;
open bd_queuesTheory;

val _ = new_theory "bd_queues_lemmas";

Theorem LIST1_IN_LIST2_PRESERVES_DISJOINT_FROM_UNRELATED_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id memory internal_state bd_ras bd_was bd_write_addresses.
  LIST1_IN_LIST2 bd_write_addresses bd_was /\
  DISJOINT_FROM_UNRELATED_BDS_TO_FETCH device_characteristics channel_id memory internal_state bd_ras bd_was
  ==>
  DISJOINT_FROM_UNRELATED_BDS_TO_FETCH device_characteristics channel_id memory internal_state bd_ras bd_write_addresses
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.DISJOINT_FROM_UNRELATED_BDS_TO_FETCH THEN
INTRO_TAC THEN
AIRTAC THEN
IRTAC lists_lemmasTheory.LIST1_IN_LIST2_PRESERVES_DISJOINTNESS_LEMMA THEN
STAC
QED

Theorem BDS_TO_FETCH_EQ_PRESERVES_DISJOINT_FROM_UNRELATED_BDS_TO_FETCH_LEMMA:
!device_characteristics memory internal_state1 internal_state2 bd_ras bd_was channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  BDS_TO_FETCH_EQ device_characteristics memory internal_state1 internal_state2 /\
  DISJOINT_FROM_UNRELATED_BDS_TO_FETCH device_characteristics channel_id memory internal_state1 bd_ras bd_was
  ==>
  DISJOINT_FROM_UNRELATED_BDS_TO_FETCH device_characteristics channel_id memory internal_state2 bd_ras bd_was
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.DISJOINT_FROM_UNRELATED_BDS_TO_FETCH THEN
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_FETCH_EQ THEN
AIRTAC THEN
LRTAC THEN
AIRTAC THEN
STAC
QED

Theorem LIST1_IN_LIST2_PRESERVES_DISJOINT_FROM_OTHER_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id memory internal_state bd_was bd_write_addresses.
  LIST1_IN_LIST2 bd_write_addresses bd_was /\
  DISJOINT_FROM_OTHER_BDS_TO_FETCH device_characteristics channel_id memory internal_state bd_was
  ==>
  DISJOINT_FROM_OTHER_BDS_TO_FETCH device_characteristics channel_id memory internal_state bd_write_addresses
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.DISJOINT_FROM_OTHER_BDS_TO_FETCH THEN
INTRO_TAC THEN
AIRTAC THEN
IRTAC lists_lemmasTheory.LIST1_IN_LIST2_PRESERVES_DISJOINTNESS_LEMMA THEN
STAC
QED

Theorem BDS_TO_FETCH_EQ_PRESERVES_DISJOINT_FROM_OTHER_BDS_TO_FETCH_LEMMA:
!device_characteristics memory internal_state1 internal_state2 bd_was channel_id.
  BDS_TO_FETCH_EQ device_characteristics memory internal_state1 internal_state2 /\
  DISJOINT_FROM_OTHER_BDS_TO_FETCH device_characteristics channel_id memory internal_state1 bd_was
  ==>
  DISJOINT_FROM_OTHER_BDS_TO_FETCH device_characteristics channel_id memory internal_state2 bd_was
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.DISJOINT_FROM_OTHER_BDS_TO_FETCH THEN
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_FETCH_EQ THEN
LRTAC THEN
AITAC THEN
AIRTAC THEN
STAC
QED

Theorem LIST1_IN_LIST2_PRESERVES_CONSISTENT_BD_WRITE_LEMMA:
!device_characteristics memory internal_state bd_was bd_write_addresses.
  LIST1_IN_LIST2 bd_write_addresses bd_was /\
  CONSISTENT_BD_WRITE device_characteristics memory internal_state bd_was
  ==>
  CONSISTENT_BD_WRITE device_characteristics memory internal_state bd_write_addresses
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.CONSISTENT_BD_WRITE THEN
ETAC WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
INTRO_TAC THEN
AIRTAC THEN
LEMMA_ASM_TAC lists_lemmasTheory.DISJOINT_LISTS_SYM_LEMMA THEN
IRTAC lists_lemmasTheory.LIST1_IN_LIST2_PRESERVES_DISJOINTNESS2_LEMMA THEN
ASM_REWRITE_TAC [lists_lemmasTheory.DISJOINT_LISTS_SYM_LEMMA]
QED

Theorem BDS_TO_FETCH_EQ_PRESERVES_CONSISTENT_BD_WRITE_LEMMA:
!device_characteristics memory internal_state1 internal_state2 bd_was.
  BDS_TO_FETCH_EQ device_characteristics memory internal_state1 internal_state2 /\
  CONSISTENT_BD_WRITE device_characteristics memory internal_state1 bd_was
  ==>
  CONSISTENT_BD_WRITE device_characteristics memory internal_state2 bd_was
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.CONSISTENT_BD_WRITE THEN
ETAC WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_FETCH_EQ THEN
AITAC THEN
AIRTAC THEN
STAC
QED

Theorem BDS_TO_FETCH_EQ_PRESERVES_WRITE_ADDRESS_NOT_BD_TO_FETCH_LEMMA:
!device_characteristics memory internal_state1 internal_state2 was.
  BDS_TO_FETCH_EQ device_characteristics memory internal_state1 internal_state2 /\
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory internal_state1 was
  ==>
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory internal_state2 was
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_FETCH_EQ THEN
AITAC THEN
LRTAC THEN
AIRTAC THEN
STAC
QED

Theorem SCRATCHPAD_ADDRESSES_EQ_PRESERVES_WRITE_ADDRESS_NOT_SCRATCHPAD_LEMMA:
!device_characteristics internal_state1 internal_state2 was.
  SCRATCHPAD_ADDRESSES_EQ device_characteristics internal_state1 internal_state2 /\
  WRITE_ADDRESS_NOT_SCRATCHPAD device_characteristics internal_state1 was
  ==>
  WRITE_ADDRESS_NOT_SCRATCHPAD device_characteristics internal_state2 was
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_SCRATCHPAD THEN
ETAC stateTheory.SCRATCHPAD_ADDRESSES_EQ THEN
LRTAC THEN
STAC
QED

Theorem BDS_TO_FETCH_EQ_PRESERVE_CONSISTENT_DMA_WRITE_LEMMA:
!device_characteristics memory internal_state1 internal_state2 was.
  BDS_TO_FETCH_EQ device_characteristics memory internal_state1 internal_state2 /\
  CONSISTENT_DMA_WRITE device_characteristics memory internal_state1 was
  ==>
  CONSISTENT_DMA_WRITE device_characteristics memory internal_state2 was
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.CONSISTENT_DMA_WRITE THEN
INTRO_TAC THEN
AIRTAC THEN
MATCH_MP_TAC BDS_TO_FETCH_EQ_PRESERVES_WRITE_ADDRESS_NOT_BD_TO_FETCH_LEMMA THEN PAXTAC THEN STAC
QED

Theorem LIST1_IN_LIST2_PRESERVES_WRITE_ADDRESS_NOT_BD_TO_FETCH_LEMMA:
!device_characteristics memory internal_state was1 was2.
  LIST1_IN_LIST2 was1 was2 /\
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory internal_state was2
  ==>
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory internal_state was1
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
INTRO_TAC THEN
AIRTAC THEN
IRTAC lists_lemmasTheory.LIST1_IN_LIST2_PRESERVES_DISJOINTNESS_LEMMA THEN
STAC
QED

Theorem LIST1_IN_LIST2_PRESERVES_WRITE_ADDRESS_NOT_SCRATCHPAD_LEMMA:
!device_characteristics internal_state was1 was2.
  LIST1_IN_LIST2 was1 was2 /\
  WRITE_ADDRESS_NOT_SCRATCHPAD device_characteristics internal_state was2
  ==>
  WRITE_ADDRESS_NOT_SCRATCHPAD device_characteristics internal_state was1
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_SCRATCHPAD THEN
INTRO_TAC THEN
AIRTAC THEN
FIRTAC lists_lemmasTheory.LIST1_IN_LIST2_PRESERVES_DISJOINTNESS_LEMMA THEN
STAC
QED

Theorem LIST1_IN_LIST2_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA:
!device_characteristics memory internal_state was1 was2.
  LIST1_IN_LIST2 was1 was2 /\
  CONSISTENT_DMA_WRITE device_characteristics memory internal_state was2
  ==>
  CONSISTENT_DMA_WRITE device_characteristics memory internal_state was1
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.CONSISTENT_DMA_WRITE THEN
INTRO_TAC THEN
AITAC THEN
MATCH_MP_TAC LIST1_IN_LIST2_PRESERVES_WRITE_ADDRESS_NOT_BD_TO_FETCH_LEMMA THEN PAXTAC THEN STAC
QED

Theorem CONSISTENT_DMA_WRITE_EMPTY_WRITE_ADDRESSES_LEMMA:
!device_characteristics memory internal_state.
  CONSISTENT_DMA_WRITE device_characteristics memory internal_state []
Proof
REPEAT GEN_TAC THEN
REWRITE_TAC [bd_queuesTheory.CONSISTENT_DMA_WRITE] THEN
REWRITE_TAC [bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH, bd_queuesTheory.WRITE_ADDRESS_NOT_SCRATCHPAD] THEN
REWRITE_TAC [lists_lemmasTheory.DISJOINT_LISTS_EMPTY_LEMMA]
QED

Theorem BD_READ_ADDRESSES_EMPTY_LEMMA:
!bds_to_fetch. bd_read_addresses bds_to_fetch [] = []
Proof
GEN_TAC THEN PTAC bd_queuesTheory.bd_read_addresses THEN TRY STAC THEN ETAC listTheory.FILTER THEN STAC
QED

val _ = export_theory();

