open HolKernel Parse boolLib bossLib helper_tactics;
open read_propertiesTheory write_propertiesTheory access_propertiesTheory;

val _ = new_theory "access_properties_updating_bd_lemmas";

Theorem UNMODIFIED_UPDATING_BD_PRESERVES_CHANNEL_R_LEMMA:
!R memory channel1 channel2.
  PENDING_ACCESSES_UNMODIFIED_UPDATING_BD channel1 channel2 /\
  UPDATING_BD_CHANNEL_REQUESTING_READ_ADDRESSES R memory channel1
  ==>
  UPDATING_BD_CHANNEL_REQUESTING_READ_ADDRESSES R memory channel2
Proof
INTRO_TAC THEN
PTAC PENDING_ACCESSES_UNMODIFIED_UPDATING_BD THEN
ETAC UPDATING_BD_CHANNEL_REQUESTING_READ_ADDRESSES THEN
STAC
QED

Theorem UNMODIFIED_UPDATING_BD_PRESERVES_CHANNEL_W_LEMMA:
!W memory channel1 channel2.
  PENDING_ACCESSES_UNMODIFIED_UPDATING_BD channel1 channel2 /\
  UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel1
  ==>
  UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel2
Proof
INTRO_TAC THEN
PTAC PENDING_ACCESSES_UNMODIFIED_UPDATING_BD THEN
ETAC UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
STAC
QED



Theorem UNEXPANDED_UPDATING_BD_PRESERVES_CHANNEL_R_LEMMA:
!R memory channel1 channel2.
  PENDING_ACCESSES_UNEXPANDED_UPDATING_BD channel1 channel2 /\
  UPDATING_BD_CHANNEL_REQUESTING_READ_ADDRESSES R memory channel1
  ==>
  UPDATING_BD_CHANNEL_REQUESTING_READ_ADDRESSES R memory channel2
Proof
INTRO_TAC THEN
PTAC PENDING_ACCESSES_UNEXPANDED_UPDATING_BD THEN
ETAC UPDATING_BD_CHANNEL_REQUESTING_READ_ADDRESSES THEN
INTRO_TAC THEN
AITAC THEN
AITAC THEN
STAC
QED

Theorem UNEXPANDED_UPDATING_BD_PRESERVES_CHANNEL_W_LEMMA:
!W memory channel1 channel2.
  PENDING_ACCESSES_UNEXPANDED_UPDATING_BD channel1 channel2 /\
  UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel1
  ==>
  UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel2
Proof
INTRO_TAC THEN
PTAC PENDING_ACCESSES_UNEXPANDED_UPDATING_BD THEN
ETAC UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
INTRO_TAC THEN
AITAC THEN
AITAC THEN
STAC
QED



Theorem CONDITIONALLY_EXPANDED_UPDATING_BD_PRESERVES_CHANNEL_R_LEMMA:
!R W memory channel1 channel2.
  PENDING_ACCESSES_CONDITIONALLY_EXPANDED_UPDATING_BD R W memory channel1 channel2 /\
  UPDATING_BD_CHANNEL_REQUESTING_READ_ADDRESSES R memory channel1
  ==>
  UPDATING_BD_CHANNEL_REQUESTING_READ_ADDRESSES R memory channel2
Proof
INTRO_TAC THEN
RW_HYP_LEMMA_TAC PENDING_ACCESSES_CONDITIONALLY_EXPANDED_UPDATING_BD THEN
ETAC UPDATING_BD_CHANNEL_REQUESTING_READ_ADDRESSES THEN
INTRO_TAC THEN
AITAC THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AITAC THEN
 STAC
 ,
 PTAC REQUEST_CONDITION_R_W THEN
 PTAC REQUEST_CONDITION_R THEN PTAC REQUEST_CONDITION_W THEN
 STAC
]
QED

Theorem CONDITIONALLY_EXPANDED_UPDATING_BD_PRESERVES_CHANNEL_W_LEMMA:
!R W memory channel1 channel2.
  PENDING_ACCESSES_CONDITIONALLY_EXPANDED_UPDATING_BD R W memory channel1 channel2 /\
  UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel1
  ==>
  UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel2
Proof
INTRO_TAC THEN
RW_HYP_LEMMA_TAC PENDING_ACCESSES_CONDITIONALLY_EXPANDED_UPDATING_BD THEN
ETAC UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES THEN
INTRO_TAC THEN
AITAC THEN
SPLIT_ASM_DISJS_TAC THENL
[
 AITAC THEN
 STAC
 ,
 PTAC REQUEST_CONDITION_R_W THEN
 PTAC REQUEST_CONDITION_R THEN PTAC REQUEST_CONDITION_W THEN
 STAC
]
QED



Theorem PENDING_ACCESSES_RESTRICTED_UPDATING_BD_PRESERVES_CHANNEL_R_LEMMA:
!R W memory channel1 channel2.
  PENDING_ACCESSES_RESTRICTED_UPDATING_BD R W memory channel1 channel2 /\
  UPDATING_BD_CHANNEL_REQUESTING_READ_ADDRESSES R memory channel1
  ==>
  UPDATING_BD_CHANNEL_REQUESTING_READ_ADDRESSES R memory channel2
Proof
INTRO_TAC THEN
RW_HYP_LEMMA_TAC PENDING_ACCESSES_RESTRICTED_UPDATING_BD THEN
SPLIT_ASM_DISJS_TAC THENL
[
 ITAC UNMODIFIED_UPDATING_BD_PRESERVES_CHANNEL_R_LEMMA THEN
 STAC
 ,
 ITAC UNEXPANDED_UPDATING_BD_PRESERVES_CHANNEL_R_LEMMA THEN
 STAC
 ,
 ITAC CONDITIONALLY_EXPANDED_UPDATING_BD_PRESERVES_CHANNEL_R_LEMMA THEN
 STAC
]
QED

Theorem PENDING_ACCESSES_RESTRICTED_UPDATING_BD_PRESERVES_CHANNEL_W_LEMMA:
!R W memory channel1 channel2.
  PENDING_ACCESSES_RESTRICTED_UPDATING_BD R W memory channel1 channel2 /\
  UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel1
  ==>
  UPDATING_BD_CHANNEL_REQUESTING_WRITE_ADDRESSES W memory channel2
Proof
INTRO_TAC THEN
RW_HYP_LEMMA_TAC PENDING_ACCESSES_RESTRICTED_UPDATING_BD THEN
SPLIT_ASM_DISJS_TAC THENL
[
 ITAC UNMODIFIED_UPDATING_BD_PRESERVES_CHANNEL_W_LEMMA THEN
 STAC
 ,
 ITAC UNEXPANDED_UPDATING_BD_PRESERVES_CHANNEL_W_LEMMA THEN
 STAC
 ,
 ITAC CONDITIONALLY_EXPANDED_UPDATING_BD_PRESERVES_CHANNEL_W_LEMMA THEN
 STAC
]
QED

val _ = export_theory();
