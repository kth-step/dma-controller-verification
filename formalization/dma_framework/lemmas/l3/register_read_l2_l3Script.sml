open HolKernel Parse boolLib bossLib helper_tactics;
open L23EQTheory l2Theory l3Theory proof_obligations_cpu_l2Theory;

val _ = new_theory "register_read_l2_l3";

Theorem DEVICE_REGISTER_READ_PRESERVES_CHANNELS_LEMMA:
!device_characteristics device1 device2 is_valid addresses read_bytes dma_address_bytes.
  (device2, dma_address_bytes, read_bytes) = device_register_read device_characteristics is_valid device1 addresses
  ==>
  !channel_id. (schannel device2 channel_id) = (schannel device1 channel_id)
Proof
INTRO_TAC THEN
GEN_TAC THEN
PTAC operationsTheory.device_register_read THENL
[
 PTAC operationsTheory.dma_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 ALL_RLTAC THEN
 LRTAC THEN
 ETAC stateTheory.schannel THEN
 RECORD_TAC THEN
 STAC
 ,
 PTAC operationsTheory.function_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 LRTAC THEN
 ETAC stateTheory.schannel THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem DEVICE_REGISTER_READ_PRESERVES_BDS_TO_UPDATE_PROCESS_WRITE_BACK_LEMMA:
!device_characteristics device1 device2 is_valid addresses read_bytes dma_address_bytes.
  (device2, dma_address_bytes, read_bytes) = device_register_read device_characteristics is_valid device1 addresses
  ==>
  BDS_TO_UPDATE_EQ device_characteristics device1 device2 /\
  BDS_TO_PROCESS_EQ device_characteristics device1 device2 /\
  BDS_TO_WRITE_BACK_EQ device_characteristics device1 device2
Proof
INTRO_TAC THEN
IRTAC DEVICE_REGISTER_READ_PRESERVES_CHANNELS_LEMMA THEN
REPEAT CONJ_TAC THENL
[
 ETAC stateTheory.BDS_TO_UPDATE_EQ THEN STAC
 ,
 ETAC stateTheory.BDS_TO_PROCESS_EQ THEN STAC
 ,
 ETAC stateTheory.BDS_TO_WRITE_BACK_EQ THEN STAC
]
QED

Theorem BDS_TO_UPDATE_EQ_BSIM_LEMMA:
!device_characteristics device21 device31 device22 device32.
  BDS_TO_UPDATE_EQ device_characteristics device21 device31 /\
  BDS_TO_UPDATE_EQ device_characteristics device21 device22 /\
  BDS_TO_UPDATE_EQ device_characteristics device31 device32
  ==>
  BDS_TO_UPDATE_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_UPDATE_EQ THEN
INTRO_TAC THEN
AITAC THEN AITAC THEN AITAC THEN
STAC
QED

Theorem BDS_TO_PROCESS_EQ_BSIM_LEMMA:
!device_characteristics device21 device31 device22 device32.
  BDS_TO_PROCESS_EQ device_characteristics device21 device31 /\
  BDS_TO_PROCESS_EQ device_characteristics device21 device22 /\
  BDS_TO_PROCESS_EQ device_characteristics device31 device32
  ==>
  BDS_TO_PROCESS_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_PROCESS_EQ THEN
INTRO_TAC THEN
AITAC THEN AITAC THEN AITAC THEN
STAC
QED

Theorem BDS_TO_WRITE_BACK_EQ_BSIM_LEMMA:
!device_characteristics device21 device31 device22 device32.
  BDS_TO_WRITE_BACK_EQ device_characteristics device21 device31 /\
  BDS_TO_WRITE_BACK_EQ device_characteristics device21 device22 /\
  BDS_TO_WRITE_BACK_EQ device_characteristics device31 device32
  ==>
  BDS_TO_WRITE_BACK_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_WRITE_BACK_EQ THEN
INTRO_TAC THEN
AITAC THEN AITAC THEN AITAC THEN
STAC
QED



Theorem DEVICE_REGISTER_READ_PRESERVES_CONCRETE_BDS_TO_FETCH_LEMMA:
!device_characteristics memory device1 device2 is_valid addresses bytes channel_id dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (device2, dma_address_bytes, bytes) = device_register_read device_characteristics is_valid device1 addresses
  ==>
  (cverification device_characteristics channel_id).bds_to_fetch memory device2.dma_state.internal_state =
  (cverification device_characteristics channel_id).bds_to_fetch memory device1.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC operationsTheory.device_register_read THENL
[
 PTAC operationsTheory.dma_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 ALL_RLTAC THEN
 PTAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH THEN
 AIRTAC THEN
 AIRTAC THEN
 ALL_LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 PTAC operationsTheory.function_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem DEVICE_REGISTER_READ_INTERNAL_STATES_FUNCTION_STATES_EQ_L2_L3_LEMMA:
!device_characteristics device21 device31 device22 is_valid addresses dma_address_bytes read_bytes.
  INTERNAL_STATES_EQ device21 device31 /\
  FUNCTION_STATES_EQ device21 device31 /\
  (device22, dma_address_bytes, read_bytes) = device_register_read device_characteristics is_valid device21 addresses
  ==>
  ?device32.
    (device32, dma_address_bytes, read_bytes) = device_register_read device_characteristics is_valid device31 addresses
Proof
INTRO_TAC THEN
PTAC operationsTheory.device_register_read THEN PTAC operationsTheory.device_register_read THENL
[
 PTAC operationsTheory.dma_register_read THEN
 PTAC operationsTheory.dma_register_read THEN
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN
 EXISTS_EQ_TAC THEN
 EQ_PAIR_ASM_TAC THEN
 ETAC stateTheory.FUNCTION_STATES_EQ THEN
 ETAC stateTheory.INTERNAL_STATES_EQ THEN
 ALL_RLTAC THEN
 LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 STAC
 ,
 PTAC operationsTheory.function_register_read THEN
 PTAC operationsTheory.function_register_read THEN
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN
 EXISTS_EQ_TAC THEN
 EQ_PAIR_ASM_TAC THEN
 ETAC stateTheory.FUNCTION_STATES_EQ THEN
 ALL_RLTAC THEN
 LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 STAC
 ,
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN EQ_PAIR_ASM_TAC THEN EXISTS_EQ_TAC THEN STAC
 ,
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN EQ_PAIR_ASM_TAC THEN EXISTS_EQ_TAC THEN STAC
]
QED

Theorem DEVICE_REGISTER_READ_INTERNAL_STATES_FUNCTION_STATES_EQ_L3_L2_LEMMA:
!device_characteristics device21 device31 device32 is_valid addresses read_bytes dma_address_bytes.
  INTERNAL_STATES_EQ device21 device31 /\
  FUNCTION_STATES_EQ device21 device31 /\
  (device32, dma_address_bytes, read_bytes) = device_register_read device_characteristics is_valid device31 addresses
  ==>
  ?device22.
    (device22, dma_address_bytes, read_bytes) = device_register_read device_characteristics is_valid device21 addresses
Proof
INTRO_TAC THEN
PTAC operationsTheory.device_register_read THEN PTAC operationsTheory.device_register_read THENL
[
 PTAC operationsTheory.dma_register_read THEN
 PTAC operationsTheory.dma_register_read THEN
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN
 EXISTS_EQ_TAC THEN
 EQ_PAIR_ASM_TAC THEN
 ETAC stateTheory.FUNCTION_STATES_EQ THEN
 ETAC stateTheory.INTERNAL_STATES_EQ THEN
 ALL_RLTAC THEN
 LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 STAC
 ,
 PTAC operationsTheory.function_register_read THEN
 PTAC operationsTheory.function_register_read THEN
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN
 EXISTS_EQ_TAC THEN
 EQ_PAIR_ASM_TAC THEN
 ETAC stateTheory.FUNCTION_STATES_EQ THEN
 ALL_RLTAC THEN
 LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 STAC
 ,
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN EQ_PAIR_ASM_TAC THEN EXISTS_EQ_TAC THEN STAC
 ,
 REWRITE_TAC [pairTheory.PAIR_EQ] THEN EQ_PAIR_ASM_TAC THEN EXISTS_EQ_TAC THEN STAC
]
QED











Theorem DEVICE_REGISTER_READ_BSIM_INTERNAL_FUNCTION_STATE_LEMMA:
!device_characteristics device21 device31 device22 device32 is_valid addresses read_bytes dma_address_bytes.
  INTERNAL_STATES_EQ device21 device31 /\
  FUNCTION_STATES_EQ device21 device31 /\
  (device22, dma_address_bytes, read_bytes) = device_register_read device_characteristics is_valid device21 addresses /\
  (device32, dma_address_bytes, read_bytes) = device_register_read device_characteristics is_valid device31 addresses
  ==>
  INTERNAL_STATES_EQ device22 device32 /\
  FUNCTION_STATES_EQ device22 device32
Proof
INTRO_TAC THEN
PTAC operationsTheory.device_register_read THEN PTAC operationsTheory.device_register_read THENL
[
 PTAC operationsTheory.dma_register_read THEN
 PTAC operationsTheory.dma_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 ALL_RLTAC THEN
 ETAC stateTheory.INTERNAL_STATES_EQ THEN
 RLTAC THEN
 ALL_LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 ALL_LRTAC THEN
 ETAC stateTheory.FUNCTION_STATES_EQ THEN
 RECORD_TAC THEN
 STAC
 ,
 PTAC operationsTheory.function_register_read THEN
 PTAC operationsTheory.function_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 ETAC stateTheory.FUNCTION_STATES_EQ THEN
 RLTAC THEN
 RLTAC THEN
 LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 ALL_LRTAC THEN
 ETAC stateTheory.INTERNAL_STATES_EQ THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem DEVICE_REGISTER_READ_BSIM_DEFINED_CHANNELS_LEMMA:
!device_characteristics device21 device31 device22 device32 is_valid addresses read_bytes dma_address_bytes.
  INTERNAL_STATES_EQ device21 device31 /\
  FUNCTION_STATES_EQ device21 device31 /\
  DEFINED_CHANNELS_EQ device_characteristics device21 device31 /\
  (device22, dma_address_bytes, read_bytes) = device_register_read device_characteristics is_valid device21 addresses /\
  (device32, dma_address_bytes, read_bytes) = device_register_read device_characteristics is_valid device31 addresses
  ==>
  DEFINED_CHANNELS_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
PTAC operationsTheory.device_register_read THEN PTAC operationsTheory.device_register_read THENL
[
 PTAC operationsTheory.dma_register_read THEN
 PTAC operationsTheory.dma_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 ALL_RLTAC THEN
 ETAC stateTheory.INTERNAL_STATES_EQ THEN
 ALL_LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 ALL_RLTAC THEN
 ETAC stateTheory.DEFINED_CHANNELS_EQ THEN
 RECORD_TAC THEN
 STAC
 ,
 PTAC operationsTheory.function_register_read THEN
 PTAC operationsTheory.function_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 RLTAC THEN
 ETAC stateTheory.FUNCTION_STATES_EQ THEN
 RLTAC THEN
 RLTAC THEN
 LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 ALL_RLTAC THEN
 ALL_LRTAC THEN
 ETAC stateTheory.DEFINED_CHANNELS_EQ THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem INTERNAL_STATES_EQ_IMPLIES_INTERNAL_STATE_EQ_LEMMA:
!device2 device3.
  INTERNAL_STATES_EQ device2 device3
  ==>
  device2.dma_state.internal_state = device3.dma_state.internal_state
Proof
INTRO_TAC THEN
ETAC stateTheory.INTERNAL_STATES_EQ THEN
STAC
QED

Theorem FUNCTION_STATES_EQ_IMPLIES_FUNCTION_STATE_EQ_LEMMA:
!device2 device3.
  FUNCTION_STATES_EQ device2 device3
  ==>
  device2.function_state = device3.function_state
Proof
INTRO_TAC THEN
ETAC stateTheory.FUNCTION_STATES_EQ THEN
STAC
QED

Theorem MEMORY_REQUESTS_REPLIES_EQ_IMPLIES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_EQ_LEMMA:
!device_characteristics device2 device3.
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device2 device3
  ==>
  device2.dma_state.pending_register_related_memory_requests = device3.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
ETAC stateTheory.MEMORY_REQUESTS_REPLIES_EQ THEN
STAC
QED

Theorem MEMORY_REQUESTS_REPLIES_EQ_IMPLIES_PENDING_REGISTER_RELATED_MEMORY_REPLIES_EQ_LEMMA:
!device_characteristics device2 device3.
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device2 device3
  ==>
  device2.dma_state.pending_register_related_memory_replies = device3.dma_state.pending_register_related_memory_replies
Proof
INTRO_TAC THEN
ETAC stateTheory.MEMORY_REQUESTS_REPLIES_EQ THEN
STAC
QED

Theorem DEVICE_REGISTER_READ_BSIM_MEMORY_REQUESTS_REPLIES_LEMMA:
!device_characteristics device21 device31 device22 device32 is_valid addresses read_bytes dma_address_bytes.
  INTERNAL_STATES_EQ device21 device31 /\
  FUNCTION_STATES_EQ device21 device31 /\
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device21 device31 /\
  DEFINED_CHANNELS_EQ device_characteristics device21 device31 /\
  (device22, dma_address_bytes, read_bytes) = device_register_read device_characteristics is_valid device21 addresses /\
  (device32, dma_address_bytes, read_bytes) = device_register_read device_characteristics is_valid device31 addresses
  ==>
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
PTAC operationsTheory.device_register_read THEN PTAC operationsTheory.device_register_read THENL
[
 PTAC operationsTheory.dma_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 3 THEN
 PTAC operationsTheory.dma_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 3 THEN
 ALL_RLTAC THEN 
 ETAC stateTheory.INTERNAL_STATES_EQ THEN
 RLTAC THEN
 LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 NRLTAC 3 THEN
 RLTAC THEN
 RLTAC THEN
 NRLTAC 2 THEN
 NRLTAC 2 THEN
 ITAC MEMORY_REQUESTS_REPLIES_EQ_IMPLIES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_EQ_LEMMA THEN
 LRTAC THEN
 RLTAC THEN
 RLTAC THEN
 ETAC stateTheory.MEMORY_REQUESTS_REPLIES_EQ THEN
 ALL_LRTAC THEN
 RECORD_TAC THEN
 ASM_REWRITE_TAC [] THEN
 INTRO_TAC THEN
 ETAC stateTheory.schannel THEN
 RW_HYPS_TAC stateTheory.schannel THEN
 RECORD_TAC THEN
 AIRTAC THEN
 STAC
 ,
 PTAC operationsTheory.function_register_read THEN
 PTAC operationsTheory.function_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 ALL_RLTAC THEN
 ETAC stateTheory.FUNCTION_STATES_EQ THEN
 RLTAC THEN
 LRTAC THEN
 EQ_PAIR_ASM_TAC THEN
 ALL_RLTAC THEN
 ALL_LRTAC THEN
 ETAC stateTheory.MEMORY_REQUESTS_REPLIES_EQ THEN
 RECORD_TAC THEN
 ASM_REWRITE_TAC [] THEN
 INTRO_TAC THEN
 ETAC stateTheory.schannel THEN
 RW_HYPS_TAC stateTheory.schannel THEN
 RECORD_TAC THEN
 AIRTAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem DEVICE_REGISTER_READ_BSIM_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics memory device21 device31 device22 device32 is_valid addresses read_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  INTERNAL_STATES_EQ device21 device31 /\
  FUNCTION_STATES_EQ device21 device31 /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device21 device31 /\
  (device22, read_bytes) = device_register_read device_characteristics is_valid device21 addresses /\
  (device32, read_bytes) = device_register_read device_characteristics is_valid device31 addresses
  ==>
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
AITAC THEN
IRTAC DEVICE_REGISTER_READ_PRESERVES_CHANNELS_LEMMA THEN
IRTAC DEVICE_REGISTER_READ_PRESERVES_CONCRETE_BDS_TO_FETCH_LEMMA THEN
STAC
QED










Theorem DEVICE_REGISTER_READ_L2_L3_LEMMA:
!device_characteristics memory device21 device31 device22 is_valid addresses read_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  L23EQ device_characteristics memory device21 device31 /\
  (device22, read_bytes) = device_register_read device_characteristics is_valid device21 addresses
  ==>
  ?device32.
    (device32, read_bytes) = device_register_read device_characteristics is_valid device31 addresses /\
    L23EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
ETAC L23EQTheory.L23EQ THEN
ITAC DEVICE_REGISTER_READ_INTERNAL_STATES_FUNCTION_STATES_EQ_L2_L3_LEMMA THEN
AXTAC THEN
PAXTAC THEN
ASM_REWRITE_TAC [] THEN
FITAC DEVICE_REGISTER_READ_BSIM_INTERNAL_FUNCTION_STATE_LEMMA THEN
FITAC DEVICE_REGISTER_READ_BSIM_DEFINED_CHANNELS_LEMMA THEN
FITAC DEVICE_REGISTER_READ_BSIM_MEMORY_REQUESTS_REPLIES_LEMMA THEN
FITAC DEVICE_REGISTER_READ_BSIM_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA THEN
ETAC L23EQ THEN
ASM_REWRITE_TAC [] THEN
IRTAC DEVICE_REGISTER_READ_PRESERVES_BDS_TO_UPDATE_PROCESS_WRITE_BACK_LEMMA THEN
IRTAC DEVICE_REGISTER_READ_PRESERVES_BDS_TO_UPDATE_PROCESS_WRITE_BACK_LEMMA THEN
FITAC BDS_TO_UPDATE_EQ_BSIM_LEMMA THEN
FITAC BDS_TO_PROCESS_EQ_BSIM_LEMMA THEN
FITAC BDS_TO_WRITE_BACK_EQ_BSIM_LEMMA THEN
STAC
QED

Theorem DEVICE_REGISTER_READ_L3_L2_LEMMA:
!device_characteristics memory device21 device31 device32 is_valid addresses read_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  L23EQ device_characteristics memory device21 device31 /\
  (device32, read_bytes) = device_register_read device_characteristics is_valid device31 addresses
  ==>
  ?device22.
    (device22, read_bytes) = device_register_read device_characteristics is_valid device21 addresses /\
    L23EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
ETAC L23EQTheory.L23EQ THEN
ITAC DEVICE_REGISTER_READ_INTERNAL_STATES_FUNCTION_STATES_EQ_L3_L2_LEMMA THEN
AXTAC THEN
PAXTAC THEN
ASM_REWRITE_TAC [] THEN
FITAC DEVICE_REGISTER_READ_BSIM_INTERNAL_FUNCTION_STATE_LEMMA THEN
FITAC DEVICE_REGISTER_READ_BSIM_DEFINED_CHANNELS_LEMMA THEN
FITAC DEVICE_REGISTER_READ_BSIM_MEMORY_REQUESTS_REPLIES_LEMMA THEN
FITAC DEVICE_REGISTER_READ_BSIM_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA THEN
ETAC L23EQ THEN
ASM_REWRITE_TAC [] THEN
IRTAC DEVICE_REGISTER_READ_PRESERVES_BDS_TO_UPDATE_PROCESS_WRITE_BACK_LEMMA THEN
IRTAC DEVICE_REGISTER_READ_PRESERVES_BDS_TO_UPDATE_PROCESS_WRITE_BACK_LEMMA THEN
FITAC BDS_TO_UPDATE_EQ_BSIM_LEMMA THEN
FITAC BDS_TO_PROCESS_EQ_BSIM_LEMMA THEN
FITAC BDS_TO_WRITE_BACK_EQ_BSIM_LEMMA THEN
STAC
QED

Theorem IS_VALID_L2_EQ_IS_VALID_L3:
is_valid_l2 = is_valid_l3
Proof
REWRITE_TAC [is_valid_l2, is_valid_l3, boolTheory.FUN_EQ_THM]
QED

Theorem DEVICE_SIM_L2_L3_REGISTER_READ_LEMMA:
!device_characteristics device21 device31 device22 memory cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  (device22, dma_address_bytes, MAP SND cpu_address_bytes) = device_register_read_l2 device_characteristics memory device21 (MAP FST cpu_address_bytes) /\
  L23EQ device_characteristics memory device21 device31
  ==>
  ?device32.
    (device32, dma_address_bytes, MAP SND cpu_address_bytes) = device_register_read_l3 device_characteristics device31 (MAP FST cpu_address_bytes) /\
    L23EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
PTAC device_register_read_l2 THEN
PTAC device_register_read_l3 THEN
ETAC IS_VALID_L2_EQ_IS_VALID_L3 THEN
IRTAC DEVICE_REGISTER_READ_L2_L3_LEMMA THEN
STAC
QED

Theorem DEVICE_SIM_L3_L2_REGISTER_READ_LEMMA:
!device_characteristics device21 device31 device32 memory cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  (device32, dma_address_bytes, MAP SND cpu_address_bytes) = device_register_read_l3 device_characteristics device31 (MAP FST cpu_address_bytes) /\
  L23EQ device_characteristics memory device21 device31
  ==>
  ?device22.
    (device22, dma_address_bytes, MAP SND cpu_address_bytes) = device_register_read_l2 device_characteristics memory device21 (MAP FST cpu_address_bytes) /\
    L23EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
PTAC device_register_read_l2 THEN
PTAC device_register_read_l3 THEN
ETAC IS_VALID_L2_EQ_IS_VALID_L3 THEN
IRTAC DEVICE_REGISTER_READ_L3_L2_LEMMA THEN
STAC
QED

val _ = export_theory();

