open HolKernel Parse boolLib bossLib helper_tactics;
open L23EQTheory l2Theory l3Theory proof_obligationsTheory proof_obligations_dma_l3Theory;

val _ = new_theory "internal_device_operation_l2_l3";

Theorem PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3_IMPLIES_PROOF_OBLIGATION_SCHEDULER_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 device_characteristics
  ==>
  PROOF_OBLIGATION_SCHEDULER device_characteristics
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 THEN
STAC
QED

Theorem PROOF_OBLIGATION_SCHEDULER_VALID_CHANNEL_ID_LEMMA:
!device_characteristics scheduler environment function_state
 internal_state collected_dma_state internal_state1 channel_id dma_channel_operation.
  PROOF_OBLIGATION_SCHEDULER device_characteristics /\
  scheduler = device_characteristics.dma_characteristics.scheduler /\
  (internal_state1, channel_id, dma_channel_operation) = scheduler environment function_state internal_state collected_dma_state
  ==>
  VALID_CHANNEL_ID device_characteristics channel_id
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATION_SCHEDULER THEN
AIRTAC THEN
STAC
QED

Theorem PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3_IMPLIES_PROOF_OBLIGATIONS_FETCH_UPDATE_PROCESS_WRITE_BACK_L2_L3_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 device_characteristics
  ==>
  PROOF_OBLIGATIONS_FETCH_UPDATE_PROCESS_WRITE_BACK_L2_L3 device_characteristics
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 THEN
STAC
QED

Theorem PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3_IMPLIES_PROOF_OBLIGATION_SCHEDULER_PRESERVES_FETCH_BD_ADDRESSES_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 device_characteristics
  ==>
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_FETCH_BD_ADDRESSES device_characteristics
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 THEN
STAC
QED

Theorem PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3_IMPLIES_PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLY_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 device_characteristics
  ==>
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLY_PRESERVES_BDS_TO_FETCH device_characteristics
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 THEN
PTAC PROOF_OBLIGATIONS_FETCH_UPDATE_PROCESS_WRITE_BACK_L2_L3 THEN
STAC
QED









Theorem ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_UPDATE_DEVICE_STATE_PRESERVES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics channel_id memory internal_state_pre_scheduling
 internal_state2 channel22 channel32 device21 device31 device22 device32.
  channel22.queue.bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2 /\
  device22 = update_device_state device21 channel_id internal_state2 channel22 /\
  device32 = update_device_state device31 channel_id internal_state2 channel32 /\
  internal_state_pre_scheduling = device21.dma_state.internal_state /\
  internal_state_pre_scheduling = device31.dma_state.internal_state /\
  (!channel_id'.
     VALID_CHANNEL_ID device_characteristics channel_id' /\
     channel_id' <> channel_id
     ==>
      (cverification device_characteristics channel_id').bds_to_fetch memory internal_state2 =
      (cverification device_characteristics channel_id').bds_to_fetch memory internal_state_pre_scheduling) /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device21 device31
  ==>
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
ETAC operationsTheory.update_device_state THEN
ETAC stateTheory.schannel THEN
ALL_LRTAC THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 LRTAC THEN ETAC optionTheory.THE_DEF THEN STAC
 ,
 RW_HYP_LEMMA_TAC boolTheory.EQ_SYM_EQ THEN
 FAITAC THEN
 LRTAC THEN
 AIRTAC THEN
 RLTAC THEN
 ETAC stateTheory.schannel THEN
 RECORD_TAC THEN
 STAC
]
QED

Theorem BDS_TO_UPDATE_EQ_UPDATE_DEVICE_STATE_PRESERVES_BDS_TO_UPDATE_EQ_LEMMA:
!device_characteristics channel_id internal_state2 channel22 channel32 device21 device31 device22 device32.
  channel22.queue.bds_to_update = channel32.queue.bds_to_update /\
  device22 = update_device_state device21 channel_id internal_state2 channel22 /\
  device32 = update_device_state device31 channel_id internal_state2 channel32 /\
  BDS_TO_UPDATE_EQ device_characteristics device21 device31
  ==>
  BDS_TO_UPDATE_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_UPDATE_EQ THEN
INTRO_TAC THEN
ETAC operationsTheory.update_device_state THEN
LRTAC THEN
LRTAC THEN
AIRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 ETAC optionTheory.THE_DEF THEN STAC
 ,
 STAC
]
QED

Theorem BDS_TO_UPDATE_EQ_UPDATE_DEVICE_STATE_PRESERVES_BDS_TO_PROCESS_EQ_LEMMA:
!device_characteristics channel_id internal_state2 channel22 channel32 device21 device31 device22 device32.
  channel22.queue.bds_to_process = channel32.queue.bds_to_process /\
  device22 = update_device_state device21 channel_id internal_state2 channel22 /\
  device32 = update_device_state device31 channel_id internal_state2 channel32 /\
  BDS_TO_PROCESS_EQ device_characteristics device21 device31
  ==>
  BDS_TO_PROCESS_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_PROCESS_EQ THEN
INTRO_TAC THEN
ETAC operationsTheory.update_device_state THEN
LRTAC THEN
LRTAC THEN
AIRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 ETAC optionTheory.THE_DEF THEN STAC
 ,
 STAC
]
QED

Theorem BDS_TO_WRITE_BACK_EQ_UPDATE_DEVICE_STATE_PRESERVES_BDS_TO_WRITE_BACK_EQ_LEMMA:
!device_characteristics channel_id internal_state2 channel22 channel32 device21 device31 device22 device32.
  channel22.queue.bds_to_write_back = channel32.queue.bds_to_write_back /\
  device22 = update_device_state device21 channel_id internal_state2 channel22 /\
  device32 = update_device_state device31 channel_id internal_state2 channel32 /\
  BDS_TO_WRITE_BACK_EQ device_characteristics device21 device31
  ==>
  BDS_TO_WRITE_BACK_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_WRITE_BACK_EQ THEN
INTRO_TAC THEN
ETAC operationsTheory.update_device_state THEN
LRTAC THEN
LRTAC THEN
AIRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 ETAC optionTheory.THE_DEF THEN STAC
 ,
 STAC
]
QED

Theorem MEMORY_REQUESTS_REPLIES_EQ_UPDATE_DEVICE_STATE_PRESERVES_MEMORY_REQUESTS_REPLIES_EQ_LEMMA:
!device_characteristics channel_id internal_state2 channel22 channel32 device21 device31 device22 device32.
  channel22.pending_accesses = channel32.pending_accesses /\
  device22 = update_device_state device21 channel_id internal_state2 channel22 /\
  device32 = update_device_state device31 channel_id internal_state2 channel32 /\
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device21 device31
  ==>
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.MEMORY_REQUESTS_REPLIES_EQ THEN
REPEAT CONJ_TAC THENL
[
 ETAC operationsTheory.update_device_state THEN LRTAC THEN LRTAC THEN RECORD_TAC THEN STAC
 ,
 ETAC operationsTheory.update_device_state THEN LRTAC THEN LRTAC THEN RECORD_TAC THEN STAC
 ,
 INTRO_TAC THEN
 AIRTAC THEN
 LRTAC THEN
 LRTAC THEN
 ETAC stateTheory.schannel THEN
 ETAC operationsTheory.update_device_state THEN
 RECORD_TAC THEN
 ETAC combinTheory.UPDATE_def THEN
 APP_SCALAR_TAC THEN
 IF_SPLIT_TAC THENL
 [
  ETAC optionTheory.THE_DEF THEN STAC
  ,
  STAC
 ]
]
QED

Theorem SCHEDULER_PRESERVES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESS_EQ_LEMMA:
!device_characteristics channel_id memory concrete_bds1 concrete_bds2 channel2
 channel3 scheduler internal_state1 internal_state2 dma_channel_operation
 environment function_state collected_dma_state.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  concrete_bds1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel2 channel3 /\
  scheduler = device_characteristics.dma_characteristics.scheduler /\
  (internal_state2, channel_id, dma_channel_operation) = scheduler environment function_state internal_state1 collected_dma_state /\
  concrete_bds2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2
  ==>
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel2 channel3
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
ALL_LRTAC THEN
ASM_REWRITE_TAC [] THEN
PTAC PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH THEN
AIRTAC THEN
AIRTAC THEN
STAC
QED

Theorem PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3_IMPLIES_PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics.
  PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 device_characteristics
  ==>
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH device_characteristics
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 THEN
STAC
QED

Theorem CHANNEL_OPERATION_L2_L3_PRESERVE_INTERNAL_STATES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_OTHER_BDS_TO_FETCH_LEMMA:
!device_characteristics channel_id memory internal_state1 internal_state22
 internal_state32 concrete_bds1 concrete_bds2 channel21 channel31 channel22
 channel32 dma_channel_operation environment.
  PROOF_OBLIGATIONS_FETCH_UPDATE_PROCESS_WRITE_BACK_L2_L3 device_characteristics /\
  EXTERNAL_BDS_FETCH_REPLY device_characteristics channel_id memory channel31 internal_state1 /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  concrete_bds1 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state1 /\
  concrete_bds2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state32 /\
  BDS_TO_FETCH_DISJOINT channel21.queue.bds_to_fetch /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds1 channel21 channel31 /\
  (internal_state22, channel22) = channel_operation_l2 device_characteristics channel_id dma_channel_operation (SOME memory) environment internal_state1 channel21 /\
  (internal_state32, channel32) = channel_operation_l3 device_characteristics channel_id dma_channel_operation (SOME memory) environment internal_state1 channel31
  ==>
  internal_state32 = internal_state22 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel22 channel32 /\
  OTHER_BDS_TO_FETCH_EQ device_characteristics channel_id memory internal_state1 internal_state32
Proof
INTRO_TAC THEN
PTAC channel_operation_l3 THEN
EQ_PAIR_ASM_TAC THEN
LRTAC THEN
RLTAC THEN
PTAC channel_operation_l2 THEN
EQ_PAIR_ASM_TAC THEN
RLTAC THEN
LRTAC THEN
PTAC PROOF_OBLIGATIONS_FETCH_UPDATE_PROCESS_WRITE_BACK_L2_L3 THEN
PTAC channel_operation_case_l3 THEN PTAC channel_operation_case_l2 THEN REMOVE_SINGLE_VAR_EQ_ASMS_TAC THENL
[
 MATCH_MP_TAC fetching_bd_lemmasTheory.FETCHING_BD_L2_L3_BSIMS_INTERNAL_STATE_CHANNEL_OTHER_BDS_TO_FETCH_LEMMA THEN PAXTAC THEN STAC
 ,
 MATCH_MP_TAC updating_bd_lemmasTheory.UPDATING_BD_L2_L3_BSIMS_INTERNAL_STATE_CHANNEL_OTHER_BDS_TO_FETCH_LEMMA THEN PAXTAC THEN STAC
 ,
 MATCH_MP_TAC processing_bd_lemmasTheory.PROCESSING_BD_L2_L3_BSIMS_INTERNAL_STATE_CHANNEL_OTHER_BDS_TO_FETCH_LEMMA THEN PAXTAC THEN STAC
 ,
 IRTAC writing_back_bd_lemmasTheory.WRITING_BACK_BD_L2_L3_BSIMS_INTERNAL_STATE_CHANNEL_BDS_TO_FETCH_LEMMA THEN
 CONJS_TAC THEN TRY STAC THEN
 ETAC stateTheory.OTHER_BDS_TO_FETCH_EQ THEN
 INTRO_TAC THEN
 ETAC stateTheory.BDS_TO_FETCH_EQ THEN
 AIRTAC THEN
 STAC
]
QED

Theorem SCHEDULER_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics scheduler environment function_state internal_state1
 collected_dma_state internal_state2 channel_id dma_channel_operation memory.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH device_characteristics /\
  scheduler = device_characteristics.dma_characteristics.scheduler /\
  (internal_state2, channel_id, dma_channel_operation) = scheduler environment function_state internal_state1 collected_dma_state
  ==>
  BDS_TO_FETCH_EQ device_characteristics memory internal_state1 internal_state2
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH THEN
PTAC stateTheory.BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
AIRTAC THEN
AIRTAC THEN
STAC
QED

Theorem ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_PRESERVED_LEMMA:
!device_characteristics memory device21 device31 internal_state internal_state2
 concrete_bds2 channel22 channel32 channel_id device22 device32.
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device21 device31 /\
  BDS_TO_FETCH_EQ device_characteristics memory device31.dma_state.internal_state internal_state /\
  OTHER_BDS_TO_FETCH_EQ device_characteristics channel_id memory internal_state internal_state2 /\
  concrete_bds2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel22 channel32 /\
  device22 = update_device_state device21 channel_id internal_state2 channel22 /\
  device32 = update_device_state device31 channel_id internal_state2 channel32
  ==>
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
ETAC operationsTheory.update_device_state THEN
ALL_LRTAC THEN
AITAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 ETAC optionTheory.THE_DEF THEN
 RLTAC THEN
 PTAC stateTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ THEN
 STAC
 ,
 LRTAC THEN
 PTAC stateTheory.OTHER_BDS_TO_FETCH_EQ THEN
 AITAC THEN
 LRTAC THEN
 PTAC stateTheory.BDS_TO_FETCH_EQ THEN
 AIRTAC THEN
 RECORD_TAC THEN
 STAC
]
QED

Theorem BDS_TO_UPDATE_EQ_PRESERVED_LEMMA:
!device_characteristics device21 device31 internal_state
 concrete_bds2 channel22 channel32 device22 device32 channel_id.
  BDS_TO_UPDATE_EQ device_characteristics device21 device31 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel22 channel32 /\
  device22 = update_device_state device21 channel_id internal_state channel22 /\
  device32 = update_device_state device31 channel_id internal_state channel32
  ==>
  BDS_TO_UPDATE_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_UPDATE_EQ THEN
INTRO_TAC THEN
AITAC THEN
IRTAC L23EQ_lemmasTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_BDS_TO_UPDATE_EQ_LEMMA THEN
ETAC operationsTheory.update_device_state THEN
ALL_LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 RLTAC THEN ETAC optionTheory.THE_DEF THEN STAC
 ,
 STAC
]
QED

Theorem BDS_TO_PROCESS_EQ_PRESERVED_LEMMA:
!device_characteristics device21 device31 internal_state
 concrete_bds2 channel22 channel32 device22 device32 channel_id.
  BDS_TO_PROCESS_EQ device_characteristics device21 device31 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel22 channel32 /\
  device22 = update_device_state device21 channel_id internal_state channel22 /\
  device32 = update_device_state device31 channel_id internal_state channel32
  ==>
  BDS_TO_PROCESS_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_PROCESS_EQ THEN
INTRO_TAC THEN
AITAC THEN
IRTAC L23EQ_lemmasTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_BDS_TO_PROCESS_EQ_LEMMA THEN
ETAC operationsTheory.update_device_state THEN
ALL_LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 RLTAC THEN ETAC optionTheory.THE_DEF THEN STAC
 ,
 STAC
]
QED

Theorem BDS_TO_WRITE_BACK_EQ_PRESERVED_LEMMA:
!device_characteristics device21 device31 internal_state
 concrete_bds2 channel22 channel32 device22 device32 channel_id.
  BDS_TO_WRITE_BACK_EQ device_characteristics device21 device31 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel22 channel32 /\
  device22 = update_device_state device21 channel_id internal_state channel22 /\
  device32 = update_device_state device31 channel_id internal_state channel32
  ==>
  BDS_TO_WRITE_BACK_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_WRITE_BACK_EQ THEN
INTRO_TAC THEN
AITAC THEN
IRTAC L23EQ_lemmasTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_BDS_TO_WRITE_BACK_EQ_LEMMA THEN
ETAC operationsTheory.update_device_state THEN
ALL_LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 RLTAC THEN ETAC optionTheory.THE_DEF THEN STAC
 ,
 STAC
]
QED

Theorem MEMORY_REQUESTS_REPLIES_EQ_PRESERVED_LEMMA:
!device_characteristics device21 device31 internal_state
 concrete_bds2 channel22 channel32 device22 device32 channel_id.
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device21 device31 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel22 channel32 /\
  device22 = update_device_state device21 channel_id internal_state channel22 /\
  device32 = update_device_state device31 channel_id internal_state channel32
  ==>
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.MEMORY_REQUESTS_REPLIES_EQ THEN
REPEAT CONJ_TAC THENL
[
 ETAC operationsTheory.update_device_state THEN ALL_LRTAC THEN RECORD_TAC THEN STAC
 ,
 ETAC operationsTheory.update_device_state THEN ALL_LRTAC THEN RECORD_TAC THEN STAC
 ,
 INTRO_TAC THEN
 AITAC THEN
 IRTAC L23EQ_lemmasTheory.ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_IMPLIES_MEMORY_REQUESTS_REPLIES_EQ_LEMMA THEN
 ETAC operationsTheory.update_device_state THEN
 ALL_LRTAC THEN
 ETAC stateTheory.schannel THEN
 RECORD_TAC THEN
 ETAC combinTheory.UPDATE_def THEN
 APP_SCALAR_TAC THEN
 IF_SPLIT_TAC THENL
 [
  RLTAC THEN ETAC optionTheory.THE_DEF THEN STAC
  ,
  STAC
 ]
]
QED

Theorem L23EQ_PRESERVED_LEMMA:
!device_characteristics memory device21 device31 internal_state internal_state2
 channel_id concrete_bds2 device22 device32 channel22 channel32.
  L23EQ device_characteristics memory device21 device31 /\
  BDS_TO_FETCH_EQ device_characteristics memory device31.dma_state.internal_state internal_state /\
  OTHER_BDS_TO_FETCH_EQ device_characteristics channel_id memory internal_state internal_state2 /\
  concrete_bds2 = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state2 /\
  ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ concrete_bds2 channel22 channel32 /\
  device22 = update_device_state device21 channel_id internal_state2 channel22 /\
  device32 = update_device_state device31 channel_id internal_state2 channel32
  ==>
  L23EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
ETAC L23EQ THEN
REPEAT CONJ_TAC THENL
[
 IRTAC ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_PRESERVED_LEMMA THEN STAC
 ,
 IRTAC BDS_TO_UPDATE_EQ_PRESERVED_LEMMA THEN STAC
 ,
 IRTAC BDS_TO_PROCESS_EQ_PRESERVED_LEMMA THEN STAC
 ,
 IRTAC BDS_TO_WRITE_BACK_EQ_PRESERVED_LEMMA THEN STAC
 ,
 IRTAC MEMORY_REQUESTS_REPLIES_EQ_PRESERVED_LEMMA THEN STAC
 ,
 FIRTAC L23EQ_lemmasTheory.FUNCTION_STATES_EQ_UPDATE_DEVICE_STATE_PRESERVES_FUNCTION_STATES_EQ_LEMMA THEN STAC
 ,
 FIRTAC L23EQ_lemmasTheory.INTERNAL_STATES_EQ_UPDATE_DEVICE_STATE_PRESERVES_INTERNAL_STATES_EQ_LEMMA THEN STAC
 ,
 FIRTAC L23EQ_lemmasTheory.DEFINED_CHANNELS_EQ_UPDATE_DEVICE_STATE_PRESERVES_DEFINED_CHANNELS_EQ_LEMMA THEN STAC
]
QED

Theorem SCHEDULER_PRESERVES_EXTERNAL_BDS_FETCH_REPLY_LEMMA:
!device_characteristics channel_id memory device scheduler internal_state1
 dma_channel_operation internal_state function_state environment collected_dma_state.
  PROOF_OBLIGATION_SCHEDULER device_characteristics /\
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  EXTERNAL_BDS_FETCH_REPLY device_characteristics channel_id memory (schannel device channel_id) internal_state /\
  scheduler = device_characteristics.dma_characteristics.scheduler /\
  (internal_state1, channel_id, dma_channel_operation) = scheduler environment function_state internal_state collected_dma_state
  ==>
  EXTERNAL_BDS_FETCH_REPLY device_characteristics channel_id memory (schannel device channel_id) internal_state1
Proof
INTRO_TAC THEN
ITAC PROOF_OBLIGATION_SCHEDULER_VALID_CHANNEL_ID_LEMMA THEN
PTAC PROOF_OBLIGATION_SCHEDULER_PRESERVES_FETCH_BD_ADDRESSES THEN
AITAC THEN
AITAC THEN
ETAC fetching_bd_lemmasTheory.EXTERNAL_BDS_FETCH_REPLY THEN
INTRO_TAC THEN
AIRTAC THEN
PTAC fetching_bd_lemmasTheory.EXTERNAL_FETCH_BD_REPLY THEN PTAC fetching_bd_lemmasTheory.EXTERNAL_FETCH_BD_REPLY THEN
STAC
QED

Theorem INVARIANT_BDS_TO_FETCH_DISJOINT_L23EQ_IMPLIES_BDS_TO_FETCH_DISJOINT_L3_L2_LEMMA:
!device_characteristics memory device21 device31 channel_id.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device31 /\
  L23EQ device_characteristics memory device21 device31
  ==>
  BDS_TO_FETCH_DISJOINT (schannel device21 channel_id).queue.bds_to_fetch
Proof
INTRO_TAC THEN
IRTAC L23EQ_lemmasTheory.L23EQ_IMPLIES_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA THEN
ETAC stateTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ THEN
AITAC THEN
ETAC invariant_l3Theory.INVARIANT_BDS_TO_FETCH_DISJOINT THEN
AIRTAC THEN
STAC
QED

Theorem INTERNAL_DMA_OPERATION_L2_L3_BISIMS_L23EQ_LEMMA:
!device_characteristics memory device21 device31 device22 device32 environment.
  PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 device_characteristics /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device31 /\
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device31 /\
  device22 = internal_dma_operation device_characteristics channel_operation_l2 (SOME memory) environment device21 /\
  device32 = internal_dma_operation device_characteristics channel_operation_l3 (SOME memory) environment device31 /\
  L23EQ device_characteristics memory device21 device31
  ==>
  L23EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
ETAC operationsTheory.internal_dma_operation THEN
BSIM_ONCE_LETS_TAC THEN NLLRTAC THEN
BSIM_ONCE_LETS_TAC THEN ITAC L23EQ_lemmasTheory.L23EQ_IMPLIES_FUNCTION_STATE_EQ_LEMMA THEN RLTAC THEN RLTAC THEN RLTAC THEN
BSIM_ONCE_LETS_TAC THEN NLLRTAC THEN NLLRTAC THEN ITAC L23EQ_lemmasTheory.L23EQ_IMPLIES_INTERNAL_STATE_EQ_LEMMA THEN LRTAC THEN
BSIM_ONCE_LETS_TAC THEN ITAC collect_dma_state_lemmasTheory.L23EQ_IMPLIES_COLLECT_DMA_STATE_EQ_LEMMA THEN LRTAC THEN LRTAC THEN
EQ_PAIR_ASM_TAC THEN NLRTAC 2 THEN
BSIM_ONCE_LETS_TAC THEN
BSIM_ONCE_LETS_TAC THEN

ITAC PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3_IMPLIES_PROOF_OBLIGATION_SCHEDULER_LEMMA THEN
ITAC PROOF_OBLIGATION_SCHEDULER_VALID_CHANNEL_ID_LEMMA THEN
ITAC L23EQ_lemmasTheory.L23EQ_IMPLIES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_EQ_LEMMA THEN
RW_HYP_LEMMA_TAC (GSYM stateTheory.schannel) THEN RW_HYP_LEMMA_TAC (GSYM stateTheory.schannel) THEN
ITAC INVARIANT_BDS_TO_FETCH_DISJOINT_L23EQ_IMPLIES_BDS_TO_FETCH_DISJOINT_L3_L2_LEMMA THEN
ASM_RL_RW_OTHERS_KEEP_TAC THEN ASM_RL_RW_OTHERS_KEEP_TAC THEN
ITAC PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3_IMPLIES_PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH_LEMMA THEN
ITAC SCHEDULER_PRESERVES_BDS_TO_FETCH_LEMMA THEN
ITAC SCHEDULER_PRESERVES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESS_EQ_LEMMA THEN
BSIM_ONCE_LETS_TAC THEN

ITAC fetching_bd_lemmasTheory.INVARIANT_EXTERNAL_FETCH_BD_REPLY_IMPLIES_EXTERNAL_BDS_FETCH_REPLY_LEMMA THEN
ITAC PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3_IMPLIES_PROOF_OBLIGATIONS_FETCH_UPDATE_PROCESS_WRITE_BACK_L2_L3_LEMMA THEN
ITAC PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3_IMPLIES_PROOF_OBLIGATION_SCHEDULER_PRESERVES_FETCH_BD_ADDRESSES_LEMMA THEN
IRTAC SCHEDULER_PRESERVES_EXTERNAL_BDS_FETCH_REPLY_LEMMA THEN
ASM_RL_RW_OTHERS_KEEP_TAC THEN
IRTAC CHANNEL_OPERATION_L2_L3_PRESERVE_INTERNAL_STATES_ABSTRACT_CONCRETE_BD_QUEUES_PENDING_ACCESSES_OTHER_BDS_TO_FETCH_LEMMA THEN
RLTAC THEN
BSIM_ONCE_LETS_TAC THEN
IRTAC L23EQ_PRESERVED_LEMMA THEN
STAC
QED

Theorem DEVICE_L2_L3_INTERNAL_DEVICE_OPERATION_LEMMA:
!device_characteristics memory device21 device22 device31 device32 environment.
  PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 device_characteristics /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device31 /\
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device31 /\
  device22 = internal_device_operation_l2 device_characteristics memory environment device21 /\
  device32 = internal_device_operation_l3 device_characteristics memory environment device31 /\
  L23EQ device_characteristics memory device21 device31
  ==>
  L23EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
PTAC internal_device_operation_l3 THEN PTAC internal_device_operation_l2 THEN
ETAC operationsTheory.internal_device_operation THEN
LETS_TAC THEN
ITAC L23EQ_lemmasTheory.L23EQ_IMPLIES_FUNCTION_STATE_EQ_LEMMA THEN
LRTAC THEN LRTAC THEN
ITAC L23EQ_lemmasTheory.L23EQ_IMPLIES_INTERNAL_STATE_EQ_LEMMA THEN
LRTAC THEN LRTAC THEN
ITAC collect_dma_state_lemmasTheory.L23EQ_IMPLIES_COLLECT_DMA_STATE_EQ_LEMMA THEN
LRTAC THEN LRTAC THEN
RLTAC THEN
RLTAC THEN
RLTAC THEN
SPLIT_SCALAR_CASE_TAC THENL
[
 FIRTAC internal_function_operation_lemmas_l2_l3Theory.INTERNAL_FUNCTION_OPERATION_BISIMS_L23EQ_LEMMA THEN STAC
 ,
 IRTAC PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3_IMPLIES_PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLY_PRESERVES_BDS_TO_FETCH_LEMMA THEN 
 FIRTAC process_register_related_memory_access_lemmasTheory.PROCESS_REGISTER_RELATED_MEMORY_ACCESS_BISIMS_L23EQ_LEMMA THEN
 STAC
 ,
 IRTAC INTERNAL_DMA_OPERATION_L2_L3_BISIMS_L23EQ_LEMMA THEN STAC
 ,
 STAC
]
QED

Theorem DEVICE_SIM_L2_L3_INTERNAL_DEVICE_OPERATION_LEMMA:
!device_characteristics memory device21 device22 device31 environment.
  PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 device_characteristics /\
  INVARIANT_L3 device_characteristics memory device31 /\
  device22 = internal_device_operation_l2 device_characteristics memory environment device21 /\
  L23EQ device_characteristics memory device21 device31
  ==>
  ?device32.
    device32 = internal_device_operation_l3 device_characteristics memory environment device31 /\
    L23EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
ETAC invariant_l3Theory.INVARIANT_L3 THEN
IRTAC DEVICE_L2_L3_INTERNAL_DEVICE_OPERATION_LEMMA THEN
EXISTS_EQ_TAC THEN
STAC
QED

Theorem DEVICE_SIM_L3_L2_INTERNAL_DEVICE_OPERATION_LEMMA:
!device_characteristics memory device21 device31 device32 environment.
  PROOF_OBLIGATIONS_INTERNAL_DEVICE_L2_L3 device_characteristics /\
  INVARIANT_L3 device_characteristics memory device31 /\
  device32 = internal_device_operation_l3 device_characteristics memory environment device31 /\
  L23EQ device_characteristics memory device21 device31
  ==>
  ?device22.
    device22 = internal_device_operation_l2 device_characteristics memory environment device21 /\
    L23EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
ETAC invariant_l3Theory.INVARIANT_L3 THEN
IRTAC DEVICE_L2_L3_INTERNAL_DEVICE_OPERATION_LEMMA THEN
EXISTS_EQ_TAC THEN
STAC
QED

val _ = export_theory();

