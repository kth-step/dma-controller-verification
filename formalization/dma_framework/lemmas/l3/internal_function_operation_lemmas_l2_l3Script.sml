open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory;

val _ = new_theory "internal_function_operation_lemmas_l2_l3";

Theorem INTERNAL_STATES_EQ_PRESERVED_LEMMA:
!device21 device22 device31 device32.
  INTERNAL_STATES_EQ device21 device22 /\
  INTERNAL_STATES_EQ device31 device32 /\
  INTERNAL_STATES_EQ device21 device31
  ==>
  INTERNAL_STATES_EQ device22 device32
Proof
INTRO_TAC THEN
ETAC stateTheory.INTERNAL_STATES_EQ THEN
STAC
QED

Theorem INTERNAL_FUNCTION_OPERATION_PRESERVES_ABSTRACT_BDS_TO_FETCH_LEMMA:
!device_characteristics environment device1 device2.
  device2 = internal_function_operation (THE device_characteristics.function_characteristics) environment device1
  ==>
  ABSTRACT_BDS_TO_FETCH_EQ device_characteristics device1 device2
Proof
INTRO_TAC THEN
ETAC stateTheory.ABSTRACT_BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
PTAC operationsTheory.internal_function_operation THEN
LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
STAC
QED

Theorem INTERNAL_FUNCTION_OPERATION_PRESERVES_CONCRETE_BDS_TO_FETCH_LEMMA:
!device_characteristics environment memory device1 device2.
  device2 = internal_function_operation (THE device_characteristics.function_characteristics) environment device1
  ==>
  CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device1 device2
Proof
INTRO_TAC THEN
ETAC stateTheory.CONCRETE_BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
PTAC operationsTheory.internal_function_operation THEN
LRTAC THEN
ETAC stateTheory.cverification THEN
RECORD_TAC THEN
STAC
QED

Theorem INTERNAL_FUNCTION_OPERATION_PRESERVES_BDS_TO_UPDATE_LEMMA:
!device_characteristics environment device1 device2.
  device2 = internal_function_operation (THE device_characteristics.function_characteristics) environment device1
  ==>
  BDS_TO_UPDATE_EQ device_characteristics device1 device2
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_UPDATE_EQ THEN
INTRO_TAC THEN
PTAC operationsTheory.internal_function_operation THEN
LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
STAC
QED

Theorem INTERNAL_FUNCTION_OPERATION_PRESERVES_BDS_TO_PROCESS_LEMMA:
!device_characteristics environment device1 device2.
  device2 = internal_function_operation (THE device_characteristics.function_characteristics) environment device1
  ==>
  BDS_TO_PROCESS_EQ device_characteristics device1 device2
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_PROCESS_EQ THEN
INTRO_TAC THEN
PTAC operationsTheory.internal_function_operation THEN
LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
STAC
QED

Theorem INTERNAL_FUNCTION_OPERATION_PRESERVES_BDS_TO_WRITE_BACK_LEMMA:
!device_characteristics environment device1 device2.
  device2 = internal_function_operation (THE device_characteristics.function_characteristics) environment device1
  ==>
  BDS_TO_WRITE_BACK_EQ device_characteristics device1 device2
Proof
INTRO_TAC THEN
ETAC stateTheory.BDS_TO_WRITE_BACK_EQ THEN
INTRO_TAC THEN
PTAC operationsTheory.internal_function_operation THEN
LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
STAC
QED

Theorem INTERNAL_FUNCTION_OPERATION_PRESERVES_MEMORY_REQUESTS_REPLIES_EQ_LEMMA:
!device_characteristics environment device1 device2.
  device2 = internal_function_operation (THE device_characteristics.function_characteristics) environment device1
  ==>
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device1 device2
Proof
INTRO_TAC THEN
ETAC stateTheory.MEMORY_REQUESTS_REPLIES_EQ THEN
PTAC operationsTheory.internal_function_operation THEN
LRTAC THEN
REWRITE_TAC [stateTheory.schannel] THEN
RECORD_TAC THEN
STAC
QED

Theorem INTERNAL_FUNCTION_OPERATION_PRESERVES_INTERNAL_STATES_EQ_LEMMA:
!device_characteristics environment device1 device2.
  device2 = internal_function_operation (THE device_characteristics.function_characteristics) environment device1
  ==>
  INTERNAL_STATES_EQ device1 device2
Proof
INTRO_TAC THEN
ETAC stateTheory.INTERNAL_STATES_EQ THEN
PTAC operationsTheory.internal_function_operation THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem INTERNAL_FUNCTION_OPERATION_PRESERVES_DEFINED_CHANNELS_EQ_LEMMA:
!device_characteristics environment device1 device2.
  device2 = internal_function_operation (THE device_characteristics.function_characteristics) environment device1
  ==>
  DEFINED_CHANNELS_EQ device_characteristics device1 device2
Proof
INTRO_TAC THEN
ETAC stateTheory.DEFINED_CHANNELS_EQ THEN
PTAC operationsTheory.internal_function_operation THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem INTERNAL_FUNCTION_OPERATION_BISIMS_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics memory device21 device31 device22 device32 environment.
  device22 = internal_function_operation (THE device_characteristics.function_characteristics) environment device21 /\
  device32 = internal_function_operation (THE device_characteristics.function_characteristics) environment device31 /\
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device21 device31
  ==>
  ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
IRTAC INTERNAL_FUNCTION_OPERATION_PRESERVES_ABSTRACT_BDS_TO_FETCH_LEMMA THEN
IRTAC INTERNAL_FUNCTION_OPERATION_PRESERVES_CONCRETE_BDS_TO_FETCH_LEMMA THEN
IRTAC L23EQ_lemmasTheory.ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_PRESERVED_LEMMA THEN
STAC
QED

Theorem INTERNAL_FUNCTION_OPERATION_BISIMS_BDS_TO_UPDATE_EQ_LEMMA:
!device_characteristics device21 device31 device22 device32 environment.
  device22 = internal_function_operation (THE device_characteristics.function_characteristics) environment device21 /\
  device32 = internal_function_operation (THE device_characteristics.function_characteristics) environment device31 /\
  BDS_TO_UPDATE_EQ device_characteristics device21 device31
  ==>
  BDS_TO_UPDATE_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
IRTAC INTERNAL_FUNCTION_OPERATION_PRESERVES_BDS_TO_UPDATE_LEMMA THEN
IRTAC INTERNAL_FUNCTION_OPERATION_PRESERVES_BDS_TO_UPDATE_LEMMA THEN
FIRTAC L23EQ_lemmasTheory.BDS_TO_UPDATE_EQ_PRESERVED_LEMMA THEN
STAC
QED

Theorem INTERNAL_FUNCTION_OPERATION_BISIMS_BDS_TO_PROCESS_EQ_LEMMA:
!device_characteristics device21 device31 device22 device32 environment.
  device22 = internal_function_operation (THE device_characteristics.function_characteristics) environment device21 /\
  device32 = internal_function_operation (THE device_characteristics.function_characteristics) environment device31 /\
  BDS_TO_PROCESS_EQ device_characteristics device21 device31
  ==>
  BDS_TO_PROCESS_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
IRTAC INTERNAL_FUNCTION_OPERATION_PRESERVES_BDS_TO_PROCESS_LEMMA THEN
IRTAC INTERNAL_FUNCTION_OPERATION_PRESERVES_BDS_TO_PROCESS_LEMMA THEN
FIRTAC L23EQ_lemmasTheory.BDS_TO_PROCESS_EQ_PRESERVED_LEMMA THEN
STAC
QED

Theorem INTERNAL_FUNCTION_OPERATION_BISIMS_BDS_TO_WRITE_BACK_EQ_LEMMA:
!device_characteristics device21 device31 device22 device32 environment.
  device22 = internal_function_operation (THE device_characteristics.function_characteristics) environment device21 /\
  device32 = internal_function_operation (THE device_characteristics.function_characteristics) environment device31 /\
  BDS_TO_WRITE_BACK_EQ device_characteristics device21 device31
  ==>
  BDS_TO_WRITE_BACK_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
IRTAC INTERNAL_FUNCTION_OPERATION_PRESERVES_BDS_TO_WRITE_BACK_LEMMA THEN
IRTAC INTERNAL_FUNCTION_OPERATION_PRESERVES_BDS_TO_WRITE_BACK_LEMMA THEN
FIRTAC L23EQ_lemmasTheory.BDS_TO_WRITE_BACK_EQ_PRESERVED_LEMMA THEN
STAC
QED

Theorem INTERNAL_FUNCTION_OPERATION_BISIMS_MEMORY_REQUESTS_REPLIES_EQ_LEMMA:
!device_characteristics device21 device31 device22 device32 environment.
  device22 = internal_function_operation (THE device_characteristics.function_characteristics) environment device21 /\
  device32 = internal_function_operation (THE device_characteristics.function_characteristics) environment device31 /\
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device21 device31
  ==>
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
IRTAC INTERNAL_FUNCTION_OPERATION_PRESERVES_MEMORY_REQUESTS_REPLIES_EQ_LEMMA THEN
IRTAC INTERNAL_FUNCTION_OPERATION_PRESERVES_MEMORY_REQUESTS_REPLIES_EQ_LEMMA THEN
FIRTAC L23EQ_lemmasTheory.MEMORY_REQUESTS_REPLIES_EQ_PRESERVED_LEMMA THEN
STAC
QED

Theorem INTERNAL_FUNCTION_OPERATION_BISIMS_FUNCTION_STATES_EQ_LEMMA:
!device_characteristics device21 device31 device22 device32 environment.
  device22 = internal_function_operation (THE device_characteristics.function_characteristics) environment device21 /\
  device32 = internal_function_operation (THE device_characteristics.function_characteristics) environment device31 /\
  FUNCTION_STATES_EQ device21 device31
  ==>
  FUNCTION_STATES_EQ device22 device32
Proof
INTRO_TAC THEN
REPEAT (PTAC operationsTheory.internal_function_operation) THEN
ETAC stateTheory.FUNCTION_STATES_EQ THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem INTERNAL_FUNCTION_OPERATION_BISIMS_INTERNAL_STATES_EQ_LEMMA:
!device_characteristics device21 device31 device22 device32 environment.
  device22 = internal_function_operation (THE device_characteristics.function_characteristics) environment device21 /\
  device32 = internal_function_operation (THE device_characteristics.function_characteristics) environment device31 /\
  INTERNAL_STATES_EQ device21 device31
  ==>
  INTERNAL_STATES_EQ device22 device32
Proof
INTRO_TAC THEN
IRTAC INTERNAL_FUNCTION_OPERATION_PRESERVES_INTERNAL_STATES_EQ_LEMMA THEN
IRTAC INTERNAL_FUNCTION_OPERATION_PRESERVES_INTERNAL_STATES_EQ_LEMMA THEN
FIRTAC INTERNAL_STATES_EQ_PRESERVED_LEMMA THEN
STAC
QED

Theorem INTERNAL_FUNCTION_OPERATION_BISIMS_DEFINED_CHANNELS_EQ_LEMMA:
!device_characteristics device21 device31 device22 device32 environment.
  device22 = internal_function_operation (THE device_characteristics.function_characteristics) environment device21 /\
  device32 = internal_function_operation (THE device_characteristics.function_characteristics) environment device31 /\
  DEFINED_CHANNELS_EQ device_characteristics device21 device31
  ==>
  DEFINED_CHANNELS_EQ device_characteristics device22 device32
Proof
INTRO_TAC THEN
IRTAC INTERNAL_FUNCTION_OPERATION_PRESERVES_DEFINED_CHANNELS_EQ_LEMMA THEN
IRTAC INTERNAL_FUNCTION_OPERATION_PRESERVES_DEFINED_CHANNELS_EQ_LEMMA THEN
FIRTAC L23EQ_lemmasTheory.DEFINED_CHANNELS_EQ_PRESERVED_LEMMA THEN
STAC
QED

Theorem INTERNAL_FUNCTION_OPERATION_BISIMS_L23EQ_LEMMA:
!device_characteristics memory device21 device31 device22 device32 environment.
  device22 = internal_function_operation (THE device_characteristics.function_characteristics) environment device21 /\
  device32 = internal_function_operation (THE device_characteristics.function_characteristics) environment device31 /\
  L23EQ device_characteristics memory device21 device31
  ==>
  L23EQ device_characteristics memory device22 device32
Proof
INTRO_TAC THEN
ETAC L23EQTheory.L23EQ THEN
FITAC INTERNAL_FUNCTION_OPERATION_BISIMS_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA THEN
FITAC INTERNAL_FUNCTION_OPERATION_BISIMS_BDS_TO_UPDATE_EQ_LEMMA THEN
FITAC INTERNAL_FUNCTION_OPERATION_BISIMS_BDS_TO_PROCESS_EQ_LEMMA THEN
FITAC INTERNAL_FUNCTION_OPERATION_BISIMS_BDS_TO_WRITE_BACK_EQ_LEMMA THEN
FITAC INTERNAL_FUNCTION_OPERATION_BISIMS_MEMORY_REQUESTS_REPLIES_EQ_LEMMA THEN
FITAC INTERNAL_FUNCTION_OPERATION_BISIMS_FUNCTION_STATES_EQ_LEMMA THEN
FITAC INTERNAL_FUNCTION_OPERATION_BISIMS_INTERNAL_STATES_EQ_LEMMA THEN
FITAC INTERNAL_FUNCTION_OPERATION_BISIMS_DEFINED_CHANNELS_EQ_LEMMA THEN
STAC
QED

val _ = export_theory();

