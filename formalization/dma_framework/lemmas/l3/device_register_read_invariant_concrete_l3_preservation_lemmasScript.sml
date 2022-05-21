open HolKernel Parse boolLib bossLib helper_tactics;
open l3Theory invariant_l3Theory proof_obligations_cpu_l3Theory;

val _ = new_theory "device_register_read_invariant_concrete_l3_preservation_lemmas";

Theorem REGISTER_READ_PRESERVES_WRITE_ADDRESS_NOT_BD_TO_FETCH_LEMMA:
!device_characteristics memory addresses bytes new_requests request_was internal_state1 internal_state2.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  (internal_state2, bytes, new_requests) = device_characteristics.dma_characteristics.register_read internal_state1 addresses /\
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory internal_state1 request_was
  ==>
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory internal_state2 request_was
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.WRITE_ADDRESS_NOT_BD_TO_FETCH THEN
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH THEN
AIRTAC THEN
AITAC THEN
QLRTAC THEN
AIRTAC THEN
STAC
QED

Theorem REGISTER_READ_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA:
!device_characteristics memory addresses bytes new_requests request_was internal_state1 internal_state2.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  (internal_state2, bytes, new_requests) = device_characteristics.dma_characteristics.register_read internal_state1 addresses /\
  CONSISTENT_DMA_WRITE device_characteristics memory internal_state1 request_was
  ==>
  CONSISTENT_DMA_WRITE device_characteristics memory internal_state2 request_was
Proof
INTRO_TAC THEN
ETAC bd_queuesTheory.CONSISTENT_DMA_WRITE THEN
INTRO_TAC THEN
AIRTAC THEN
IRTAC REGISTER_READ_PRESERVES_WRITE_ADDRESS_NOT_BD_TO_FETCH_LEMMA THEN
STAC
QED

Theorem DMA_REGISTER_READ_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA:
!device_characteristics memory device1 device2 addresses bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  (device2, dma_address_bytes, bytes) = dma_register_read device_characteristics is_valid_l3 device1 addresses /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device1
  ==>
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_register_read THEN
LRTAC THEN
EQ_PAIR_ASM_TAC THEN
RLTAC THEN
LRTAC THEN
LRTAC THEN
LRTAC THEN
ETAC NO_MEMORY_WRITES_TO_BDS THEN
RECORD_TAC THEN
ETAC operationsTheory.channel_requests THEN
RECORD_TAC THEN
INTRO_TAC THEN
AIRTAC THEN
IRTAC REGISTER_READ_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA THEN
STAC
QED


Theorem FUNCTION_REGISTER_READ_PRESERVES_INVARIANT_BDS_TO_FETCH_DISJOINT_LEMMA:
!device_characteristics memory device1 device2 addresses bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  (device2, bytes) = function_register_read device_characteristics device1 addresses /\
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device1
  ==>
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device2
Proof
INTRO_TAC THEN
IRTAC device_register_read_lemmasTheory.FUNCTION_REGISTER_READ_PRESERVES_DMA_STATE_LEMMA THEN
ETAC invariant_l3Theory.INVARIANT_BDS_TO_FETCH_DISJOINT THEN
STAC
QED

Theorem FUNCTION_REGISTER_READ_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA:
!device_characteristics memory device1 device2 addresses bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  (device2, bytes) = function_register_read device_characteristics device1 addresses /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device1
  ==>
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device2
Proof
INTRO_TAC THEN
IRTAC device_register_read_lemmasTheory.FUNCTION_REGISTER_READ_PRESERVES_DMA_STATE_LEMMA THEN
ETAC NO_MEMORY_WRITES_TO_BDS THEN
ETAC operationsTheory.channel_requests THEN
LRTAC THEN
STAC
QED

Theorem DEVICE_REGISTER_READ_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA:
!device_characteristics memory device1 device2 addresses bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  (device2, dma_address_bytes, bytes) = device_register_read device_characteristics is_valid_l3 device1 addresses /\
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device1
  ==>
  NO_MEMORY_WRITES_TO_BDS device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC operationsTheory.device_register_read THENL
[
 IRTAC DMA_REGISTER_READ_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA THEN STAC
 ,
 IRTAC FUNCTION_REGISTER_READ_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

(*******************************************************************************)

Theorem DMA_REGISTER_READ_PRESERVES_NOT_DMA_BDS_LEMMA:
!device_characteristics memory device1 device2 addresses bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BD_INTERPRETATION device_characteristics /\
  (device2, dma_address_bytes, bytes) = dma_register_read device_characteristics is_valid_l3 device1 addresses /\
  NOT_DMA_BDS device_characteristics memory device1
  ==>
  NOT_DMA_BDS device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC NOT_DMA_BDS THEN
ITAC invariant_l3_lemmasTheory.DMA_REGISTER_READ_PRESERVES_CHANNEL_BDS_LEMMA THEN
ITAC invariant_l3_lemmasTheory.DMA_REGISTER_READ_PRESERVES_CHANNEL_BDS_LEMMA THEN
IRTAC device_register_read_lemmasTheory.DMA_REGISTER_READ_IMPLIES_REGISTER_READ_LEMMA THEN
AXTAC THEN
INTRO_TAC THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC “channel_id_dma_bd : 'b channel_id_type” thm)) THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC “channel_id_bd : 'b channel_id_type” thm)) THEN
ADTAC false THEN
ADTAC false THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BD_INTERPRETATION THEN
AIRTAC THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC “channel_id_dma_bd : 'b channel_id_type” thm)) THEN
ADTAC false THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC “channel_id_dma_bd : 'b channel_id_type” thm)) THEN
PAT_X_ASSUM “!x.P” (fn thm => ASSUME_TAC (SPEC “channel_id_bd : 'b channel_id_type” thm)) THEN
AIRTAC THEN
STAC
QED

Theorem FUNCTION_REGISTER_READ_PRESERVES_NOT_DMA_BDS_LEMMA:
!device_characteristics memory device1 device2 addresses bytes.
  (device2,bytes) = function_register_read device_characteristics device1 addresses /\
  NOT_DMA_BDS device_characteristics memory device1
  ==>
  NOT_DMA_BDS device_characteristics memory device2
Proof
INTRO_TAC THEN
IRTAC device_register_read_lemmasTheory.FUNCTION_REGISTER_READ_PRESERVES_DMA_STATE_LEMMA THEN
ETAC NOT_DMA_BDS THEN
LRTAC THEN
STAC
QED

Theorem DEVICE_REGISTER_READ_PRESERVES_NOT_DMA_BDS_LEMMA:
!device_characteristics memory device1 device2 addresses bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BD_INTERPRETATION device_characteristics /\
  (device2, dma_address_bytes, bytes) = device_register_read device_characteristics is_valid_l3 device1 addresses /\
  NOT_DMA_BDS device_characteristics memory device1
  ==>
  NOT_DMA_BDS device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC operationsTheory.device_register_read THENL
[
 IRTAC DMA_REGISTER_READ_PRESERVES_NOT_DMA_BDS_LEMMA THEN STAC
 ,
 IRTAC FUNCTION_REGISTER_READ_PRESERVES_NOT_DMA_BDS_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

(*******************************************************************************)

(*
Theorem DMA_REGISTER_READ_PRESERVES_NOT_DMA_SCRATCHPAD_LEMMA:
!device_characteristics memory device1 device2 addresses bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_SCRATCHPAD device_characteristics /\
  NOT_DMA_SCRATCHPAD device_characteristics memory device1 /\
  (device2,bytes) = dma_register_read device_characteristics is_valid_l3 device1 addresses
  ==>
  NOT_DMA_SCRATCHPAD device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC NOT_DMA_SCRATCHPAD THEN
INTRO_TAC THEN
ITAC invariant_l3_lemmasTheory.DMA_REGISTER_READ_PRESERVES_CHANNEL_BDS_LEMMA THEN
QLRTAC THEN
IRTAC device_register_read_lemmasTheory.DMA_REGISTER_READ_IMPLIES_REGISTER_READ_LEMMA THEN
AXTAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BD_INTERPRETATION THEN
AITAC THEN
AITAC THEN
QRLTAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_READ_PRESERVES_SCRATCHPAD THEN
AIRTAC THEN
LRTAC THEN
AIRTAC THEN
STAC
QED

Theorem FUNCTION_REGISTER_READ_PRESERVES_NOT_DMA_SCRATCHPAD_LEMMA:
!device_characteristics memory device1 device2 addresses bytes.
  NOT_DMA_SCRATCHPAD device_characteristics memory device1 /\
  (device2, bytes) = function_register_read device_characteristics device1 addresses
  ==>
  NOT_DMA_SCRATCHPAD device_characteristics memory device2
Proof
INTRO_TAC THEN
IRTAC device_register_read_lemmasTheory.FUNCTION_REGISTER_READ_PRESERVES_DMA_STATE_LEMMA THEN
ETAC NOT_DMA_SCRATCHPAD THEN
STAC
QED

Theorem DEVICE_REGISTER_READ_PRESERVES_NOT_DMA_SCRATCHPAD_LEMMA:
!device_characteristics memory device1 device2 addresses bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_SCRATCHPAD device_characteristics /\
  (device2,bytes) = device_register_read device_characteristics is_valid_l3 device1 addresses /\
  NOT_DMA_SCRATCHPAD device_characteristics memory device1
  ==>
  NOT_DMA_SCRATCHPAD device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC operationsTheory.device_register_read THENL
[
 IRTAC DMA_REGISTER_READ_PRESERVES_NOT_DMA_SCRATCHPAD_LEMMA THEN STAC
 ,
 IRTAC FUNCTION_REGISTER_READ_PRESERVES_NOT_DMA_SCRATCHPAD_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED
*)

(*******************************************************************************)

Theorem EVERY_T_LEMMA:
!l. EVERY (\x. T) l
Proof
Induct THEN REWRITE_TAC [listTheory.EVERY_DEF] THEN STAC
QED

Theorem DMA_REGISTER_READ_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics device1 device2 addresses bytes dma_address_bytes.
  (device2, dma_address_bytes, bytes) = dma_register_read device_characteristics is_valid_l3 device1 addresses /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device1
  ==>
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device2
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_register_read THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 3 THEN
LRTAC THEN
ETAC MEMORY_WRITES_PRESERVES_BDS_TO_FETCH THEN
RECORD_TAC THEN
RLTAC THEN
ETAC stateTheory.READ_REQUESTS THEN
ETAC listTheory.EVERY_APPEND THEN
CONJS_TAC THEN TRY STAC THEN
LRTAC THEN
LRTAC THEN
ETAC listTheory.EVERY_FILTER THEN
REWRITE_TAC [EVERY_T_LEMMA]
QED

Theorem FUNCTION_REGISTER_READ_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics device1 device2 addresses bytes dma_addresS_bytes.
  (device2, dma_addresS_bytes, bytes) = function_register_read device_characteristics device1 addresses /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device1
  ==>
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device2
Proof
INTRO_TAC THEN
PTAC operationsTheory.function_register_read THEN
EQ_PAIR_ASM_TAC THEN
LRTAC THEN
RLTAC THEN
ETAC MEMORY_WRITES_PRESERVES_BDS_TO_FETCH THEN
RECORD_TAC THEN
STAC
QED

Theorem DEVICE_REGISTER_READ_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics device1 device2 addresses bytes dma_address_bytes.
  (device2, dma_address_bytes, bytes) = device_register_read device_characteristics is_valid_l3 device1 addresses /\
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device1
  ==>
  MEMORY_WRITES_PRESERVES_BDS_TO_FETCH device2
Proof
INTRO_TAC THEN
PTAC operationsTheory.device_register_read THENL
[
 IRTAC DMA_REGISTER_READ_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA THEN STAC
 ,
 IRTAC FUNCTION_REGISTER_READ_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

(*******************************************************************************)

Theorem DMA_REGISTER_READ_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA:
!device_characteristics memory device1 device2 addresses bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device1 /\
  (device2, dma_address_bytes, bytes) = dma_register_read device_characteristics is_valid_l3 device1 addresses
  ==>
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_EXTERNAL_FETCH_BD_REPLY THEN
RW_HYPS_TAC stateTheory.schannel THEN
REWRITE_TAC [stateTheory.schannel] THEN
ITAC device_register_read_lemmasTheory.DMA_REGISTER_READ_PRESERVES_CHANNELS_LEMMA THEN
LRTAC THEN
IRTAC device_register_read_lemmasTheory.DMA_REGISTER_READ_IMPLIES_REGISTER_READ_LEMMA THEN
AXTAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_READ_PRESERVES_FETCH_BD_ADDRESSES THEN
AIRTAC THEN
INTRO_TAC THEN
AITAC THEN
AIRTAC THEN
STAC
QED

Theorem FUNCTION_REGISTER_READ_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA:
!device_characteristics memory device1 device2 addresses bytes dma_address_bytes.
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device1 /\
  (device2, dma_address_bytes, bytes) = function_register_read device_characteristics device1 addresses
  ==>
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_EXTERNAL_FETCH_BD_REPLY THEN
IRTAC device_register_read_lemmasTheory.FUNCTION_REGISTER_READ_PRESERVES_DMA_STATE_LEMMA THEN
RW_HYPS_TAC stateTheory.schannel THEN
REWRITE_TAC [stateTheory.schannel] THEN
LRTAC THEN
STAC
QED

Theorem DEVICE_REGISTER_READ_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA:
!device_characteristics memory device1 device2 addresses bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  (device2, dma_address_bytes, bytes) = device_register_read device_characteristics is_valid_l3 device1 addresses /\
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device1
  ==>
  INVARIANT_EXTERNAL_FETCH_BD_REPLY device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC operationsTheory.device_register_read THENL
[
 IRTAC DMA_REGISTER_READ_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA THEN STAC
 ,
 IRTAC FUNCTION_REGISTER_READ_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

(*******************************************************************************)

Theorem DMA_REGISTER_READ_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA:
!device_characteristics memory device1 device2 addresses bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  (device2, dma_address_bytes, bytes) = dma_register_read device_characteristics is_valid_l3 device1 addresses /\
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device1
  ==>
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES THEN
RW_HYPS_TAC stateTheory.schannel THEN
REWRITE_TAC [stateTheory.schannel] THEN
ITAC device_register_read_lemmasTheory.DMA_REGISTER_READ_PRESERVES_CHANNELS_LEMMA THEN
LRTAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_READ_PRESERVES_FETCH_BD_ADDRESSES THEN
IRTAC device_register_read_lemmasTheory.DMA_REGISTER_READ_IMPLIES_REGISTER_READ_LEMMA THEN
AXTAC THEN
AIRTAC THEN
INTRO_TAC THEN
AITAC THEN
AIRTAC THEN
STAC
QED

Theorem FUNCTION_REGISTER_READ_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA:
!device_characteristics memory device1 device2 addresses bytes dma_address_bytes.
  (device2, dma_address_bytes, bytes) = function_register_read device_characteristics device1 addresses /\
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device1
  ==>
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES THEN
IRTAC device_register_read_lemmasTheory.FUNCTION_REGISTER_READ_PRESERVES_DMA_STATE_LEMMA THEN
RW_HYPS_TAC stateTheory.schannel THEN
REWRITE_TAC [stateTheory.schannel] THEN
LRTAC THEN
STAC
QED

Theorem DEVICE_REGISTER_READ_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA:
!device_characteristics memory device1 device2 addresses bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  (device2, dma_address_bytes, bytes) = device_register_read device_characteristics is_valid_l3 device1 addresses /\
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device1
  ==>
  FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC operationsTheory.device_register_read THENL
[
 IRTAC DMA_REGISTER_READ_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA THEN STAC
 ,
 IRTAC FUNCTION_REGISTER_READ_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

(*******************************************************************************)

Theorem DEVICE_REGISTER_READ_PRESERVES_INVARIANT_BDS_TO_FETCH_DISJOINT_LEMMA:
!device_characteristics memory device1 device2 addresses bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  (device2, dma_address_bytes, bytes) = device_register_read device_characteristics is_valid_l3 device1 addresses /\
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device1
  ==>
  INVARIANT_BDS_TO_FETCH_DISJOINT device_characteristics memory device2
Proof
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH THEN
PTAC operationsTheory.device_register_read THENL
[
 PTAC operationsTheory.dma_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 NLRTAC 4 THEN
 AIRTAC THEN
 ETAC invariant_l3Theory.INVARIANT_BDS_TO_FETCH_DISJOINT THEN
 RECORD_TAC THEN
 INTRO_TAC THEN
 AITAC THEN
 PAT_X_ASSUM “!x. P” (fn thm => ASSUME_TAC (Q.SPEC ‘memory’ thm)) THEN
 AIRTAC THEN
 STAC
 ,
 PTAC operationsTheory.function_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 LRTAC THEN
 ETAC invariant_l3Theory.INVARIANT_BDS_TO_FETCH_DISJOINT THEN
 RECORD_TAC THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN STAC
]
QED

Theorem DEVICE_REGISTER_READ_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA:
!device_characteristics memory device1 device2 addresses bytes dma_address_bytes.
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BD_INTERPRETATION device_characteristics /\
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  INVARIANT_CONCRETE_L3 device_characteristics memory device1 /\
  (device2, dma_address_bytes, bytes) = device_register_read device_characteristics is_valid_l3 device1 addresses
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory device2
Proof
INTRO_TAC THEN
ETAC INVARIANT_CONCRETE_L3 THEN
ITAC DEVICE_REGISTER_READ_PRESERVES_INVARIANT_BDS_TO_FETCH_DISJOINT_LEMMA THEN
ITAC DEVICE_REGISTER_READ_PRESERVES_INVARIANT_BDS_TO_FETCH_DISJOINT_LEMMA THEN
ITAC DEVICE_REGISTER_READ_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA THEN
ITAC DEVICE_REGISTER_READ_PRESERVES_NOT_DMA_BDS_LEMMA THEN
(*ITAC DEVICE_REGISTER_READ_PRESERVES_NOT_DMA_SCRATCHPAD_LEMMA THEN*)
ITAC DEVICE_REGISTER_READ_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA THEN
ITAC DEVICE_REGISTER_READ_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA THEN
ITAC DEVICE_REGISTER_READ_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA THEN
STAC
QED

Theorem FILTER_IS_VALID_L3_ID_LEMMA:
!new_requests.
  FILTER is_valid_l3 new_requests = new_requests
Proof
Induct THEN REWRITE_TAC [listTheory.FILTER] THEN
GEN_TAC THEN
PTAC l3Theory.is_valid_l3 THEN
REWRITE_TAC [l3Theory.is_valid_l3] THEN
STAC
QED

Theorem DMA_REGISTER_READ_L3_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_CPU_REGISTER_READ_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L3 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATIONS_DMA_L3 device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_read cpu_address_bytes) cpu2 /\
  (device2, dma_address_bytes, MAP SND cpu_address_bytes) = dma_register_read device_characteristics is_valid_l3 device1 (MAP FST cpu_address_bytes) /\
  memory2 = update_memory memory1 dma_address_bytes /\
  INVARIANT_CONCRETE_L3 device_characteristics memory1 device1
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_register_read THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 3 THEN
ETAC FILTER_IS_VALID_L3_ID_LEMMA THEN
RLTAC THEN
PTAC proof_obligations_cpu_l3Theory.PROOF_OBLIGATION_CPU_REGISTER_READ_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L3 THEN
AIRTAC THEN
STAC
QED

Theorem DEVICE_REGISTER_READ_L3_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics cpu1 cpu2 memory1 memory2 device1 device2 cpu_address_bytes dma_address_bytes.
  PROOF_OBLIGATION_CPU_REGISTER_READ_MEMORY_WRITE_PRESERVES_INVARIANT_CONCRETE_L3 INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_REGISTER_READ_PRESERVES_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATIONS_DMA_L3 device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_read cpu_address_bytes) cpu2 /\
  (device2, dma_address_bytes, MAP SND cpu_address_bytes) = device_register_read_l3 device_characteristics device1 (MAP FST cpu_address_bytes) /\
  memory2 = update_memory memory1 dma_address_bytes /\
  INVARIANT_CONCRETE_L3 device_characteristics memory1 device1
  ==>
  INVARIANT_CONCRETE_L3 device_characteristics memory2 device2
Proof
INTRO_TAC THEN
PTAC l3Theory.device_register_read_l3 THEN
PTAC operationsTheory.device_register_read THENL
[
 IRTAC DMA_REGISTER_READ_L3_PRESERVES_INVARIANT_CONCRETE_L3_LEMMA THEN STAC
 ,
 ETAC INVARIANT_CONCRETE_L3 THEN
 ITAC FUNCTION_REGISTER_READ_PRESERVES_INVARIANT_BDS_TO_FETCH_DISJOINT_LEMMA THEN
 ITAC FUNCTION_REGISTER_READ_PRESERVES_NO_MEMORY_WRITES_TO_BDS_LEMMA THEN
 ITAC FUNCTION_REGISTER_READ_PRESERVES_MEMORY_WRITES_PRESERVES_BDS_TO_FETCH_LEMMA THEN
 ITAC FUNCTION_REGISTER_READ_PRESERVES_INVARIANT_EXTERNAL_FETCH_BD_REPLY_LEMMA THEN
 ITAC FUNCTION_REGISTER_READ_PRESERVES_FETCH_BD_ADDRESSES_EQ_REQUEST_ADDRESSES_LEMMA THEN
 PTAC operationsTheory.function_register_read THEN
 EQ_PAIR_ASM_TAC THEN
 IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN STAC
 ,
 EQ_PAIR_ASM_TAC THEN IRTAC write_properties_lemmasTheory.EMPTY_DMA_ADDRESS_BYTES_PRESERVES_MEMORY_LEMMA THEN STAC
]
QED

val _ = export_theory();

