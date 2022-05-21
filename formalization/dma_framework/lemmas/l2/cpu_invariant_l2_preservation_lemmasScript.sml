open HolKernel Parse boolLib bossLib helper_tactics;
open invariant_l2Theory proof_obligations_cpu_l2Theory;

val _ = new_theory "cpu_invariant_l2_preservation_lemmas";

Theorem BD_TO_FETCH_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA:
!device_characteristics channel_id device bd.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  MEM bd (schannel device channel_id).queue.bds_to_fetch
  ==>
  DMAC_CAN_ACCESS_MEMORY device_characteristics device
Proof
INTRO_TAC THEN
PTAC proof_obligationsTheory.DMAC_CAN_ACCESS_MEMORY THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
PTAC proof_obligationsTheory.IDLE_DMAC THEN
CCONTR_TAC THEN
ETAC boolTheory.NOT_CLAUSES THEN
AIRTAC THEN
LRTAC THEN
ETAC listTheory.MEM THEN
STAC
QED

Theorem BD_TO_UPDATE_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA:
!device_characteristics channel_id device bd.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  MEM bd (schannel device channel_id).queue.bds_to_update
  ==>
  DMAC_CAN_ACCESS_MEMORY device_characteristics device
Proof
INTRO_TAC THEN
PTAC proof_obligationsTheory.DMAC_CAN_ACCESS_MEMORY THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
PTAC proof_obligationsTheory.IDLE_DMAC THEN
CCONTR_TAC THEN
ETAC boolTheory.NOT_CLAUSES THEN
AIRTAC THEN
LRTAC THEN
ETAC listTheory.MEM THEN
STAC
QED

Theorem BD_TO_PROCESS_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA:
!device_characteristics channel_id device bd.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  MEM bd (schannel device channel_id).queue.bds_to_process
  ==>
  DMAC_CAN_ACCESS_MEMORY device_characteristics device
Proof
INTRO_TAC THEN
PTAC proof_obligationsTheory.DMAC_CAN_ACCESS_MEMORY THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
PTAC proof_obligationsTheory.IDLE_DMAC THEN
CCONTR_TAC THEN
ETAC boolTheory.NOT_CLAUSES THEN
AIRTAC THEN
LRTAC THEN
ETAC listTheory.MEM THEN
STAC
QED

Theorem BD_TO_WRITE_BACK_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA:
!device_characteristics channel_id device bd.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  MEM bd (schannel device channel_id).queue.bds_to_write_back
  ==>
  DMAC_CAN_ACCESS_MEMORY device_characteristics device
Proof
INTRO_TAC THEN
PTAC proof_obligationsTheory.DMAC_CAN_ACCESS_MEMORY THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
PTAC proof_obligationsTheory.IDLE_DMAC THEN
CCONTR_TAC THEN
ETAC boolTheory.NOT_CLAUSES THEN
AIRTAC THEN
LRTAC THEN
ETAC listTheory.MEM THEN
STAC
QED

Theorem CPU_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics memory1 memory2 cpu1 cpu2 address_bytes device.
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes /\
  INVARIANT_FETCH_BD_L2 device_characteristics memory1 device
  ==>
  INVARIANT_FETCH_BD_L2 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC INVARIANT_FETCH_BD_L2 THEN
INTRO_TAC THEN
PTAC proof_obligations_cpu_l1Theory.PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY THEN
AITAC THEN
RW_HYPS_TAC proof_obligations_cpu_l1Theory.DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
ITAC BD_TO_FETCH_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA THEN
AITAC THEN
AIRTAC THEN
ETAC stateTheory.R_W_EQ THEN
RLTAC THEN
RLTAC THEN
STAC
QED

Theorem CPU_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics memory1 memory2 cpu1 cpu2 address_bytes device.
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes /\
  INVARIANT_UPDATE_BD_L2 device_characteristics memory1 device
  ==>
  INVARIANT_UPDATE_BD_L2 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC INVARIANT_UPDATE_BD_L2 THEN
INTRO_TAC THEN
PTAC proof_obligations_cpu_l1Theory.PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY THEN
AITAC THEN
RW_HYPS_TAC proof_obligations_cpu_l1Theory.DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
ITAC BD_TO_UPDATE_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA THEN
AITAC THEN
AIRTAC THEN
ETAC stateTheory.R_W_EQ THEN
RLTAC THEN
RLTAC THEN
STAC
QED

Theorem CPU_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics memory1 memory2 cpu1 cpu2 address_bytes device.
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes /\
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory1 device
  ==>
  INVARIANT_TRANSFER_DATA_L2 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC INVARIANT_TRANSFER_DATA_L2 THEN
INTRO_TAC THEN
PTAC proof_obligations_cpu_l1Theory.PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY THEN
AITAC THEN
RW_HYPS_TAC proof_obligations_cpu_l1Theory.DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
ITAC BD_TO_PROCESS_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA THEN
AITAC THEN
AIRTAC THEN
ETAC stateTheory.R_W_EQ THEN
RLTAC THEN
RLTAC THEN
STAC
QED

Theorem CPU_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics memory1 memory2 cpu1 cpu2 address_bytes device.
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes /\
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory1 device
  ==>
  INVARIANT_WRITE_BACK_BD_L2 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC INVARIANT_WRITE_BACK_BD_L2 THEN
INTRO_TAC THEN
PTAC proof_obligations_cpu_l1Theory.PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY THEN
AITAC THEN
RW_HYPS_TAC proof_obligations_cpu_l1Theory.DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
ITAC BD_TO_WRITE_BACK_IMPLIES_DMAC_CAN_ACCESS_MEMORY_LEMMA THEN
AITAC THEN
AIRTAC THEN
ETAC stateTheory.R_W_EQ THEN
RLTAC THEN
RLTAC THEN
STAC
QED

Theorem CPU_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics memory1 memory2 cpu1 cpu2 address_bytes device.
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_OR_SUPERSET_OF_SCRATCHPAD INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes /\
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory1 device
  ==>
  INVARIANT_SCRATCHPAD_R_L2 device_characteristics memory2 device
Proof
INTRO_TAC THEN
PTAC proof_obligations_cpu_l1Theory.PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY THEN
PTAC proof_obligations_cpu_l2Theory.PROOF_OBLIGATION_CPU_PRESERVES_R_W_OR_SUPERSET_OF_SCRATCHPAD THEN
Cases_on ‘DMAC_CAN_ACCESS_MEMORY device_characteristics device’ THENL
[
 WEAKEN_TAC is_forall THEN
 AIRTAC THEN
 RW_HYPS_TAC proof_obligations_cpu_l1Theory.DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
 AIRTAC THEN
 ETAC INVARIANT_SCRATCHPAD_R_L2 THEN
 ETAC stateTheory.R_W_EQ THEN
 STAC
 ,
 AIRTAC THEN
 RW_HYPS_TAC proof_obligations_cpu_l2Theory.NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W THEN
 AIRTAC THEN
 ETAC INVARIANT_SCRATCHPAD_R_L2 THEN
 INTRO_TAC THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  FAIRTAC THEN STAC
  ,
  PTAC proof_obligationsTheory.SCRATCHPAD_R THEN AIRTAC THEN STAC
 ]
]
QED

Theorem CPU_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics memory1 memory2 cpu1 cpu2 address_bytes device.
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_OR_SUPERSET_OF_SCRATCHPAD INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes /\
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory1 device
  ==>
  INVARIANT_SCRATCHPAD_W_L2 device_characteristics memory2 device
Proof
INTRO_TAC THEN
PTAC proof_obligations_cpu_l1Theory.PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY THEN
PTAC proof_obligations_cpu_l2Theory.PROOF_OBLIGATION_CPU_PRESERVES_R_W_OR_SUPERSET_OF_SCRATCHPAD THEN
Cases_on ‘DMAC_CAN_ACCESS_MEMORY device_characteristics device’ THENL
[
 WEAKEN_TAC is_forall THEN
 AIRTAC THEN
 RW_HYPS_TAC proof_obligations_cpu_l1Theory.DMAC_CAN_ACCESS_MEMORY_IMPLIES_R_W_EQ THEN
 AIRTAC THEN
 ETAC INVARIANT_SCRATCHPAD_W_L2 THEN
 ETAC stateTheory.R_W_EQ THEN
 STAC
 ,
 AIRTAC THEN
 RW_HYPS_TAC proof_obligations_cpu_l2Theory.NOT_DMAC_CAN_ACCESS_MEMORY_IMPLIES_PRESERVED_R_W_OR_SCRATCHPAD_R_W THEN
 AIRTAC THEN
 ETAC INVARIANT_SCRATCHPAD_W_L2 THEN
 INTRO_TAC THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  FAIRTAC THEN STAC
  ,
  PTAC proof_obligationsTheory.SCRATCHPAD_W THEN AIRTAC THEN STAC
 ]
]
QED

Theorem CPU_MEMORY_WRITE_PRESERVES_INVARIANT_L2_LEMMA:
!INVARIANT_CPU cpu_transition device_characteristics memory1 memory2 cpu1 cpu2 address_bytes device.
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_WHEN_DMAC_ACCESSES_MEMORY INVARIANT_CPU cpu_transition device_characteristics /\
  PROOF_OBLIGATION_CPU_PRESERVES_R_W_OR_SUPERSET_OF_SCRATCHPAD INVARIANT_CPU cpu_transition device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  cpu_transition cpu1 (cpu_memory_write address_bytes) cpu2 /\
  memory2 = update_memory memory1 address_bytes /\
  INVARIANT_L2 device_characteristics memory1 device
  ==>
  INVARIANT_L2 device_characteristics memory2 device
Proof
INTRO_TAC THEN
ETAC INVARIANT_L2 THEN
ITAC CPU_PRESERVES_INVARIANT_FETCH_BD_L2_LEMMA THEN
ITAC CPU_PRESERVES_INVARIANT_UPDATE_BD_L2_LEMMA THEN
ITAC CPU_PRESERVES_INVARIANT_TRANSFER_DATA_L2_LEMMA THEN
ITAC CPU_PRESERVES_INVARIANT_WRITE_BACK_BD_L2_LEMMA THEN
ITAC CPU_PRESERVES_INVARIANT_SCRATCHPAD_R_L2_LEMMA THEN
ITAC CPU_PRESERVES_INVARIANT_SCRATCHPAD_W_L2_LEMMA THEN
STAC
QED

val _ = export_theory();

