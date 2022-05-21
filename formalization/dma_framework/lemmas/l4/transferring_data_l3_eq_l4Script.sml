open HolKernel Parse boolLib bossLib helper_tactics;
open l3Theory l4Theory invariant_l4Theory;

val _ = new_theory "transferring_data_l3_eq_l4";

Theorem BD_TRANSFER_PAIR_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id
 q.
  ?ras was. (ras, was) = (cverification device_characteristics channel_id).bd_transfer_ras_was device.dma_state.internal_state q
Proof
REWRITE_TAC [GSYM pairTheory.pair_CASES]
QED

fun ADD_INST_LEMMA_TAC (lemma : Thm.thm) (A : Term.term list, t : Term.term) =
  let val (A', t') = (((concl o SPEC_ALL) lemma)::A, t) in
  let val validation = fn thms =>
    let val thm = hd thms in
    let val thm' = PROVE_HYP (SPEC_ALL lemma) thm in
      thm'
    end end in
    ([(A', t')], validation)
  end end

Theorem TRANSFERRING_DATA_REPLIES_REQUESTS_IMPLIES_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics channel_id p internal_state1 channel1 bd internal_state2
 channel2 new_requests complete replies memory.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  p = (coperation device_characteristics channel_id).process_replies_generate_requests /\
  (internal_state2, channel2, new_requests, complete) = transferring_data_replies_requests replies p internal_state1 channel1 bd
  ==>
  BDS_TO_FETCH_EQ device_characteristics memory internal_state1 internal_state2
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_replies_requests THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 4 THEN
ETAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH THEN
AIRTAC THEN
ETAC stateTheory.BDS_TO_FETCH_EQ THEN
INTRO_TAC THEN
AIRTAC THEN
STAC
QED

Theorem MEM_NEW_REQUESTS_IMPLIES_WRITE_REQUEST_LEMMA:
!l y new_requests e.
  l = request_to_write_addresses y /\
  MEM y new_requests /\
  MEM e l
  ==>
  ?address_bytes tag.
    MEM (request_write address_bytes tag) new_requests /\
    l = MAP FST address_bytes
Proof
INTRO_TAC THEN
PTAC operationsTheory.request_to_write_addresses THENL
[
 ALL_LRTAC THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
 ,
 ALL_LRTAC THEN PAXTAC THEN STAC
]
QED

Theorem TRANSFERRING_DATA_REPLIES_REQUESTS_IMPLIES_DECLARED_DMA_WRITES_LEMMA:
!device_characteristics channel_id p internal_state1 channel1 bd internal_state2
 channel2 new_requests complete replies ras was.
  PROOF_OBLIGATION_WRITE_REQUESTS_CONSISTENT_WITH_BD device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  p = (coperation device_characteristics channel_id).process_replies_generate_requests /\
  (internal_state2, channel2, new_requests, complete) = transferring_data_replies_requests replies p internal_state1 channel1 bd /\
  (ras, was) = (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state1 bd
  ==>
  LIST1_IN_LIST2 (FLAT (MAP request_to_write_addresses new_requests)) was
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_replies_requests THEN
EQ_PAIR_ASM_TAC THEN
NRLTAC 4 THEN
ETAC proof_obligationsTheory.PROOF_OBLIGATION_WRITE_REQUESTS_CONSISTENT_WITH_BD THEN
ETAC listsTheory.LIST1_IN_LIST2 THEN
ETAC listTheory.EVERY_MEM THEN
BETA_TAC THEN
INTRO_TAC THEN
ETAC listTheory.MEM_FLAT THEN
AXTAC THEN
ETAC listTheory.MEM_MAP THEN
AXTAC THEN
ITAC MEM_NEW_REQUESTS_IMPLIES_WRITE_REQUEST_LEMMA THEN
AXTAC THEN
AITAC THEN
AXTAC THEN
LRTAC THEN
EQ_PAIR_ASM_TAC THEN
RLTAC THEN
REMOVE_SINGLE_VAR_EQ_ASMS_TAC THEN
LRTAC THEN
IRTAC lists_lemmasTheory.LIST1_IN_LIST2_MEM_LIST1_IMPLIES_MEM_LIST2_LEMMA THEN
STAC
QED

Theorem PROCESS_REPLIES_GENERATE_REQUESTS_IMPLIES_SCRATCHPAD_ADDRESSES_EQ_LEMMA:
!device_characteristics channel_id p replies internal_state1 internal_state2
 channel1 channel2 bd requests complete.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_SCRATCHPAD device_characteristics /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  p = (coperation device_characteristics channel_id).process_replies_generate_requests /\
  (internal_state2, channel2, requests, complete) = transferring_data_replies_requests replies p internal_state1 channel1 bd
  ==>
  SCRATCHPAD_ADDRESSES_EQ device_characteristics internal_state1 internal_state2
Proof
INTRO_TAC THEN
PTAC operationsTheory.transferring_data_replies_requests THEN
EQ_PAIR_ASM_TAC THEN
RLTAC THEN RLTAC THEN RLTAC THEN RLTAC THEN LRTAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_SCRATCHPAD THEN
AIRTAC THEN
PTAC stateTheory.SCRATCHPAD_ADDRESSES_EQ THEN
STAC
QED

Theorem PROCESSING_BD_L4_EQ_L3_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id memory internal_state channel.
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVE_BDS_TO_FETCH device_characteristics /\
  PROOF_OBLIGATION_PROCESS_REPLIES_GENERATE_REQUESTS_PRESERVES_SCRATCHPAD device_characteristics /\
  PROOF_OBLIGATION_WRITE_REQUESTS_CONSISTENT_WITH_BD device_characteristics /\
  INVARIANT_PROCESS_BD_DMA_WRITE_L4 device_characteristics memory device /\
  BDS_TO_FETCH_EQ device_characteristics memory device.dma_state.internal_state internal_state /\
  SCRATCHPAD_ADDRESSES_EQ device_characteristics device.dma_state.internal_state internal_state /\
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device.dma_state.internal_state internal_state /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  channel = schannel device channel_id
  ==>
  transferring_data_l4 device_characteristics channel_id        internal_state channel =
  transferring_data_l3 device_characteristics channel_id memory internal_state channel
Proof
INTRO_TAC THEN
PTAC transferring_data_l4 THEN PTAC transferring_data_l3 THEN TRY (ASM_REWRITE_TAC [pairTheory.PAIR_EQ]) THEN
IRTAC lists_lemmasTheory.MEM_HD_LEMMA THEN
PTAC INVARIANT_PROCESS_BD_DMA_WRITE_L4 THEN
ETAC DMA_WRITE THEN
ADD_INST_LEMMA_TAC BD_TRANSFER_PAIR_LEMMA THEN
AXTAC THEN
AITAC THEN
IRTAC bd_queues_lemmasTheory.BDS_TO_FETCH_EQ_PRESERVE_CONSISTENT_DMA_WRITE_LEMMA THEN
ITAC TRANSFERRING_DATA_REPLIES_REQUESTS_IMPLIES_BDS_TO_FETCH_EQ_LEMMA THEN
ITAC PROCESS_REPLIES_GENERATE_REQUESTS_IMPLIES_SCRATCHPAD_ADDRESSES_EQ_LEMMA THEN
IRTAC bd_queues_lemmasTheory.BDS_TO_FETCH_EQ_PRESERVE_CONSISTENT_DMA_WRITE_LEMMA THEN
PTAC stateTheory.BD_TRANSFER_RAS_WAS_EQ THEN
AITAC THEN
QRLTAC THEN
IRTAC TRANSFERRING_DATA_REPLIES_REQUESTS_IMPLIES_DECLARED_DMA_WRITES_LEMMA THEN
IRTAC bd_queues_lemmasTheory.LIST1_IN_LIST2_PRESERVES_CONSISTENT_DMA_WRITE_LEMMA THEN
CONTR_ASMS_TAC
QED

val _ = export_theory();

