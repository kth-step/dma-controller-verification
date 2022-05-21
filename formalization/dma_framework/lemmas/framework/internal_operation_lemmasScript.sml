open HolKernel Parse boolLib bossLib helper_tactics;
open stateTheory operationsTheory proof_obligationsTheory;

val _ = new_theory "internal_operation_lemmas";

Theorem UPDATING_OTHER_CHANNEL_PRESERVES_CHANNEL_LEMMA:
!channels1 channels2 channel_id channel_id' channel1 channel2 channel.
  channels2 = (channel_id =+ channel) channels1 /\
  channel1 = THE (channels1 channel_id') /\
  channel_id <> channel_id' /\
  channel2 = THE (channels2 channel_id')
  ==>
  channel2 = channel1
Proof
INTRO_TAC THEN
ALL_LRTAC THEN
REWRITE_TAC [combinTheory.UPDATE_def] THEN
APP_SCALAR_TAC THEN
STAC
QED

Theorem INTERNAL_DMA_OPERATION_SCHEDULER_LEMMA:
!device_characteristics environment device1 internal_state_pre_scheduling
 internal_state1 channel1 function_state scheduler channel_id dma_channel_operation
 pipelines pending_register_memory_accesses.
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation
  ==>
  (internal_state1, channel_id, dma_channel_operation) = scheduler environment function_state internal_state_pre_scheduling (pipelines, pending_register_memory_accesses)
Proof
INTRO_TAC THEN
PTAC INTERNAL_DMA_OPERATION THEN
STAC
QED

Theorem INTERNAL_DMA_OPERATION_DEVICE_CHARACTERISTICS_SCHEDULER_LEMMA:
!device_characteristics environment device1 internal_state_pre_scheduling
 internal_state1 channel1 function_state scheduler channel_id dma_channel_operation
 pipelines pending_register_memory_accesses.
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation
  ==>
  (internal_state1, channel_id, dma_channel_operation) = device_characteristics.dma_characteristics.scheduler environment function_state internal_state_pre_scheduling (pipelines, pending_register_memory_accesses)
Proof
INTRO_TAC THEN
PTAC INTERNAL_DMA_OPERATION THEN
STAC
QED

Theorem INTERNAL_DMA_OPERATION_IMPLIES_CHANNEL_STATE_LEMMA:
!device_characteristics environment device1 pipelines
 pending_register_memory_accesses internal_state_pre_scheduling
 internal_state1 channel1 function_state scheduler channel_id
 dma_channel_operation.
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation
  ==>
  channel1 = schannel device1 channel_id
Proof
INTRO_TAC THEN
PTAC INTERNAL_DMA_OPERATION THEN
STAC
QED

Theorem INTERNAL_DMA_OPERATION_PIPELINES_PENDING_REGISTER_MEMORY_ACCESSES_LEMMA:
!device_characteristics environment device1 pipelines
 pending_register_memory_accesses internal_state_pre_scheduling
 internal_state1 channel1 function_state scheduler channel_id
 dma_channel_operation.
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation
  ==>
  (pipelines, pending_register_memory_accesses) = collect_dma_state device_characteristics.dma_characteristics device1.dma_state
Proof
INTRO_TAC THEN
PTAC INTERNAL_DMA_OPERATION THEN
STAC
QED

Theorem INTERNAL_DMA_OPERATION_INTERNAL_STATE_PRE_SCHEDULING_LEMMA:
!device_characteristics environment device1 pipelines
 pending_register_memory_accesses internal_state_pre_scheduling
 internal_state1 channel1 function_state scheduler channel_id
 dma_channel_operation.
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation
  ==>
  internal_state_pre_scheduling = device1.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC INTERNAL_DMA_OPERATION THEN
STAC
QED






Theorem INTERNAL_FUNCTION_OPERATION_PRESERVES_ALL_DMA_CHANNELS_PENDING_ACCESSES_LEMMA:
!device_characteristics environment device1 device2.
  device2 = internal_function_operation (THE device_characteristics.function_characteristics) environment device1
  ==>
  !channel_id.
    (schannel device2 channel_id).pending_accesses = (schannel device1 channel_id).pending_accesses
Proof
INTRO_TAC THEN
PTAC internal_function_operation THEN
IRTAC state_lemmasTheory.FUNCTION_STATE_UPDATE_PRESERVES_ALL_DMA_CHANNEL_PENDING_ACCESSES_LEMMA THEN
STAC
QED

Theorem INTERNAL_FUNCTION_OPERATION_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA:
!function_characteristics_option environment device1 device2.
  device2 = internal_function_operation function_characteristics_option environment device1
  ==>
  device2.dma_state.pending_register_related_memory_requests = device1.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
PTAC internal_function_operation THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem UPDATE_DEVICE_STATE_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA:
!device1 device2 channel_id internal_state channel.
  device2 = update_device_state device1 channel_id internal_state channel
  ==>
  device2.dma_state.pending_register_related_memory_requests = device1.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
PTAC update_device_state THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_ALL_DMA_CHANNEL_PENDING_ACCESSES_LEMMA:
!dma_characteristics device1 device2.
  device2 = process_register_related_memory_access dma_characteristics device1
  ==>
  !channel_id.
    (THE (device2.dma_state.channels channel_id)).pending_accesses =
    (THE (device1.dma_state.channels channel_id)).pending_accesses
Proof
INTRO_TAC THEN
GEN_TAC THEN
PTAC process_register_related_memory_access THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_IMPLIES_UNEXPANDED_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA:
!device_characteristics device1 device2.
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1
  ==>
  LIST1_IN_LIST2 device2.dma_state.pending_register_related_memory_requests device1.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
PTAC listsTheory.LIST1_IN_LIST2 THEN
PTAC process_register_related_memory_access THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [listTheory.EVERY_MEM] THEN
APP_SCALAR_TAC THEN
STAC
QED

Theorem INTERNAL_DMA_OPERATION_SCHEDULER_PRESERVES_BD_INTERPRETATION_LEMMA:
!device_characteristics environment device1 pipelines pending_register_memory_accesses internal_state_pre_scheduling
 internal_state1 channel1 function_state scheduler channel_id dma_channel_operation bd.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION device_characteristics /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines pending_register_memory_accesses channel_id dma_channel_operation
  ==>
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state1 bd =
    (cverification device_characteristics channel_id).bd_transfer_ras_was device1.dma_state.internal_state bd
Proof
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION THEN
PTAC INTERNAL_DMA_OPERATION THEN
AIRTAC THEN
INTRO_TAC THEN
AIRTAC THEN
STAC
QED

Theorem INTERNAL_DMA_OPERATION_IMPLIES_VALID_CHANNEL_ID_LEMMA:
!device_characteristics environment device1 pipelines pending_register_memory_accesses internal_state_pre_scheduling
 internal_state1 channel1 function_state scheduler channel_id dma_channel_operation.
  PROOF_OBLIGATION_SCHEDULER device_characteristics /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
     pending_register_memory_accesses channel_id dma_channel_operation
  ==>
  VALID_CHANNEL_ID device_characteristics channel_id
Proof
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_SCHEDULER THEN
PTAC INTERNAL_DMA_OPERATION THEN
AITAC THEN
STAC
QED

Theorem PROCESS_REPLIES_GENERATE_REQUESTS_IMPLIES_READ_ADDRESSES_IN_RAS_LEMMA:
!device_characteristics environment device1 pipelines pending_register_memory_accesses internal_state_pre_scheduling
 internal_state1 channel1 function_state scheduler channel_id dma_channel_operation
 bd bd_ras bd_was bd_ras_wass internal_state2 new_requests complete replies.
  PROOF_OBLIGATION_READ_REQUESTS_CONSISTENT_WITH_BD device_characteristics /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (bd, bd_ras, bd_was)::bd_ras_wass = channel1.queue.bds_to_process /\
  (internal_state2, new_requests, complete) = (coperation device_characteristics channel_id).process_replies_generate_requests internal_state1 bd replies
  ==>
  ?ras was.
    (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state1 bd = (ras, was) /\
    (!addresses tag. MEM (request_read addresses tag) new_requests ==> LIST1_IN_LIST2 addresses ras)
Proof
INTRO_TAC THEN
(fn (A, t) =>
 let val device_characteristics_goal = (rand o valOf) (List.find (fn ass => (length o #2 o strip_comb) ass = 1) A) in
 let val device_characteristics_thm = (#1 o dest_forall o concl) state_lemmasTheory.BD_TRANSFER_RAS_WAS_EQ_RAS_WAS_LEMMA in
 let val subst_te_ty = match_term device_characteristics_thm device_characteristics_goal in
 let val instantiated_thm = INST_TY_TERM subst_te_ty (SPEC_ALL state_lemmasTheory.BD_TRANSFER_RAS_WAS_EQ_RAS_WAS_LEMMA) in
   (ASSUME_TAC instantiated_thm THEN AXTAC) (A, t)
 end end end end
) THEN
PAXTAC THEN
ASM_REWRITE_TAC [] THEN
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_READ_REQUESTS_CONSISTENT_WITH_BD THEN
AITAC THEN
AXTAC THEN
LRTAC THEN
EQ_PAIR_ASM_TAC THEN
STAC
QED

Theorem PROCESS_REPLIES_GENERATE_REQUESTS_IMPLIES_WRITE_ADDRESSES_IN_WAS_LEMMA:
!device_characteristics device1 environment internal_state_pre_scheduling
 internal_state1 internal_state2 channel1 function_state scheduler
 channel_id dma_channel_operation bd bd_ras bd_was bd_ras_wass new_requests
 complete replies pipelines pending_register_memory_accesses.
  PROOF_OBLIGATION_WRITE_REQUESTS_CONSISTENT_WITH_BD device_characteristics /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state1 channel1 function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation /\
  VALID_CHANNEL_ID device_characteristics channel_id /\
  (bd, bd_ras, bd_was)::bd_ras_wass = channel1.queue.bds_to_process /\
  (internal_state2, new_requests, complete) = (coperation device_characteristics channel_id).process_replies_generate_requests internal_state1 bd replies
  ==>
  ?ras was.
    (cverification device_characteristics channel_id).bd_transfer_ras_was internal_state1 bd = (ras, was) /\
    (!address_bytes tag. MEM (request_write address_bytes tag) new_requests ==> LIST1_IN_LIST2 (MAP FST address_bytes) was)
Proof
INTRO_TAC THEN
(fn (A, t) =>
 let val device_characteristics_goal = (rand o valOf) (List.find (fn ass => (length o #2 o strip_comb) ass = 1) A) in
 let val device_characteristics_thm = (#1 o dest_forall o concl) state_lemmasTheory.BD_TRANSFER_RAS_WAS_EQ_RAS_WAS_LEMMA in
 let val subst_te_ty = match_term device_characteristics_thm device_characteristics_goal in
 let val instantiated_thm = INST_TY_TERM subst_te_ty (SPEC_ALL state_lemmasTheory.BD_TRANSFER_RAS_WAS_EQ_RAS_WAS_LEMMA) in
   (ASSUME_TAC instantiated_thm THEN AXTAC) (A, t)
 end end end end
) THEN
PAXTAC THEN
ASM_REWRITE_TAC [] THEN
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_WRITE_REQUESTS_CONSISTENT_WITH_BD THEN
AITAC THEN
AXTAC THEN
LRTAC THEN
EQ_PAIR_ASM_TAC THEN
STAC
QED

Theorem INTERNAL_DMA_OPERATION_SCHEDULER_IMPLIES_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics environment device1 pipelines channel_id
 pending_register_memory_accesses internal_state_pre_scheduling
 internal_state channel function_state scheduler dma_channel_operation.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH device_characteristics /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state channel function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation
  ==>
  !memory.
    BDS_TO_FETCH_EQ device_characteristics memory device1.dma_state.internal_state internal_state
Proof
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_SCHEDULER_PRESERVES_BDS_TO_FETCH THEN
PTAC INTERNAL_DMA_OPERATION THEN
REWRITE_TAC [BDS_TO_FETCH_EQ] THEN
INTRO_TAC THEN
AIRTAC THEN
AIRTAC THEN
STAC
QED

Theorem INTERNAL_DMA_OPERATION_SCHEDULER_IMPLIES_SCRATCHPAD_ADDRESSES_EQ_LEMMA:
!device_characteristics environment device1 pipelines channel_id
 pending_register_memory_accesses internal_state_pre_scheduling
 internal_state channel function_state scheduler dma_channel_operation.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_SCRATCHPAD device_characteristics /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state channel function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation
  ==>
  SCRATCHPAD_ADDRESSES_EQ device_characteristics device1.dma_state.internal_state internal_state
Proof
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_SCHEDULER_PRESERVES_SCRATCHPAD THEN
PTAC INTERNAL_DMA_OPERATION THEN
REWRITE_TAC [SCRATCHPAD_ADDRESSES_EQ] THEN
AIRTAC THEN
STAC
QED

Theorem INTERNAL_DMA_OPERATION_SCHEDULER_IMPLIES_PIPELINES_LEMMA:
!device_characteristics environment device pipelines channel_id
 pending_register_memory_accesses internal_state_pre_scheduling
 internal_state channel function_state scheduler dma_channel_operation.
  INTERNAL_DMA_OPERATION
    device_characteristics environment device internal_state_pre_scheduling
    internal_state channel function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation
  ==>
  pipelines = collect_channels_state device_characteristics.dma_characteristics device.dma_state.channels
Proof
INTRO_TAC THEN
PTAC INTERNAL_DMA_OPERATION THEN
PTAC collect_dma_state THEN
EQ_PAIR_ASM_TAC THEN
STAC
QED

Theorem INTERNAL_DMA_OPERATION_SCHEDULER_IMPLIES_BD_RAS_WAS_EQ_LEMMA:
!device_characteristics environment device1 pipelines channel_id
 pending_register_memory_accesses internal_state_pre_scheduling
 internal_state channel function_state scheduler dma_channel_operation.
  PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION device_characteristics /\
  INTERNAL_DMA_OPERATION
    device_characteristics environment device1 internal_state_pre_scheduling
    internal_state channel function_state scheduler pipelines
    pending_register_memory_accesses channel_id dma_channel_operation
  ==>
  BD_TRANSFER_RAS_WAS_EQ device_characteristics device1.dma_state.internal_state internal_state
Proof
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_SCHEDULER_PRESERVES_BD_INTERPRETATION THEN
PTAC INTERNAL_DMA_OPERATION THEN
REWRITE_TAC [BD_TRANSFER_RAS_WAS_EQ] THEN
INTRO_TAC THEN
AIRTAC THEN
AIRTAC THEN
STAC
QED




Theorem EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_UPDATE_LEMMA:
!channel1 channel2 channel3 bds_to_fetch.
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL channel1 channel2 bds_to_fetch /\
  channel1.queue.bds_to_update = channel3.queue.bds_to_update
  ==>
  channel2.queue.bds_to_update = channel3.queue.bds_to_update
Proof
INTRO_TAC THEN
ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL THEN
SPLIT_ASM_DISJS_TAC THENL
[
 ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH THEN
 ETAC operationsTheory.APPENDED_BDS THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 ETAC operationsTheory.NOT_EXTENDED_ABSTRACT_BDS_TO_FETCH_AND_UNCHANGED_CHANNEL THEN
 STAC
]
QED

Theorem EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_PROCESS_LEMMA:
!channel1 channel2 channel3 bds_to_fetch.
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL channel1 channel2 bds_to_fetch /\
  channel1.queue.bds_to_process = channel3.queue.bds_to_process
  ==>
  channel2.queue.bds_to_process = channel3.queue.bds_to_process
Proof
INTRO_TAC THEN
ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL THEN
SPLIT_ASM_DISJS_TAC THENL
[
 ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH THEN
 ETAC operationsTheory.APPENDED_BDS THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 ETAC operationsTheory.NOT_EXTENDED_ABSTRACT_BDS_TO_FETCH_AND_UNCHANGED_CHANNEL THEN
 STAC
]
QED

Theorem EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_BDS_TO_WRITE_BACK_LEMMA:
!channel1 channel2 channel3 bds_to_fetch.
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL channel1 channel2 bds_to_fetch /\
  channel1.queue.bds_to_write_back = channel3.queue.bds_to_write_back
  ==>
  channel2.queue.bds_to_write_back = channel3.queue.bds_to_write_back
Proof
INTRO_TAC THEN
ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL THEN
SPLIT_ASM_DISJS_TAC THENL
[
 ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH THEN
 ETAC operationsTheory.APPENDED_BDS THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 ETAC operationsTheory.NOT_EXTENDED_ABSTRACT_BDS_TO_FETCH_AND_UNCHANGED_CHANNEL THEN
 STAC
]
QED

Theorem EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL_PRESERVES_PENDING_ACCESSES_LEMMA:
!channel1 channel2 channel3 bds_to_fetch.
  EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL channel1 channel2 bds_to_fetch /\
  channel1.pending_accesses = channel3.pending_accesses
  ==>
  channel2.pending_accesses = channel3.pending_accesses
Proof
INTRO_TAC THEN
ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH_OR_PRESERVED_CHANNEL THEN
SPLIT_ASM_DISJS_TAC THENL
[
 ETAC operationsTheory.EXTENDED_ABSTRACT_BDS_TO_FETCH THEN
 ETAC operationsTheory.APPENDED_BDS THEN
 LRTAC THEN
 RECORD_TAC THEN
 STAC
 ,
 ETAC operationsTheory.NOT_EXTENDED_ABSTRACT_BDS_TO_FETCH_AND_UNCHANGED_CHANNEL THEN
 STAC
]
QED

Theorem UPDATING_CHANNEL_ZERO_IMPLIES_DEFINED_PRESERVED_CHANNELS_ZERO_LEMMA:
!channels1 channels2 channel.
  channels2 = (0w =+ SOME channel) channels1
  ==>
  DEFINED_PRESERVED_CHANNELS channels1 channels2 0w
Proof
INTRO_TAC THEN
PTAC DEFINED_PRESERVED_CHANNELS THEN
LRTAC THEN
CONJS_TAC THENL
[
 INTRO_TAC THEN
 ETAC wordsTheory.WORD_LS_word_0 THEN
 LRTAC THEN
 ETAC combinTheory.UPDATE_def THEN
 APP_SCALAR_TAC THEN
 REWRITE_TAC [optionTheory.IS_SOME_DEF]
 ,
 INTRO_TAC THEN
 ETAC wordsTheory.WORD_HIGHER THEN
 ETAC wordsTheory.WORD_LO_word_0 THEN
 ETAC combinTheory.UPDATE_def THEN
 APP_SCALAR_TAC THEN
 RW_HYP_LEMMA_TAC boolTheory.EQ_SYM_EQ THEN
 ASM_REWRITE_TAC [optionTheory.IS_SOME_DEF]
]
QED

Theorem UPDATING_ACCESSED_CHANNEL_AND_PRESERVED_CHANNELS_IMPLIES_SAME_CHANNELS_LEMMA:
!channels channels2 channels1 channel1 channel2 channel1' channel2' n channel_id channel_id'.
  SUC n < dimword (: 'b) /\
  PRESERVED_CHANNELS channels channels2 (n2w n) /\
  channel_id = (n2w n + 1w : 'b word) /\
  channel_id' = (n2w n + 1w) /\
  channels = (channel_id =+ SOME channel2) channels1 /\
  channel1 = THE (channels1 channel_id) /\
  channel1' = THE (channels1 channel_id') /\
  channel2' = THE (channels2 channel_id')
  ==>
  channel1' = channel1 /\
  channel2' = channel2
Proof
INTRO_TAC THEN
ETAC PRESERVED_CHANNELS THEN
ALL_LRTAC THEN
REWRITE_TAC [] THEN
AIRTAC THEN
IRTAC word_lemmasTheory.EQ_SUC_IMPLIES_GT_LEMMA THEN
REPEAT (WEAKEN_TAC is_forall) THEN
AITAC THEN
LRTAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
REWRITE_TAC [optionTheory.THE_DEF]
QED

Theorem PRESERVED_CHANNELS_IMPLIES_NEXT_INDEX_LEMMA:
!n channels channels2 channels1 channel.
  SUC n < dimword (: 'a) /\
  channels = ((n2w n + 1w) =+ channel) channels1 /\
  PRESERVED_CHANNELS channels channels2 (n2w n : 'a word)
  ==>
  PRESERVED_CHANNELS channels1 channels2 (n2w n + 1w)
Proof
INTRO_TAC THEN
ETAC PRESERVED_CHANNELS THEN
CONJS_TAC THENL
[
 INTRO_TAC THEN
 LRTAC THEN
 ITAC word_lemmasTheory.GT_SUC_IMPLIES_GT_LEMMA THEN
 AITAC THEN
 LRTAC THEN
 ETAC combinTheory.UPDATE_def THEN
 APP_SCALAR_TAC THEN
 ETAC wordsTheory.WORD_HIGHER THEN
 IRTAC wordsTheory.WORD_LOWER_NOT_EQ THEN
 IRTAC wordsTheory.WORD_LOWER_NOT_EQ THEN
 STAC
]
QED

Theorem APPEND_BDS_CHANNEL_ZERO_PRESERVED_CHANNELS_LEMMA:
!channels1 channels2 channel.
  channels2 = (0w =+ SOME channel) channels1
  ==>
  PRESERVED_CHANNELS channels1 channels2 0w
Proof
INTRO_TAC THEN
PTAC PRESERVED_CHANNELS THEN
INTRO_TAC THEN
LRTAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
ETAC wordsTheory.WORD_HIGHER THEN
ETAC wordsTheory.WORD_LO_word_0 THEN
RW_HYP_LEMMA_TAC boolTheory.EQ_SYM_EQ THEN
STAC
QED










Theorem APPENDED_REPLY_REMOVED_REQUEST_CHANNEL_TRANSFERS_ABSTRACT_CONCRETE_BDS_TO_FETCH_EQ_LEMMA:
!device_characteristics device11 device21 device12 device22 serviced_request channel_id memory internal_state.
  (schannel device11 channel_id).queue.bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state /\
  APPENDED_REPLY_REMOVED_REQUEST_CHANNEL (schannel device11 channel_id) (schannel device12 channel_id) serviced_request /\
  APPENDED_REPLY_REMOVED_REQUEST_CHANNEL (schannel device21 channel_id) (schannel device22 channel_id) serviced_request
  ==>
  (schannel device12 channel_id).queue.bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state
Proof
INTRO_TAC THEN
ETAC operationsTheory.APPENDED_REPLY_REMOVED_REQUEST_CHANNEL THEN
ETAC operationsTheory.append_reply_remove_request_channel THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem APPENDED_REPLY_REMOVED_REQUEST_CHANNEL_TRANSFERS_BDS_TO_UPDATE_EQ_LEMMA:
!device11 device21 device12 device22 serviced_request channel_id.
 (schannel device11 channel_id).queue.bds_to_update = (schannel device21 channel_id).queue.bds_to_update /\
  APPENDED_REPLY_REMOVED_REQUEST_CHANNEL (schannel device11 channel_id) (schannel device12 channel_id) serviced_request /\
  APPENDED_REPLY_REMOVED_REQUEST_CHANNEL (schannel device21 channel_id) (schannel device22 channel_id) serviced_request
  ==>
  (schannel device12 channel_id).queue.bds_to_update = (schannel device22 channel_id).queue.bds_to_update
Proof
INTRO_TAC THEN
ETAC operationsTheory.APPENDED_REPLY_REMOVED_REQUEST_CHANNEL THEN
LRTAC THEN
LRTAC THEN
ETAC operationsTheory.append_reply_remove_request_channel THEN
RECORD_TAC THEN
STAC
QED

Theorem APPENDED_REPLY_REMOVED_REQUEST_CHANNEL_TRANSFERS_BDS_TO_PROCESS_EQ_LEMMA:
!device11 device21 device12 device22 serviced_request channel_id.
 (schannel device11 channel_id).queue.bds_to_process = (schannel device21 channel_id).queue.bds_to_process /\
  APPENDED_REPLY_REMOVED_REQUEST_CHANNEL (schannel device11 channel_id) (schannel device12 channel_id) serviced_request /\
  APPENDED_REPLY_REMOVED_REQUEST_CHANNEL (schannel device21 channel_id) (schannel device22 channel_id) serviced_request
  ==>
  (schannel device12 channel_id).queue.bds_to_process = (schannel device22 channel_id).queue.bds_to_process
Proof
INTRO_TAC THEN
ETAC operationsTheory.APPENDED_REPLY_REMOVED_REQUEST_CHANNEL THEN
LRTAC THEN
LRTAC THEN
ETAC operationsTheory.append_reply_remove_request_channel THEN
RECORD_TAC THEN
STAC
QED

Theorem APPENDED_REPLY_REMOVED_REQUEST_CHANNEL_TRANSFERS_BDS_TO_WRITE_BACK_EQ_LEMMA:
!device11 device21 device12 device22 serviced_request channel_id.
 (schannel device11 channel_id).queue.bds_to_write_back = (schannel device21 channel_id).queue.bds_to_write_back /\
  APPENDED_REPLY_REMOVED_REQUEST_CHANNEL (schannel device11 channel_id) (schannel device12 channel_id) serviced_request /\
  APPENDED_REPLY_REMOVED_REQUEST_CHANNEL (schannel device21 channel_id) (schannel device22 channel_id) serviced_request
  ==>
  (schannel device12 channel_id).queue.bds_to_write_back = (schannel device22 channel_id).queue.bds_to_write_back
Proof
INTRO_TAC THEN
ETAC operationsTheory.APPENDED_REPLY_REMOVED_REQUEST_CHANNEL THEN
LRTAC THEN
LRTAC THEN
ETAC operationsTheory.append_reply_remove_request_channel THEN
RECORD_TAC THEN
STAC
QED

Theorem APPENDED_REPLY_REMOVED_REQUEST_CHANNEL_TRANSFERS_PENDING_ACCESSES_LEMMA:
!channel11 channel21 channel12 channel22 serviced_request .
  APPENDED_REPLY_REMOVED_REQUEST_CHANNEL channel11 channel12 serviced_request /\
  APPENDED_REPLY_REMOVED_REQUEST_CHANNEL channel21 channel22 serviced_request /\
  channel21.pending_accesses = channel11.pending_accesses
  ==>
  channel12.pending_accesses = channel22.pending_accesses
Proof
INTRO_TAC THEN
ETAC operationsTheory.APPENDED_REPLY_REMOVED_REQUEST_CHANNEL THEN
REPEAT (PTAC operationsTheory.append_reply_remove_request_channel) THEN
RLTAC THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem APPEND_REPLY_REMOVED_REQUEST_CHANNEL_PRESERVES_QUEUE_LEMMA:
!channel1 channel2 serviced_request.
  APPENDED_REPLY_REMOVED_REQUEST_CHANNEL channel1 channel2 serviced_request
  ==>
  channel1.queue = channel2.queue
Proof
INTRO_TAC THEN
PTAC operationsTheory.APPENDED_REPLY_REMOVED_REQUEST_CHANNEL THEN
PTAC operationsTheory.append_reply_remove_request_channel THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED



Theorem UPDATE_DEVICE_STATE_IMPLIES_PENDING_REGISTER_RELEATED_MEMORY_REQUESTS_IN_POST_STATE_LEMMA:
!device1 device2 channel_id internal_state2 channel2.
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  LIST1_IN_LIST2 device2.dma_state.pending_register_related_memory_requests device1.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
PTAC operationsTheory.update_device_state THEN
LRTAC THEN
PTAC listsTheory.LIST1_IN_LIST2 THEN
RECORD_TAC THEN
ETAC listTheory.EVERY_MEM THEN
APP_SCALAR_TAC THEN
REWRITE_TAC [boolTheory.IMP_CLAUSES]
QED

Theorem INTERNAL_STATE_EQ_IMPLIES_SCRATCHPAD_ADDRESSES_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type).
  device2.dma_state.internal_state = device1.dma_state.internal_state
  ==>
  SCRATCHPAD_ADDRESSES_EQ device_characteristics device1.dma_state.internal_state device2.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC stateTheory.SCRATCHPAD_ADDRESSES_EQ THEN
STAC
QED

Theorem REMOVE_PENDING_REQUEST_IMPLIES_LIST1_IN_LIST2_LEMMA:
!pending_requests1 pending_requests2 serviced_request.
  pending_requests2 = remove_pending_request serviced_request pending_requests1
  ==>
  LIST1_IN_LIST2 pending_requests2 pending_requests1
Proof
INTRO_TAC THEN
PTAC operationsTheory.remove_pending_request THEN
LRTAC THEN
PTAC listsTheory.LIST1_IN_LIST2 THEN
ETAC listTheory.EVERY_MEM THEN
APP_SCALAR_TAC THEN
INTRO_TAC THEN
ETAC listTheory.MEM_FILTER THEN
STAC
QED

Theorem PENDING_REGISTER_RELATED_MEMORY_REQUEST_IMPLIES_NOT_IDLE_DMAC_OR_PENDING_MEMORY_REQUEST_LEMMA:
!device_characteristics device request.
  MEM request device.dma_state.pending_register_related_memory_requests
  ==>
  DMAC_CAN_ACCESS_MEMORY device_characteristics device
Proof
INTRO_TAC THEN
PTAC DMAC_CAN_ACCESS_MEMORY THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
PTAC NO_REGISTER_RELATED_MEMORY_REQUEST THEN
CCONTR_TAC THEN
ETAC boolTheory.NOT_CLAUSES THEN
LRTAC THEN
ETAC listTheory.MEM THEN
STAC
QED



Theorem UPDATING_SOME_STATE_PRESERVES_DEFINED_CHANNELS_LEMMA:
!device_characteristics channel_id device1 device2 internal_state channel.
  device2 = update_device_state device1 channel_id internal_state channel /\
  DEFINED_CHANNELS device_characteristics device1
  ==>
  DEFINED_CHANNELS device_characteristics device2
Proof
INTRO_TAC THEN
ETAC stateTheory.DEFINED_CHANNELS THEN
ETAC stateTheory.VALID_CHANNELS THEN
INTRO_TAC THEN
PTAC operationsTheory.update_device_state THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [combinTheory.UPDATE_def] THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 REWRITE_TAC [optionTheory.IS_SOME_DEF]
 ,
 AITAC THEN
 STAC
]
QED

Theorem COLLECT_DMA_STATE_CHANNELS_TO_PIPELINES_INTERNAL_STATE_IMPLIES_PIPELINES_EQ_LEMMA:
!pipelines1 pipelines2 pending_register_memory_accesses device_characteristics
 device1 device2 channel1 channel_id internal_state1.
  (pipelines1, pending_register_memory_accesses) = collect_dma_state device_characteristics.dma_characteristics device1.dma_state /\
  device2 = device1 with dma_state := device1.dma_state with internal_state := internal_state1 /\
  channel1 = schannel device1 channel_id /\
  pipelines2 = collect_channels_state device_characteristics.dma_characteristics device2.dma_state.channels
  ==>
  pipelines1 = pipelines2
Proof
INTRO_TAC THEN
ETAC operationsTheory.collect_dma_state THEN
LRTAC THEN
RECORD_TAC THEN
LETS_TAC THEN
EQ_PAIR_ASM_TAC THEN
STAC
QED

Theorem SCHEDULER_DMA_OPERATION_EQ_INTERNAL_DMA_OPERATION_LEMMA:
scheduler_dma_operation = internal_dma_operation
Proof
REWRITE_TAC [boolTheory.FUN_EQ_THM] THEN
REPEAT GEN_TAC THEN
PTAC scheduler_dma_operation THEN
ETAC scheduler_operation THEN
ETAC operationsTheory.internal_dma_operation THEN
ONCE_LETS_TAC THEN
RLTAC THEN
ONCE_LETS_ASM_TAC THEN
ONCE_LETS_TAC THEN
RLTAC THEN
ONCE_LETS_ASM_TAC THEN
ONCE_LETS_TAC THEN
RLTAC THEN
ONCE_LETS_ASM_TAC THEN
ONCE_LETS_TAC THEN
ONCE_LETS_ASM_TAC THEN
ONCE_LETS_TAC THEN
LRTAC THEN
ONCE_LETS_ASM_TAC THEN
ONCE_LETS_ASM_TAC THEN
LRTAC THEN
ONCE_LETS_TAC THEN
ONCE_LETS_TAC THEN
ETAC dma_operation THEN
ONCE_LETS_ASM_TAC THEN
LETS_TAC THEN
RLTAC THEN
LRTAC THEN
LRTAC THEN
LRTAC THEN
LRTAC THEN
LRTAC THEN
LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
LRTAC THEN
EQ_PAIR_ASM_TAC THEN
LRTAC THEN
LRTAC THEN
REWRITE_TAC [operationsTheory.update_device_state] THEN
RECORD_TAC THEN
REWRITE_TAC []
QED

Theorem MEM_APPENDED_CHANNEL2_BDS_TO_FETCH_IMPLIES_MEM_CHANNEL1_BDS_TO_FETCH_OR_APPENDED_BDS_LEMMA:
!bd channel1 channel2 appended_bds.
  MEM bd channel2.queue.bds_to_fetch /\
  channel2 = channel1 with queue := channel1.queue with bds_to_fetch := channel1.queue.bds_to_fetch ++ appended_bds
  ==>
  MEM bd channel1.queue.bds_to_fetch \/
  MEM bd appended_bds
Proof
INTRO_TAC THEN
LRTAC THEN
RECORD_TAC THEN
ETAC listTheory.MEM_APPEND THEN
STAC
QED



Theorem APPEND_REPLY_REMOVE_REQUEST_UPDATING_BD_PRESERVES_PENDING_ACCESSES_REPLIES_FETCHING_BD_LEMMA:
!pending_accesses serviced_request.
  (append_reply_remove_request_updating_bd serviced_request pending_accesses).replies.fetching_bd =
  pending_accesses.replies.fetching_bd
Proof
REPEAT GEN_TAC THEN
ETAC operationsTheory.append_reply_remove_request_updating_bd THEN
IF_SPLIT_TAC THEN RECORD_TAC THEN STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_TRANSFERRING_DATA_PRESERVES_PENDING_ACCESSES_REPLIES_FETCHING_BD_LEMMA:
!pending_accesses serviced_request.
  (append_reply_remove_request_transferring_data serviced_request pending_accesses).replies.fetching_bd =
  pending_accesses.replies.fetching_bd
Proof
REPEAT GEN_TAC THEN
ETAC operationsTheory.append_reply_remove_request_transferring_data THEN
IF_SPLIT_TAC THEN RECORD_TAC THEN STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_WRITING_BACK_BD_PRESERVES_PENDING_ACCESSES_REPLIES_FETCHING_BD_LEMMA:
!pending_accesses serviced_request.
  (append_reply_remove_request_writing_back_bd serviced_request pending_accesses).replies.fetching_bd =
  pending_accesses.replies.fetching_bd
Proof
REPEAT GEN_TAC THEN
ETAC operationsTheory.append_reply_remove_request_writing_back_bd THEN
IF_SPLIT_TAC THEN RECORD_TAC THEN STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_CHANNEL_MATCHES_OR_PRESERVES_FETCHING_BD_REPLY_LEMMA:
!device1 device2 channel_id address_bytes tag.
  schannel device2 channel_id = append_reply_remove_request_channel (MAP SND address_bytes, request_read (MAP FST address_bytes) tag) (schannel device1 channel_id)
  ==>
  ((schannel device2 channel_id).pending_accesses.replies.fetching_bd = SOME (MAP SND address_bytes, tag) /\
   (schannel device1 channel_id).pending_accesses.requests.fetching_bd = SOME (request_read (MAP FST address_bytes) tag)) \/
  ((schannel device2 channel_id).pending_accesses.replies.fetching_bd =
   (schannel device1 channel_id).pending_accesses.replies.fetching_bd)
Proof
INTRO_TAC THEN
PTAC operationsTheory.append_reply_remove_request_channel THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.append_reply_remove_request_operation THEN
LRTAC THEN
RECORD_TAC THEN
ETAC operationsTheory.append_reply_remove_request_fetching_bd THEN
IF_SPLIT_TAC THEN RECORD_TAC THENL
[
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
 REWRITE_TAC [APPEND_REPLY_REMOVE_REQUEST_WRITING_BACK_BD_PRESERVES_PENDING_ACCESSES_REPLIES_FETCHING_BD_LEMMA] THEN
 REWRITE_TAC [APPEND_REPLY_REMOVE_REQUEST_TRANSFERRING_DATA_PRESERVES_PENDING_ACCESSES_REPLIES_FETCHING_BD_LEMMA] THEN
 REWRITE_TAC [APPEND_REPLY_REMOVE_REQUEST_UPDATING_BD_PRESERVES_PENDING_ACCESSES_REPLIES_FETCHING_BD_LEMMA] THEN
 PTAC operationsTheory.fetching_bd_request_served THEN TRY SOLVE_F_ASM_TAC THEN
 PTAC operationsTheory.serviced_request_to_reply THEN
 ALL_LRTAC THEN
 RECORD_TAC THEN
 REWRITE_TAC [] THEN
 EXISTS_EQ_TAC
 ,
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 REWRITE_TAC [APPEND_REPLY_REMOVE_REQUEST_WRITING_BACK_BD_PRESERVES_PENDING_ACCESSES_REPLIES_FETCHING_BD_LEMMA] THEN
 REWRITE_TAC [APPEND_REPLY_REMOVE_REQUEST_TRANSFERRING_DATA_PRESERVES_PENDING_ACCESSES_REPLIES_FETCHING_BD_LEMMA] THEN
 REWRITE_TAC [APPEND_REPLY_REMOVE_REQUEST_UPDATING_BD_PRESERVES_PENDING_ACCESSES_REPLIES_FETCHING_BD_LEMMA]
]
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_UPDATING_BD_PRESERVES_PENDING_ACCESSES_REQUESTS_FETCHING_BD_LEMMA:
!pending_accesses serviced_request.
  (append_reply_remove_request_updating_bd serviced_request pending_accesses).requests.fetching_bd =
  pending_accesses.requests.fetching_bd
Proof
REPEAT GEN_TAC THEN
ETAC operationsTheory.append_reply_remove_request_updating_bd THEN
IF_SPLIT_TAC THEN RECORD_TAC THEN STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_TRANSFERRING_DATA_PRESERVES_PENDING_ACCESSES_REQUESTS_FETCHING_BD_LEMMA:
!pending_accesses serviced_request.
  (append_reply_remove_request_transferring_data serviced_request pending_accesses).requests.fetching_bd =
  pending_accesses.requests.fetching_bd
Proof
REPEAT GEN_TAC THEN
ETAC operationsTheory.append_reply_remove_request_transferring_data THEN
IF_SPLIT_TAC THEN RECORD_TAC THEN STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_WRITING_BACK_BD_PRESERVES_PENDING_ACCESSES_REQUESTS_FETCHING_BD_LEMMA:
!pending_accesses serviced_request.
  (append_reply_remove_request_writing_back_bd serviced_request pending_accesses).requests.fetching_bd =
  pending_accesses.requests.fetching_bd
Proof
REPEAT GEN_TAC THEN
ETAC operationsTheory.append_reply_remove_request_writing_back_bd THEN
IF_SPLIT_TAC THEN RECORD_TAC THEN STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_CHANNEL_PRESERVES_OR_REMOVES_FETCHING_BD_REQUEST_LEMMA:
!device1 device2 channel_id serviced_request.
  schannel device2 channel_id = append_reply_remove_request_channel serviced_request (schannel device1 channel_id)
  ==>
  (schannel device2 channel_id).pending_accesses.requests.fetching_bd =
  (schannel device1 channel_id).pending_accesses.requests.fetching_bd \/
  (schannel device2 channel_id).pending_accesses.requests.fetching_bd = NONE
Proof
INTRO_TAC THEN
PTAC operationsTheory.append_reply_remove_request_channel THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.append_reply_remove_request_operation THEN
LRTAC THEN
RECORD_TAC THEN
ETAC operationsTheory.append_reply_remove_request_fetching_bd THEN
IF_SPLIT_TAC THEN RECORD_TAC THENL
[
 MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
 REWRITE_TAC [APPEND_REPLY_REMOVE_REQUEST_WRITING_BACK_BD_PRESERVES_PENDING_ACCESSES_REQUESTS_FETCHING_BD_LEMMA] THEN
 REWRITE_TAC [APPEND_REPLY_REMOVE_REQUEST_TRANSFERRING_DATA_PRESERVES_PENDING_ACCESSES_REQUESTS_FETCHING_BD_LEMMA] THEN
 REWRITE_TAC [APPEND_REPLY_REMOVE_REQUEST_UPDATING_BD_PRESERVES_PENDING_ACCESSES_REQUESTS_FETCHING_BD_LEMMA] THEN
 RECORD_TAC THEN
 STAC
 ,
 MATCH_MP_TAC boolTheory.OR_INTRO_THM1 THEN
 REWRITE_TAC [APPEND_REPLY_REMOVE_REQUEST_WRITING_BACK_BD_PRESERVES_PENDING_ACCESSES_REQUESTS_FETCHING_BD_LEMMA] THEN
 REWRITE_TAC [APPEND_REPLY_REMOVE_REQUEST_TRANSFERRING_DATA_PRESERVES_PENDING_ACCESSES_REQUESTS_FETCHING_BD_LEMMA] THEN
 REWRITE_TAC [APPEND_REPLY_REMOVE_REQUEST_UPDATING_BD_PRESERVES_PENDING_ACCESSES_REQUESTS_FETCHING_BD_LEMMA]
]
QED

Theorem LIST1_IN_LIST2_PRESERVES_REQUEST_TO_WRITE_ADDRESSES_LEMMA:
!requests requests_was previous_requests previous_requests_was request_was.
  requests_was = MAP request_to_write_addresses requests /\
  MEM request_was requests_was /\
  LIST1_IN_LIST2 requests previous_requests /\
  previous_requests_was = MAP request_to_write_addresses previous_requests
  ==>
  MEM request_was previous_requests_was
Proof
INTRO_TAC THEN
ALL_LRTAC THEN
ETAC listTheory.MEM_MAP THEN
AXTAC THEN
IRTAC lists_lemmasTheory.LIST1_IN_LIST2_MEM_LIST1_IMPLIES_MEM_LIST2_LEMMA THEN
PAXTAC THEN
STAC
QED

Theorem REQUEST_WAS_IN_REQUESTS_WAS_LEMMA:
!requests requests_was address_bytes tag request_was.
  requests_was = MAP request_to_write_addresses requests /\
  MEM (request_write address_bytes tag) requests /\
  request_was = MAP FST address_bytes
  ==>
  MEM request_was requests_was
Proof
Induct THEN TRY (REWRITE_TAC [listTheory.MEM]) THEN
INTRO_TAC THEN
SPLIT_ASM_DISJS_TAC THENL
[
 RLTAC THEN
 ALL_LRTAC THEN
 ETAC listTheory.MAP THEN
 ETAC operationsTheory.request_to_write_addresses THEN
 ETAC listTheory.MEM THEN
 STAC
 ,
 ETAC listTheory.MAP THEN
 AIRTAC THEN
 LRTAC THEN
 ETAC listTheory.MEM THEN
 STAC
]
QED

Theorem REQUEST_WAS_EMPTY_OR_WRITE_REQUEST_LEMMA:
!requests requests_was request_was.
  requests_was = MAP request_to_write_addresses requests /\
  MEM request_was requests_was
  ==>
  request_was = [] \/
  ?address_bytes tag.
    MEM (request_write address_bytes tag) requests /\
    MAP FST address_bytes = request_was
Proof
Induct THENL
[
 INTRO_TAC THEN ETAC listTheory.MAP THEN LRTAC THEN ETAC listTheory.MEM THEN SOLVE_F_ASM_TAC
 ,
 INTRO_TAC THEN
 ETAC listTheory.MAP THEN
 LRTAC THEN
 ETAC listTheory.MEM THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  PTAC operationsTheory.request_to_write_addresses THEN TRY STAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  PAXTAC THEN
  ASM_REWRITE_TAC [listTheory.MEM]
  ,
  AIRTAC THEN
  SPLIT_ASM_DISJS_TAC THEN TRY STAC THEN
  MATCH_MP_TAC boolTheory.OR_INTRO_THM2 THEN
  REWRITE_TAC [listTheory.MEM] THEN
  AXTAC THEN
  PAXTAC THEN
  STAC
 ]
]
QED

Theorem WRITE_REQUEST_IN_REQUEST_WRITE_ADDRESSES_LEMMA:
!request_was address_bytes requests tag.
  request_was = MAP FST address_bytes /\
  MEM (request_write address_bytes tag) requests
  ==>
  ?requests_was.
     requests_was = MAP request_to_write_addresses requests /\
     MEM request_was requests_was
Proof
INTRO_TAC THEN
EXISTS_EQ_TAC THEN
IRTAC REQUEST_WAS_IN_REQUESTS_WAS_LEMMA THEN
STAC
QED



Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_BD_TRANSFER_RAS_WAS_LEMMA:
!device_characteristics device1 device2.
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_BD_INTERPRETATION device_characteristics /\
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1
  ==>
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    !bd.
      (cverification device_characteristics channel_id).bd_transfer_ras_was device2.dma_state.internal_state bd =
      (cverification device_characteristics channel_id).bd_transfer_ras_was device1.dma_state.internal_state bd
Proof
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_BD_INTERPRETATION THEN
PTAC operationsTheory.process_register_related_memory_access THEN
LRTAC THEN
RECORD_TAC THEN
AIRTAC THEN
INTRO_TAC THEN
AIRTAC THEN
RLTAC THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_IMPLIES_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_LEMMA:
!device_characteristics device1 device2.
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1
  ==>
  ?processed_replies.
    (device2.dma_state.internal_state, processed_replies) = device_characteristics.dma_characteristics.process_register_related_memory_replies device1.dma_state.internal_state device1.dma_state.pending_register_related_memory_requests device1.dma_state.pending_register_related_memory_replies
Proof
INTRO_TAC THEN
PTAC operationsTheory.process_register_related_memory_access THEN
LRTAC THEN
RECORD_TAC THEN
PAXTAC THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_BDS_TO_FETCH_LEMMA:
!device_characteristics device1 device2.
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLY_PRESERVES_BDS_TO_FETCH device_characteristics /\
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1
  ==>
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    !memory.
      (cverification device_characteristics channel_id).bds_to_fetch memory device2.dma_state.internal_state =
      (cverification device_characteristics channel_id).bds_to_fetch memory device1.dma_state.internal_state
Proof
INTRO_TAC THEN
INTRO_TAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLY_PRESERVES_BDS_TO_FETCH THEN
IRTAC PROCESS_REGISTER_RELATED_MEMORY_ACCESS_IMPLIES_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_LEMMA THEN
AXTAC THEN
AIRTAC THEN
AIRTAC THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_CHANNELS_LEMMA:
!device_characteristics device1 device2.
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1
  ==>
  device2.dma_state.channels = device1.dma_state.channels
Proof
INTRO_TAC THEN
PTAC operationsTheory.process_register_related_memory_access THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_SCRATCHPAD_ADDRESSES_LEMMA:
!device_characteristics device1 device2.
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_SCRATCHPAD device_characteristics /\
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1
  ==>
  device_characteristics.dma_characteristics.scratchpad_addresses device2.dma_state.internal_state =
  device_characteristics.dma_characteristics.scratchpad_addresses device1.dma_state.internal_state
Proof
INTRO_TAC THEN
IRTAC PROCESS_REGISTER_RELATED_MEMORY_ACCESS_IMPLIES_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_LEMMA THEN
AXTAC THEN
PTAC proof_obligationsTheory.PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_PRESERVES_SCRATCHPAD THEN
AIRTAC THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA:
!device_characteristics device1 device2.
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1
  ==>
  device2.dma_state.pending_register_related_memory_requests = device1.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
PTAC operationsTheory.process_register_related_memory_access THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem PROCESS_REGISTER_RELATED_MEMORY_ACCESS_PRESERVES_FETCH_BD_ADDRESSES_LEMMA:
!device_characteristics device1 device2.
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_REPLIES_PRESERVES_FETCH_BD_ADDRESSES device_characteristics /\
  device2 = process_register_related_memory_access device_characteristics.dma_characteristics device1
  ==>
  !channel_id.
    VALID_CHANNEL_ID device_characteristics channel_id
    ==>
    (coperation device_characteristics channel_id).fetch_bd_addresses device2.dma_state.internal_state =
    (coperation device_characteristics channel_id).fetch_bd_addresses device1.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_REPLIES_PRESERVES_FETCH_BD_ADDRESSES THEN
IRTAC PROCESS_REGISTER_RELATED_MEMORY_ACCESS_IMPLIES_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_LEMMA THEN
AXTAC THEN
AIRTAC THEN
STAC
QED

Theorem UPDATE_DEVICE_STATE_UPDATES_CHANNEL_LEMMA:
!device1 device2 channel_id internal_state2 channel2.
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  schannel device2 channel_id = channel2
Proof
INTRO_TAC THEN
PTAC operationsTheory.update_device_state THEN
LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
REWRITE_TAC [optionTheory.THE_DEF]
QED

Theorem UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_LEMMA:
!device1 device2 channel_id1 internal_state2 channel2.
  device2 = update_device_state device1 channel_id1 internal_state2 channel2
  ==>
  !channel_id2.
    channel_id2 <> channel_id1
    ==>
    schannel device2 channel_id2 = schannel device1 channel_id2
Proof
INTRO_TAC THEN
INTRO_TAC THEN
PTAC operationsTheory.update_device_state THEN
LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THEN TRY STAC THEN
LRTAC THEN
CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
QED

Theorem UPDATE_INTERNAL_DEVICE_STATE_LEMMA:
!device1 device2 internal_state2 channel2 channel_id.
  device2 = update_device_state device1 channel_id internal_state2 channel2
  ==>
  device2.dma_state.internal_state = internal_state2
Proof
INTRO_TAC THEN
LRTAC THEN
PTAC operationsTheory.update_device_state THEN
RECORD_TAC THEN
STAC
QED

Theorem UPDATE_DEVICE_STATE_CHANNEL_EQ_LEMMA:
!device1 device2 channel_id internal_state channel2.
  device2 = update_device_state device1 channel_id internal_state channel2
  ==>
  channel2 = schannel device2 channel_id
Proof
INTRO_TAC THEN
ETAC operationsTheory.update_device_state THEN
LRTAC THEN
ETAC stateTheory.schannel THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
REWRITE_TAC [optionTheory.THE_DEF]
QED

Theorem UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_PENDING_ACCESSES_REPLIES_FETCHING_BD_LEMMA:
!device1 device2 channel_id channel_id' internal_state2 channel2.
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  channel_id <> channel_id'
  ==>
  (schannel device2 channel_id').pending_accesses.replies.fetching_bd =
  (schannel device1 channel_id').pending_accesses.replies.fetching_bd
Proof
INTRO_TAC THEN
ETAC stateTheory.schannel THEN
LRTAC THEN
ETAC operationsTheory.update_device_state THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
ASM_REWRITE_TAC []
QED

Theorem UPDATE_DEVICE_STATE_PRESERVES_OTHER_CHANNELS_PENDING_ACCESSES_REQUESTS_FETCHING_BD_LEMMA:
!device1 device2 channel_id channel_id' internal_state2 channel2.
  device2 = update_device_state device1 channel_id internal_state2 channel2 /\
  channel_id <> channel_id'
  ==>
  (schannel device2 channel_id').pending_accesses.requests.fetching_bd =
  (schannel device1 channel_id').pending_accesses.requests.fetching_bd
Proof
INTRO_TAC THEN
ETAC stateTheory.schannel THEN
LRTAC THEN
ETAC operationsTheory.update_device_state THEN
RECORD_TAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
ASM_REWRITE_TAC []
QED

val _ = export_theory();
