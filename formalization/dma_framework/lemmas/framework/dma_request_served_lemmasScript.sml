open HolKernel Parse boolLib bossLib helper_tactics;
open operationsTheory;
open read_propertiesTheory;

val _ = new_theory "dma_request_served_lemmas";

Theorem APPEND_REPLY_REMOVE_REQUEST_FETCHING_BD_NOT_EXPANDING_PENDING_ACCESSES_LEMMA:
!pending_accesses1 pending_accesses2 serviced_request.
  pending_accesses2 = append_reply_remove_request_fetching_bd serviced_request pending_accesses1
  ==>
  (!request. pending_accesses2.requests.fetching_bd = SOME request ==> pending_accesses1.requests.fetching_bd = SOME request) /\
  (!request. MEM request pending_accesses2.requests.updating_bd ==> MEM request pending_accesses1.requests.updating_bd) /\
  (!request. MEM request pending_accesses2.requests.transferring_data ==> MEM request pending_accesses1.requests.transferring_data) /\
  (!request. MEM request pending_accesses2.requests.writing_back_bd ==> MEM request pending_accesses1.requests.writing_back_bd)
Proof
INTRO_TAC THEN
PTAC append_reply_remove_request_fetching_bd THEN
REPEAT CONJ_TAC THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [optionTheory.NOT_NONE_SOME]
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_FETCHING_BD_NOT_EXPANDING_FETCHING_BD_REQUESTS_LEMMA:
!requests_fetching_bd pending_accesses serviced_request.
  requests_fetching_bd = (append_reply_remove_request_fetching_bd serviced_request pending_accesses).requests.fetching_bd
  ==>
  (!request. requests_fetching_bd = SOME request ==> pending_accesses.requests.fetching_bd = SOME request)
Proof
INTRO_TAC THEN
PTAC append_reply_remove_request_fetching_bd THEN
RECORD_TAC THEN
ASM_REWRITE_TAC [optionTheory.NOT_NONE_SOME, boolTheory.IMP_CLAUSES]
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_FETCHING_BD_NOT_EXPANDING_UPDATING_BD_REQUESTS_LEMMA:
!requests_updating_bd pending_accesses serviced_request.
  requests_updating_bd = (append_reply_remove_request_fetching_bd serviced_request pending_accesses).requests.updating_bd
  ==>
  (!request. MEM request requests_updating_bd ==> MEM request pending_accesses.requests.updating_bd)
Proof
INTRO_TAC THEN
PTAC append_reply_remove_request_fetching_bd THEN
RECORD_TAC THEN
ASM_REWRITE_TAC [boolTheory.IMP_CLAUSES]
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_FETCHING_BD_NOT_EXPANDING_TRANSFERRING_DATA_REQUESTS_LEMMA:
!requests_transferring_data pending_accesses serviced_request.
  requests_transferring_data = (append_reply_remove_request_fetching_bd serviced_request pending_accesses).requests.transferring_data
  ==>
  (!request. MEM request requests_transferring_data ==> MEM request pending_accesses.requests.transferring_data)
Proof
INTRO_TAC THEN
PTAC append_reply_remove_request_fetching_bd THEN
RECORD_TAC THEN
ASM_REWRITE_TAC [boolTheory.IMP_CLAUSES]
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_FETCHING_BD_NOT_EXPANDING_WRITING_BACK_BD_REQUESTS_LEMMA:
!requests_writing_back_bd pending_accesses serviced_request.
  requests_writing_back_bd = (append_reply_remove_request_fetching_bd serviced_request pending_accesses).requests.writing_back_bd
  ==>
  (!request. MEM request requests_writing_back_bd ==> MEM request pending_accesses.requests.writing_back_bd)
Proof
INTRO_TAC THEN
PTAC append_reply_remove_request_fetching_bd THEN
RECORD_TAC THEN
ASM_REWRITE_TAC [boolTheory.IMP_CLAUSES]
QED












Theorem APPEND_REPLY_REMOVE_REQUEST_UPDATING_BD_NOT_EXPANDING_PENDING_ACCESSES_LEMMA:
!pending_accesses1 pending_accesses2 serviced_request.
  pending_accesses2 = append_reply_remove_request_updating_bd serviced_request pending_accesses1
  ==>
  (!request. pending_accesses2.requests.fetching_bd = SOME request ==> pending_accesses1.requests.fetching_bd = SOME request) /\
  (!request. MEM request pending_accesses2.requests.updating_bd ==> MEM request pending_accesses1.requests.updating_bd) /\
  (!request. MEM request pending_accesses2.requests.transferring_data ==> MEM request pending_accesses1.requests.transferring_data) /\
  (!request. MEM request pending_accesses2.requests.writing_back_bd ==> MEM request pending_accesses1.requests.writing_back_bd)
Proof
INTRO_TAC THEN
PTAC append_reply_remove_request_updating_bd THEN
REPEAT CONJ_TAC THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [boolTheory.IMP_CLAUSES] THEN
INTRO_TAC THEN
ETAC remove_pending_request THEN
ETAC listTheory.MEM_FILTER THEN
STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_UPDATING_BD_NOT_EXPANDING_FETCHING_BD_REQUESTS_LEMMA:
!requests_fetching_bd pending_accesses serviced_request.
  requests_fetching_bd = (append_reply_remove_request_updating_bd serviced_request pending_accesses).requests.fetching_bd
  ==>
  (!request. requests_fetching_bd = SOME request ==> pending_accesses.requests.fetching_bd = SOME request)
Proof
INTRO_TAC THEN
PTAC append_reply_remove_request_updating_bd THEN
RECORD_TAC THEN
ASM_REWRITE_TAC [optionTheory.NOT_NONE_SOME, boolTheory.IMP_CLAUSES]
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_UPDATING_BD_NOT_EXPANDING_UPDATING_BD_REQUESTS_LEMMA:
!requests_updating_bd pending_accesses serviced_request.
  requests_updating_bd = (append_reply_remove_request_updating_bd serviced_request pending_accesses).requests.updating_bd
  ==>
  (!request. MEM request requests_updating_bd ==> MEM request pending_accesses.requests.updating_bd)
Proof
INTRO_TAC THEN
INTRO_TAC THEN
PTAC append_reply_remove_request_updating_bd THEN
RECORD_TAC THEN
LRTAC THEN
TRY (ETAC remove_pending_request) THEN
TRY (ETAC listTheory.MEM_FILTER) THEN
STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_UPDATING_BD_NOT_EXPANDING_TRANSFERRING_DATA_REQUESTS_LEMMA:
!requests_transferring_data pending_accesses serviced_request.
  requests_transferring_data = (append_reply_remove_request_updating_bd serviced_request pending_accesses).requests.transferring_data
  ==>
  (!request. MEM request requests_transferring_data ==> MEM request pending_accesses.requests.transferring_data)
Proof
INTRO_TAC THEN
INTRO_TAC THEN
PTAC append_reply_remove_request_updating_bd THEN
RECORD_TAC THEN
LRTAC THEN
TRY (ETAC remove_pending_request) THEN
TRY (ETAC listTheory.MEM_FILTER) THEN
STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_UPDATING_BD_NOT_EXPANDING_WRITING_BACK_BD_REQUESTS_LEMMA:
!requests_writing_back_bd pending_accesses serviced_request.
  requests_writing_back_bd = (append_reply_remove_request_updating_bd serviced_request pending_accesses).requests.writing_back_bd
  ==>
  (!request. MEM request requests_writing_back_bd ==> MEM request pending_accesses.requests.writing_back_bd)
Proof
INTRO_TAC THEN
INTRO_TAC THEN
PTAC append_reply_remove_request_updating_bd THEN
RECORD_TAC THEN
LRTAC THEN
TRY (ETAC remove_pending_request) THEN
TRY (ETAC listTheory.MEM_FILTER) THEN
STAC
QED



Theorem APPEND_REPLY_REMOVE_REQUEST_TRANSFERRING_DATA_NOT_EXPANDING_PENDING_ACCESSES_LEMMA:
!pending_accesses1 pending_accesses2 serviced_request.
  pending_accesses2 = append_reply_remove_request_transferring_data serviced_request pending_accesses1
  ==>
  (!request. pending_accesses2.requests.fetching_bd = SOME request ==> pending_accesses1.requests.fetching_bd = SOME request) /\
  (!request. MEM request pending_accesses2.requests.updating_bd ==> MEM request pending_accesses1.requests.updating_bd) /\
  (!request. MEM request pending_accesses2.requests.transferring_data ==> MEM request pending_accesses1.requests.transferring_data) /\
  (!request. MEM request pending_accesses2.requests.writing_back_bd ==> MEM request pending_accesses1.requests.writing_back_bd)
Proof
INTRO_TAC THEN
PTAC append_reply_remove_request_transferring_data THEN
REPEAT CONJ_TAC THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [boolTheory.IMP_CLAUSES] THEN
INTRO_TAC THEN
ETAC remove_pending_request THEN
ETAC listTheory.MEM_FILTER THEN
STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_TRANSFERRING_DATA_NOT_EXPANDING_FETCHING_BD_REQUESTS_LEMMA:
!requests_fetching_bd pending_accesses serviced_request.
  requests_fetching_bd = (append_reply_remove_request_transferring_data serviced_request pending_accesses).requests.fetching_bd
  ==>
  (!request. requests_fetching_bd = SOME request ==> pending_accesses.requests.fetching_bd = SOME request)
Proof
INTRO_TAC THEN
PTAC append_reply_remove_request_transferring_data THEN
RECORD_TAC THEN
ASM_REWRITE_TAC [optionTheory.NOT_NONE_SOME, boolTheory.IMP_CLAUSES]
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_TRANSFERRING_DATA_NOT_EXPANDING_UPDATING_BD_REQUESTS_LEMMA:
!requests_updating_bd pending_accesses serviced_request.
  requests_updating_bd = (append_reply_remove_request_transferring_data serviced_request pending_accesses).requests.updating_bd
  ==>
  (!request. MEM request requests_updating_bd ==> MEM request pending_accesses.requests.updating_bd)
Proof
INTRO_TAC THEN
INTRO_TAC THEN
PTAC append_reply_remove_request_transferring_data THEN
RECORD_TAC THEN
LRTAC THEN
TRY (ETAC remove_pending_request) THEN
TRY (ETAC listTheory.MEM_FILTER) THEN
STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_TRANSFERRING_DATA_NOT_EXPANDING_TRANSFERRING_DATA_REQUESTS_LEMMA:
!requests_transferring_data pending_accesses serviced_request.
  requests_transferring_data = (append_reply_remove_request_transferring_data serviced_request pending_accesses).requests.transferring_data
  ==>
  (!request. MEM request requests_transferring_data ==> MEM request pending_accesses.requests.transferring_data)
Proof
INTRO_TAC THEN
INTRO_TAC THEN
PTAC append_reply_remove_request_transferring_data THEN
RECORD_TAC THEN
LRTAC THEN
TRY (ETAC remove_pending_request) THEN
TRY (ETAC listTheory.MEM_FILTER) THEN
STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_TRANSFERRING_DATA_NOT_EXPANDING_WRITING_BACK_BD_REQUESTS_LEMMA:
!requests_writing_back_bd pending_accesses serviced_request.
  requests_writing_back_bd = (append_reply_remove_request_transferring_data serviced_request pending_accesses).requests.writing_back_bd
  ==>
  (!request. MEM request requests_writing_back_bd ==> MEM request pending_accesses.requests.writing_back_bd)
Proof
INTRO_TAC THEN
INTRO_TAC THEN
PTAC append_reply_remove_request_transferring_data THEN
RECORD_TAC THEN
LRTAC THEN
TRY (ETAC remove_pending_request) THEN
TRY (ETAC listTheory.MEM_FILTER) THEN
STAC
QED



Theorem APPEND_REPLY_REMOVE_REQUEST_WRITING_BACK_BD_NOT_EXPANDING_PENDING_ACCESSES_LEMMA:
!pending_accesses1 pending_accesses2 serviced_request.
  pending_accesses2 = append_reply_remove_request_writing_back_bd serviced_request pending_accesses1
  ==>
  (!request. pending_accesses2.requests.fetching_bd = SOME request ==> pending_accesses1.requests.fetching_bd = SOME request) /\
  (!request. MEM request pending_accesses2.requests.updating_bd ==> MEM request pending_accesses1.requests.updating_bd) /\
  (!request. MEM request pending_accesses2.requests.transferring_data ==> MEM request pending_accesses1.requests.transferring_data) /\
  (!request. MEM request pending_accesses2.requests.writing_back_bd ==> MEM request pending_accesses1.requests.writing_back_bd)
Proof
INTRO_TAC THEN
PTAC append_reply_remove_request_writing_back_bd THEN
REPEAT CONJ_TAC THEN
LRTAC THEN
RECORD_TAC THEN
REWRITE_TAC [boolTheory.IMP_CLAUSES] THEN
INTRO_TAC THEN
ETAC remove_pending_request THEN
ETAC listTheory.MEM_FILTER THEN
STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_WRITING_BACK_BD_NOT_EXPANDING_FETCHING_BD_REQUESTS_LEMMA:
!requests_fetching_bd pending_accesses serviced_request.
  requests_fetching_bd = (append_reply_remove_request_writing_back_bd serviced_request pending_accesses).requests.fetching_bd
  ==>
  (!request. requests_fetching_bd = SOME request ==> pending_accesses.requests.fetching_bd = SOME request)
Proof
INTRO_TAC THEN
PTAC append_reply_remove_request_writing_back_bd THEN
RECORD_TAC THEN
ASM_REWRITE_TAC [optionTheory.NOT_NONE_SOME, boolTheory.IMP_CLAUSES]
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_WRITING_BACK_BD_NOT_EXPANDING_UPDATING_BD_REQUESTS_LEMMA:
!requests_updating_bd pending_accesses serviced_request.
  requests_updating_bd = (append_reply_remove_request_writing_back_bd serviced_request pending_accesses).requests.updating_bd
  ==>
  (!request. MEM request requests_updating_bd ==> MEM request pending_accesses.requests.updating_bd)
Proof
INTRO_TAC THEN
INTRO_TAC THEN
PTAC append_reply_remove_request_writing_back_bd THEN
RECORD_TAC THEN
LRTAC THEN
TRY (ETAC remove_pending_request) THEN
TRY (ETAC listTheory.MEM_FILTER) THEN
STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_WRITING_BACK_BD_NOT_EXPANDING_TRANSFERRING_DATA_REQUESTS_LEMMA:
!requests_transferring_data pending_accesses serviced_request.
  requests_transferring_data = (append_reply_remove_request_writing_back_bd serviced_request pending_accesses).requests.transferring_data
  ==>
  (!request. MEM request requests_transferring_data ==> MEM request pending_accesses.requests.transferring_data)
Proof
INTRO_TAC THEN
INTRO_TAC THEN
PTAC append_reply_remove_request_writing_back_bd THEN
RECORD_TAC THEN
LRTAC THEN
TRY (ETAC remove_pending_request) THEN
TRY (ETAC listTheory.MEM_FILTER) THEN
STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_WRITING_BACK_BD_NOT_EXPANDING_WRITING_BACK_BD_REQUESTS_LEMMA:
!requests_writing_back_bd pending_accesses serviced_request.
  requests_writing_back_bd = (append_reply_remove_request_writing_back_bd serviced_request pending_accesses).requests.writing_back_bd
  ==>
  (!request. MEM request requests_writing_back_bd ==> MEM request pending_accesses.requests.writing_back_bd)
Proof
INTRO_TAC THEN
INTRO_TAC THEN
PTAC append_reply_remove_request_writing_back_bd THEN
RECORD_TAC THEN
LRTAC THEN
TRY (ETAC remove_pending_request) THEN
TRY (ETAC listTheory.MEM_FILTER) THEN
STAC
QED



Theorem APPEND_REPLY_REMOVE_REQUEST_OPERATION_NOT_EXPANDING_FETCHING_BD_REQUESTS_LEMMA:
!pending_accesses requests_fetching_bd serviced_request operation.
  requests_fetching_bd = (append_reply_remove_request_operation serviced_request pending_accesses operation).requests.fetching_bd
  ==>
  (!request. requests_fetching_bd = SOME request ==> pending_accesses.requests.fetching_bd = SOME request)
Proof
INTRO_TAC THEN
PTAC append_reply_remove_request_operation THENL
[
 ITAC APPEND_REPLY_REMOVE_REQUEST_FETCHING_BD_NOT_EXPANDING_FETCHING_BD_REQUESTS_LEMMA THEN STAC
 ,
 ITAC APPEND_REPLY_REMOVE_REQUEST_UPDATING_BD_NOT_EXPANDING_FETCHING_BD_REQUESTS_LEMMA THEN STAC
 ,
 ITAC APPEND_REPLY_REMOVE_REQUEST_TRANSFERRING_DATA_NOT_EXPANDING_FETCHING_BD_REQUESTS_LEMMA THEN STAC
 ,
 ITAC APPEND_REPLY_REMOVE_REQUEST_WRITING_BACK_BD_NOT_EXPANDING_FETCHING_BD_REQUESTS_LEMMA THEN STAC
]
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_OPERATION_NOT_EXPANDING_UPDATING_BD_REQUESTS_LEMMA:
!pending_accesses requests_updating_bd serviced_request operation.
  requests_updating_bd = (append_reply_remove_request_operation serviced_request pending_accesses operation).requests.updating_bd
  ==>
  (!request. MEM request requests_updating_bd ==> MEM request pending_accesses.requests.updating_bd)
Proof
INTRO_TAC THEN
PTAC append_reply_remove_request_operation THENL
[
 ITAC APPEND_REPLY_REMOVE_REQUEST_FETCHING_BD_NOT_EXPANDING_UPDATING_BD_REQUESTS_LEMMA THEN STAC
 ,
 ITAC APPEND_REPLY_REMOVE_REQUEST_UPDATING_BD_NOT_EXPANDING_UPDATING_BD_REQUESTS_LEMMA THEN STAC
 ,
 ITAC APPEND_REPLY_REMOVE_REQUEST_TRANSFERRING_DATA_NOT_EXPANDING_UPDATING_BD_REQUESTS_LEMMA THEN STAC
 ,
 ITAC APPEND_REPLY_REMOVE_REQUEST_WRITING_BACK_BD_NOT_EXPANDING_UPDATING_BD_REQUESTS_LEMMA THEN STAC
]
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_OPERATION_NOT_EXPANDING_TRANSFERRING_DATA_REQUESTS_LEMMA:
!pending_accesses requests_transferring_data serviced_request operation.
  requests_transferring_data =
  (append_reply_remove_request_operation serviced_request pending_accesses operation).requests.transferring_data
  ==>
  (!request. MEM request requests_transferring_data ==> MEM request pending_accesses.requests.transferring_data)
Proof
INTRO_TAC THEN
PTAC append_reply_remove_request_operation THENL
[
 ITAC APPEND_REPLY_REMOVE_REQUEST_FETCHING_BD_NOT_EXPANDING_TRANSFERRING_DATA_REQUESTS_LEMMA THEN STAC
 ,
 ITAC APPEND_REPLY_REMOVE_REQUEST_UPDATING_BD_NOT_EXPANDING_TRANSFERRING_DATA_REQUESTS_LEMMA THEN STAC
 ,
 ITAC APPEND_REPLY_REMOVE_REQUEST_TRANSFERRING_DATA_NOT_EXPANDING_TRANSFERRING_DATA_REQUESTS_LEMMA THEN STAC
 ,
 ITAC APPEND_REPLY_REMOVE_REQUEST_WRITING_BACK_BD_NOT_EXPANDING_TRANSFERRING_DATA_REQUESTS_LEMMA THEN STAC
]
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_OPERATION_NOT_EXPANDING_WRITING_BACK_BD_REQUESTS_LEMMA:
!pending_accesses requests_writing_back_bd serviced_request operation.
  requests_writing_back_bd =
  (append_reply_remove_request_operation serviced_request pending_accesses operation).requests.writing_back_bd
  ==>
  (!request. MEM request requests_writing_back_bd ==> MEM request pending_accesses.requests.writing_back_bd)
Proof
INTRO_TAC THEN
PTAC append_reply_remove_request_operation THENL
[
 ITAC APPEND_REPLY_REMOVE_REQUEST_FETCHING_BD_NOT_EXPANDING_WRITING_BACK_BD_REQUESTS_LEMMA THEN STAC
 ,
 ITAC APPEND_REPLY_REMOVE_REQUEST_UPDATING_BD_NOT_EXPANDING_WRITING_BACK_BD_REQUESTS_LEMMA THEN STAC
 ,
 ITAC APPEND_REPLY_REMOVE_REQUEST_TRANSFERRING_DATA_NOT_EXPANDING_WRITING_BACK_BD_REQUESTS_LEMMA THEN STAC
 ,
 ITAC APPEND_REPLY_REMOVE_REQUEST_WRITING_BACK_BD_NOT_EXPANDING_WRITING_BACK_BD_REQUESTS_LEMMA THEN STAC
]
QED



Theorem FOLDL_APPEND_REPLY_REMOVE_REQUEST_OPERATION_NOT_EXPANDING_REQUESTS_FETCHING_BD_LEMMA:
!qs serviced_request pending_accesses requests_fetching_bd.
  requests_fetching_bd = (FOLDL (append_reply_remove_request_operation serviced_request) pending_accesses qs).requests.fetching_bd
  ==>
  (!request. requests_fetching_bd = SOME request ==> pending_accesses.requests.fetching_bd = SOME request)
Proof
Induct THENL
[
 REWRITE_TAC [listTheory.FOLDL] THEN
 INTRO_TAC THEN
 STAC
 ,
 REWRITE_TAC [listTheory.FOLDL] THEN
 INTRO_TAC THEN
 AITAC THEN
 INTRO_TAC THEN
 FAIRTAC THEN
 FITAC APPEND_REPLY_REMOVE_REQUEST_OPERATION_NOT_EXPANDING_FETCHING_BD_REQUESTS_LEMMA THEN
 FAIRTAC THEN
 STAC
]
QED

Theorem FOLDL_APPEND_REPLY_REMOVE_REQUEST_OPERATION_NOT_EXPANDING_REQUESTS_UPDATING_BD_LEMMA:
!qs serviced_request pending_accesses requests_updating_bd.
  requests_updating_bd = (FOLDL (append_reply_remove_request_operation serviced_request) pending_accesses qs).requests.updating_bd
  ==>
  (!request. MEM request requests_updating_bd ==> MEM request pending_accesses.requests.updating_bd)
Proof
Induct THENL
[
 REWRITE_TAC [listTheory.FOLDL] THEN
 INTRO_TAC THEN
 ASM_REWRITE_TAC [boolTheory.IMP_CLAUSES]
 ,
 REWRITE_TAC [listTheory.FOLDL] THEN
 INTRO_TAC THEN
 AITAC THEN
 INTRO_TAC THEN
 FAIRTAC THEN
 FITAC APPEND_REPLY_REMOVE_REQUEST_OPERATION_NOT_EXPANDING_UPDATING_BD_REQUESTS_LEMMA THEN
 FAIRTAC THEN
 STAC
]
QED

Theorem FOLDL_APPEND_REPLY_REMOVE_REQUEST_OPERATION_NOT_EXPANDING_REQUESTS_TRANSFERRING_DATA_LEMMA:
!qs serviced_request pending_accesses requests_transferring_data.
  requests_transferring_data = (FOLDL (append_reply_remove_request_operation serviced_request) pending_accesses qs).requests.transferring_data
  ==>
  (!request. MEM request requests_transferring_data ==> MEM request pending_accesses.requests.transferring_data)
Proof
Induct THENL
[
 REWRITE_TAC [listTheory.FOLDL] THEN
 INTRO_TAC THEN
 ASM_REWRITE_TAC [boolTheory.IMP_CLAUSES]
 ,
 REWRITE_TAC [listTheory.FOLDL] THEN
 INTRO_TAC THEN
 AITAC THEN
 INTRO_TAC THEN
 FAIRTAC THEN
 FITAC APPEND_REPLY_REMOVE_REQUEST_OPERATION_NOT_EXPANDING_TRANSFERRING_DATA_REQUESTS_LEMMA THEN
 FAIRTAC THEN
 STAC
]
QED

Theorem FOLDL_APPEND_REPLY_REMOVE_REQUEST_OPERATION_NOT_EXPANDING_REQUESTS_WRITING_BACK_BD_LEMMA:
!qs serviced_request pending_accesses requests_writing_back_bd.
  requests_writing_back_bd = (FOLDL (append_reply_remove_request_operation serviced_request) pending_accesses qs).requests.writing_back_bd
  ==>
  (!request. MEM request requests_writing_back_bd ==> MEM request pending_accesses.requests.writing_back_bd)
Proof
Induct THENL
[
 REWRITE_TAC [listTheory.FOLDL] THEN
 INTRO_TAC THEN
 ASM_REWRITE_TAC [boolTheory.IMP_CLAUSES]
 ,
 REWRITE_TAC [listTheory.FOLDL] THEN
 INTRO_TAC THEN
 AITAC THEN
 INTRO_TAC THEN
 FAIRTAC THEN
 FITAC APPEND_REPLY_REMOVE_REQUEST_OPERATION_NOT_EXPANDING_WRITING_BACK_BD_REQUESTS_LEMMA THEN
 FAIRTAC THEN
 STAC
]
QED



Theorem APPEND_REPLY_REMOVE_REQUEST_CHANNEL_NOT_EXPANDING_PENDING_REQUESTS_LEMMA:
!channel1 channel2 serviced_request.
  channel2 = append_reply_remove_request_channel serviced_request channel1
  ==>
  (!request. channel2.pending_accesses.requests.fetching_bd = SOME request
         ==> channel1.pending_accesses.requests.fetching_bd = SOME request) /\
  (!request. MEM request channel2.pending_accesses.requests.updating_bd
         ==> MEM request channel1.pending_accesses.requests.updating_bd) /\
  (!request. MEM request channel2.pending_accesses.requests.transferring_data
         ==> MEM request channel1.pending_accesses.requests.transferring_data) /\
  (!request. MEM request channel2.pending_accesses.requests.writing_back_bd
         ==> MEM request channel1.pending_accesses.requests.writing_back_bd)
Proof
INTRO_TAC THEN
ETAC append_reply_remove_request_channel THEN
LRTAC THEN
REPEAT CONJ_TAC THEN
INTRO_TAC THEN
RECORD_TAC THENL
[
 FITAC FOLDL_APPEND_REPLY_REMOVE_REQUEST_OPERATION_NOT_EXPANDING_REQUESTS_FETCHING_BD_LEMMA
 ,
 FITAC FOLDL_APPEND_REPLY_REMOVE_REQUEST_OPERATION_NOT_EXPANDING_REQUESTS_UPDATING_BD_LEMMA
 ,
 FITAC FOLDL_APPEND_REPLY_REMOVE_REQUEST_OPERATION_NOT_EXPANDING_REQUESTS_TRANSFERRING_DATA_LEMMA
 ,
 FITAC FOLDL_APPEND_REPLY_REMOVE_REQUEST_OPERATION_NOT_EXPANDING_REQUESTS_WRITING_BACK_BD_LEMMA
] THEN
FAIRTAC THEN
STAC
QED



Theorem REMOVE_PENDING_REQUESTS_NOT_EXPANDING_PENDING_REQUESTS_LEMMA:
!request reply pending_requests.
  MEM request (remove_pending_request reply pending_requests)
  ==>
  MEM request pending_requests
Proof
INTRO_TAC THEN
PTAC remove_pending_request THEN
ETAC listTheory.MEM_FILTER THEN
STAC
QED

Theorem APPEND_REPLY_REMOVE_REGISTER_RELATED_REPLY_NOT_EXPANDING_PENDING_REQUESTS_LEMMA:
!reply pending_requests1 pending_requests2 pending_replies1 pending_replies2 request.
  (pending_requests2, pending_replies2) = append_reply_remove_register_related_reply reply pending_requests1 pending_replies1 /\
  MEM request pending_requests2
  ==>
  MEM request pending_requests1
Proof
INTRO_TAC THEN
PTAC append_reply_remove_register_related_reply THENL
[
 EQ_PAIR_ASM_TAC THEN
 LRTAC THEN
 ITAC REMOVE_PENDING_REQUESTS_NOT_EXPANDING_PENDING_REQUESTS_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 STAC
]
QED

Theorem DMA_REQUEST_SERVED_NOT_EXPANDING_PENDING_REQUESTS_LEMMA:
!device_characteristics device1 device2 reply.
  device2 = dma_request_served device_characteristics device1 reply
  ==>
  LIST1_IN_LIST2 device2.dma_state.pending_register_related_memory_requests device1.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
PTAC dma_request_served THEN
LRTAC THEN
RECORD_TAC THEN
ITAC APPEND_REPLY_REMOVE_REGISTER_RELATED_REPLY_NOT_EXPANDING_PENDING_REQUESTS_LEMMA THEN
PTAC listsTheory.LIST1_IN_LIST2 THEN
ETAC listTheory.EVERY_MEM THEN
APP_SCALAR_TAC THEN
STAC
QED





Theorem APPEND_REPLY_REMOVE_REQUEST_CHANNEL_APPENDS_REPLY_REMOVES_REQUEST_LEMMA:
!channel1 channel2 channel_index max_index serviced_request.
  channel_index <=+ max_index /\
  channel2 = append_reply_remove_request_channel serviced_request channel1
  ==>
  APPENDED_REPLY_REMOVED_REQUEST_INDEXED_CHANNEL channel1 channel2 serviced_request channel_index max_index
Proof
INTRO_TAC THEN
PTAC APPENDED_REPLY_REMOVED_REQUEST_INDEXED_CHANNEL THEN
CONJ_TAC THENL
[
 INTRO_TAC THEN
 PTAC APPENDED_REPLY_REMOVED_REQUEST_CHANNEL THEN
 STAC
 ,
 INTRO_TAC THEN
 ETAC wordsTheory.WORD_NOT_HIGHER THEN
 CONTR_ASMS_TAC
]
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_CHANNEL_ZERO_IMPLIES_APPENDED_REPLY_REMOVED_REQUEST_CHANNELS_ZERO_LEMMA:
!channels1 channels2 channel1 channel2 serviced_request.
  channel1 = THE (channels1 0w) /\
  channel2 = append_reply_remove_request_channel serviced_request channel1 /\
  channels2 = (0w =+ SOME channel2) channels1
  ==>
  APPENDED_REPLY_REMOVED_REQUEST_CHANNELS channels1 channels2 serviced_request 0w
Proof
INTRO_TAC THEN
ETAC APPENDED_REPLY_REMOVED_REQUEST_CHANNELS THEN
INTRO_TAC THEN
ETAC APPENDED_REPLY_REMOVED_REQUEST_INDEXED_CHANNEL THEN
CONJ_TAC THENL
[
 INTRO_TAC THEN
 PTAC APPENDED_REPLY_REMOVED_REQUEST_CHANNEL THEN
 ITAC ((GEN_ALL o #1 o EQ_IMP_RULE o SPEC_ALL) wordsTheory.WORD_LS_word_0) THEN
 LRTAC THEN
 RLTAC THEN
 RLTAC THEN
 LRTAC THEN
 ETAC combinTheory.UPDATE_def THEN
 APP_SCALAR_TAC THEN
 LRTAC THEN
 LRTAC THEN
 APP_SCALAR_TAC THEN
 ASM_REWRITE_TAC [optionTheory.THE_DEF]
 ,
 INTRO_TAC THEN
 ETAC wordsTheory.WORD_HIGHER THEN
 IRTAC wordsTheory.WORD_LOWER_NOT_EQ THEN
 ALL_LRTAC THEN
 ETAC combinTheory.UPDATE_def THEN
 APP_SCALAR_TAC THEN
 STAC
]
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_CHANNEL_APPENDED_REPLY_REMOVED_REQUEST_OR_PRESERVES_CHANNELS_LEMMA:
!channels1 channels2 channel1 channel2 serviced_request.
  channel1 = THE (channels1 0w) /\
  channel2 = append_reply_remove_request_channel serviced_request channel1 /\
  channels2 = (0w =+ SOME channel2) channels1
  ==>
  APPENDED_REPLY_REMOVED_REQUEST_CHANNELS channels1 channels2 serviced_request 0w /\
  PRESERVED_CHANNELS channels1 channels2 0w /\
  DEFINED_PRESERVED_CHANNELS channels1 channels2 0w
Proof
INTRO_TAC THEN
ITAC internal_operation_lemmasTheory.UPDATING_CHANNEL_ZERO_IMPLIES_DEFINED_PRESERVED_CHANNELS_ZERO_LEMMA THEN
ITAC APPEND_REPLY_REMOVE_REQUEST_CHANNEL_ZERO_IMPLIES_APPENDED_REPLY_REMOVED_REQUEST_CHANNELS_ZERO_LEMMA THEN
ITAC internal_operation_lemmasTheory.APPEND_BDS_CHANNEL_ZERO_PRESERVED_CHANNELS_LEMMA THEN STAC
QED

Theorem UPDATING_SUC_APPENDED_REPLY_REMOVED_REQUEST_CHANNELS_IMPLIES_APPENDED_REPLY_REMOVED_REQUEST_CHANNEL_LEMMA:
!channels1 channels2 channels channel1 channel2 channel index n serviced_request.
  SUC n < dimword (: 'b) /\
  index : 'b word <=+ n2w n /\
  channel1 = THE (channels1 index) /\
  channel2 = THE (channels2 index) /\
  channels = ((n2w n + 1w) =+ SOME channel) channels1 /\
  APPENDED_REPLY_REMOVED_REQUEST_CHANNELS channels channels2 serviced_request (n2w n)
  ==>
  APPENDED_REPLY_REMOVED_REQUEST_CHANNEL channel1 channel2 serviced_request
Proof
INTRO_TAC THEN
ETAC APPENDED_REPLY_REMOVED_REQUEST_CHANNELS THEN
FAITAC THEN
ETAC APPENDED_REPLY_REMOVED_REQUEST_INDEXED_CHANNEL THEN
AITAC THEN
ALL_LRTAC THEN
IRTAC word_lemmasTheory.LEQ_MAX_IMPLIES_DISTINCT_GT_MAX_LEMMA THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
IF_SPLIT_TAC THENL
[
 LRTAC THEN
 CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
 ,
 STAC
]
QED

Theorem UPDATING_NEXT_APPENDED_REPLY_REMOVED_REQUEST_CHANNELS_IMPLIES_INDEXED_CHANNEL_LEMMA:
!channels channels1 channels2 n index channel1' channel2' channel2 serviced_request.
  SUC n < dimword (: 'b) /\
  APPENDED_REPLY_REMOVED_REQUEST_CHANNELS channels channels2 serviced_request (n2w n : 'b word) /\
  index <=+ n2w n /\
  channels = ((n2w n + 1w) =+ SOME channel2) channels1 /\
  channel2' = THE (channels2 index) /\
  channel1' = THE (channels1 index)
  ==>
  APPENDED_REPLY_REMOVED_REQUEST_INDEXED_CHANNEL channel1' channel2' serviced_request index (n2w n + 1w)
Proof
INTRO_TAC THEN
ETAC APPENDED_REPLY_REMOVED_REQUEST_INDEXED_CHANNEL THEN
CONJ_TAC THENL
[
 INTRO_TAC THEN
 FIRTAC UPDATING_SUC_APPENDED_REPLY_REMOVED_REQUEST_CHANNELS_IMPLIES_APPENDED_REPLY_REMOVED_REQUEST_CHANNEL_LEMMA THEN
 STAC
 ,
 INTRO_TAC THEN
 IRTAC word_lemmasTheory.LEQ_GT_SUC_IMPLIES_F_LEMMA THEN
 SOLVE_F_ASM_TAC
]
QED



Theorem UPDATING_SUC_PRESERVED_IMPLIES_GT_PRESERVED_LEMMA:
!n channels channels2 channels1 channel1' channel2' channel index.
  SUC n < dimword (: 'b) /\
  PRESERVED_CHANNELS channels channels2 (n2w n : 'b word) /\
  channels = ((n2w n + 1w) =+ SOME channel) channels1 /\
  channel1' = THE (channels1 index) /\
  channel2' = THE (channels2 index) /\
  index >+ n2w n + 1w
  ==>
  channel1' = channel2'
Proof
INTRO_TAC THEN
ETAC PRESERVED_CHANNELS THEN
ITAC word_lemmasTheory.GT_SUC_IMPLIES_GT_LEMMA THEN
FAIRTAC THEN
ALL_LRTAC THEN
ETAC combinTheory.UPDATE_def THEN
APP_SCALAR_TAC THEN
ETAC wordsTheory.WORD_HIGHER THEN
IRTAC wordsTheory.WORD_LOWER_NOT_EQ THEN
STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_AND_PRESERVED_CHANNELS_IMPLIES_APPENDED_REPLY_REMOVED_REQUEST_INDEXED_CHANNEL_LEMMA:
!n channels channels2 channels1 channel1 channel2 channel1' channel2' serviced_request index.
  SUC n < dimword (: 'b) /\
  PRESERVED_CHANNELS channels channels2 (n2w n : 'b word) /\
  channel1' = THE (channels1 index) /\
  channel2' = THE (channels2 index) /\
  channel1 = THE (channels1 (n2w n + 1w)) /\
  channel2 = append_reply_remove_request_channel serviced_request channel1 /\
  channels = ((n2w n + 1w) =+ SOME channel2) channels1 /\
  index >+ n2w n
  ==>
  APPENDED_REPLY_REMOVED_REQUEST_INDEXED_CHANNEL channel1' channel2' serviced_request index (n2w n + 1w)
Proof
INTRO_TAC THEN
ETAC APPENDED_REPLY_REMOVED_REQUEST_INDEXED_CHANNEL THEN
CONJ_TAC THENL
[
 INTRO_TAC THEN
 IRTAC word_lemmasTheory.WORD_LEQ_SUC_IMPLIES_LEQ_OR_EQ_SUC_LEMMA THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  ETAC wordsTheory.WORD_HIGHER THEN
  ASSUME_TAC (SPECL [“n2w n : 'b word”, “index : 'b word”] (REWRITE_RULE [boolTheory.DE_MORGAN_THM] (INST_TYPE [alpha |-> beta] wordsTheory.WORD_LOWER_EQ_ANTISYM))) THEN
  SPLIT_ASM_DISJS_TAC THEN CONTR_ASMS_TAC
  ,
  ITAC internal_operation_lemmasTheory.UPDATING_ACCESSED_CHANNEL_AND_PRESERVED_CHANNELS_IMPLIES_SAME_CHANNELS_LEMMA THEN
  ETAC APPENDED_REPLY_REMOVED_REQUEST_CHANNEL THEN
  STAC
 ]
 ,
 INTRO_TAC THEN
 IRTAC UPDATING_SUC_PRESERVED_IMPLIES_GT_PRESERVED_LEMMA THEN
 STAC
]
QED

Theorem APPENDED_REPLY_REMOVED_REQUEST_CHANNELS_SUC_LEMMA:
!n channel1 channel2 channels1 channels channels2 serviced_request.
  SUC n < dimword (: 'b) /\
  channel1 = THE (channels1 (n2w n + 1w : 'b word)) /\
  channel2 = append_reply_remove_request_channel serviced_request channel1 /\
  channels = ((n2w n + 1w) =+ SOME channel2) channels1 /\
  PRESERVED_CHANNELS channels channels2 (n2w n) /\
  APPENDED_REPLY_REMOVED_REQUEST_CHANNELS channels channels2 serviced_request (n2w n)
  ==>
  APPENDED_REPLY_REMOVED_REQUEST_CHANNELS channels1 channels2 serviced_request (n2w n + 1w)
Proof
INTRO_TAC THEN
REWRITE_TAC [APPENDED_REPLY_REMOVED_REQUEST_CHANNELS] THEN
INTRO_TAC THEN
Cases_on ‘index <=+ n2w n’ THENL
[
 IRTAC UPDATING_NEXT_APPENDED_REPLY_REMOVED_REQUEST_CHANNELS_IMPLIES_INDEXED_CHANNEL_LEMMA THEN STAC
 ,
 ETAC wordsTheory.WORD_NOT_LOWER_EQUAL THEN
 ETAC wordsTheory.WORD_HIGHER THEN
 ITAC APPEND_REPLY_REMOVE_REQUEST_AND_PRESERVED_CHANNELS_IMPLIES_APPENDED_REPLY_REMOVED_REQUEST_INDEXED_CHANNEL_LEMMA THEN STAC
]
QED

Theorem APPEND_REPLY_REMOVED_REQUEST_CHANNELS_LEMMA:
!n channel 
(channels1 : ('channel_index_width) channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
channel' channels' channels2 serviced_request.
  SUC n < dimword (: 'channel_index_width) /\
  (!(channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
    (channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option).
     APPENDED_REPLY_REMOVED_REQUEST_INDEXED_OR_PRESERVED_CHANNELS channels1 channels2 serviced_request (n2w n)) /\
  n2w n + 1w <> 0w /\
  channel = THE (channels1 (n2w n + 1w)) /\
  channel' = append_reply_remove_request_channel serviced_request channel /\
  channels' = ((n2w n + 1w) =+ SOME channel') channels1 /\
  channels2 = append_reply_remove_request_channels_index serviced_request channels' (n2w n)
  ==>
  APPENDED_REPLY_REMOVED_REQUEST_CHANNELS channels1 channels2 serviced_request (n2w n + 1w)
Proof
INTRO_TAC THEN
RW_HYPS_TAC operationsTheory.APPENDED_REPLY_REMOVED_REQUEST_INDEXED_OR_PRESERVED_CHANNELS THEN
IRTAC APPENDED_REPLY_REMOVED_REQUEST_CHANNELS_SUC_LEMMA THEN
INST_IMP_ASM_GOAL_TAC THEN
AIRTAC THEN
STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_CHANNEL_NOT_ZERO_PRESERVED_CHANNELS_LEMMA:
!n channel1 channel2 serviced_request
 (channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels  : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option).
  SUC n < dimword (: 'channel_index_width) /\
  (!(channels1 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
    (channels2 : 'channel_index_width channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option).
     APPENDED_REPLY_REMOVED_REQUEST_INDEXED_OR_PRESERVED_CHANNELS channels1 channels2 serviced_request (n2w n)) /\
  channel1 = THE (channels1 (n2w n + 1w)) /\
  channel2 = append_reply_remove_request_channel serviced_request channel1 /\
  channels = ((n2w n + 1w) =+ SOME channel2) channels1 /\
  n2w n + 1w <> 0w /\
  channels2 = append_reply_remove_request_channels_index serviced_request channels (n2w n)
  ==>
  PRESERVED_CHANNELS channels1 channels2 (n2w n + 1w)
Proof
INTRO_TAC THEN
RW_HYPS_TAC APPENDED_REPLY_REMOVED_REQUEST_INDEXED_OR_PRESERVED_CHANNELS THEN
FAIRTAC THEN
IRTAC internal_operation_lemmasTheory.PRESERVED_CHANNELS_IMPLIES_NEXT_INDEX_LEMMA THEN
STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_CHANNELS_SUC_IMPLIES_DEFINED_PRESERVED_CHANNELS_LEMMA:
!n 
 (channels1 : ('channel_index_width) channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels :  ('channel_index_width) channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels2 : ('channel_index_width) channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 channel serviced_request.
  (!(channels1 : ('channel_index_width) channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
    (channels2 : ('channel_index_width) channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option).
     APPENDED_REPLY_REMOVED_REQUEST_INDEXED_OR_PRESERVED_CHANNELS channels1 channels2 serviced_request (n2w n)) /\
  SUC n < dimword (: 'channel_index_width) /\
  n2w n + 1w <> 0w /\
  channels = ((n2w n + 1w) =+ SOME channel) channels1 /\
  channels2 = append_reply_remove_request_channels_index serviced_request channels (n2w n)
  ==>
  DEFINED_PRESERVED_CHANNELS channels1 channels2 (n2w n + 1w)
Proof
INTRO_TAC THEN
RW_HYPS_TAC APPENDED_REPLY_REMOVED_REQUEST_INDEXED_OR_PRESERVED_CHANNELS THEN
AIRTAC THEN
ETAC DEFINED_PRESERVED_CHANNELS THEN
CONJ_TAC THENL
[
 INTRO_TAC THEN
 IRTAC word_lemmasTheory.WORD_LEQ_SUC_IMPLIES_LEQ_OR_EQ_SUC_LEMMA THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  AIRTAC THEN STAC
  ,
  ITAC word_lemmasTheory.EQ_SUC_IMPLIES_GT_LEMMA THEN
  LRTAC THEN
  FAIRTAC THEN
  RLTAC THEN
  LRTAC THEN
  ETAC combinTheory.UPDATE_def THEN
  APP_SCALAR_TAC THEN
  REWRITE_TAC [optionTheory.IS_SOME_DEF]
 ]
 ,
 INTRO_TAC THEN
 ETAC wordsTheory.WORD_HIGHER THEN
 ITAC wordsTheory.WORD_LOWER_NOT_EQ THEN
 ETAC wordsTheory.WORD_HIGHER THEN
 ITAC word_lemmasTheory.GT_SUC_IMPLIES_GT_LEMMA THEN
 FAIRTAC THEN
 RLTAC THEN
 LRTAC THEN
 ETAC combinTheory.UPDATE_def THEN
 APP_SCALAR_TAC THEN
 STAC
]
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_CHANNELS_INDEX_APPENDED_REPLY_REMOVED_REQUEST_CHANNELS_INDUCTION_LEMMA:
!n serviced_request.
  SUC n < dimword (: 'channel_index_width)
  ==>
  (!(channels1 : ('channel_index_width) channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
    (channels2 : ('channel_index_width) channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option).
    APPENDED_REPLY_REMOVED_REQUEST_INDEXED_OR_PRESERVED_CHANNELS channels1 channels2 serviced_request (n2w n))
  ==>
  (!(channels1 : ('channel_index_width) channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
    (channels2 : ('channel_index_width) channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option).
    APPENDED_REPLY_REMOVED_REQUEST_INDEXED_OR_PRESERVED_CHANNELS channels1 channels2 serviced_request (n2w (SUC n)))
Proof
INTRO_TAC THEN
INTRO_TAC THEN
REWRITE_TAC [APPENDED_REPLY_REMOVED_REQUEST_INDEXED_OR_PRESERVED_CHANNELS] THEN
INTRO_TAC THEN
PTAC operationsTheory.append_reply_remove_request_channels_index THENL
[
 RLTAC THEN
 ITAC APPEND_REPLY_REMOVE_REQUEST_CHANNEL_APPENDED_REPLY_REMOVED_REQUEST_OR_PRESERVES_CHANNELS_LEMMA THEN
 ITAC internal_operation_lemmasTheory.APPEND_BDS_CHANNEL_ZERO_PRESERVED_CHANNELS_LEMMA THEN
 ITAC internal_operation_lemmasTheory.UPDATING_CHANNEL_ZERO_IMPLIES_DEFINED_PRESERVED_CHANNELS_ZERO_LEMMA THEN
 STAC
 ,
 ETAC wordsTheory.n2w_SUC THEN
 ETAC wordsTheory.WORD_ADD_SUB THEN
 ITAC APPEND_REPLY_REMOVED_REQUEST_CHANNELS_LEMMA THEN
 ITAC APPEND_REPLY_REMOVE_REQUEST_CHANNEL_NOT_ZERO_PRESERVED_CHANNELS_LEMMA THEN
 ITAC APPEND_REPLY_REMOVE_REQUEST_CHANNELS_SUC_IMPLIES_DEFINED_PRESERVED_CHANNELS_LEMMA THEN
 STAC
]
QED

Theorem APPENDED_REPLY_REMOVED_REQUEST_INDEXED_OR_PRESERVED_CHANNELS_LEMMA:
!index channels1 channels2 serviced_request.
  APPENDED_REPLY_REMOVED_REQUEST_INDEXED_OR_PRESERVED_CHANNELS channels1 channels2 serviced_request index
Proof
ABS_APP_TAC THEN
MATCH_MP_TAC wordsTheory.WORD_INDUCT THEN
BETA_TAC THEN
CONJ_TAC THENL
[
 REPEAT GEN_TAC THEN
 PTAC APPENDED_REPLY_REMOVED_REQUEST_INDEXED_OR_PRESERVED_CHANNELS THEN 
 INTRO_TAC THEN
 PTAC operationsTheory.append_reply_remove_request_channels_index THEN (TRY (CONTR_NEG_ASM_TAC boolTheory.EQ_REFL)) THEN
 IRTAC APPEND_REPLY_REMOVE_REQUEST_CHANNEL_APPENDED_REPLY_REMOVED_REQUEST_OR_PRESERVES_CHANNELS_LEMMA THEN
 STAC
 ,
 INTRO_TAC THEN
 INTRO_TAC THEN
 REPEAT GEN_TAC THEN
 IRTAC APPEND_REPLY_REMOVE_REQUEST_CHANNELS_INDEX_APPENDED_REPLY_REMOVED_REQUEST_CHANNELS_INDUCTION_LEMMA THEN
 INST_IMP_ASM_GOAL_TAC THEN
 STAC
]
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_CHANNELS_IMPLIES_IS_SOME_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (channels1 : ('channel_index_width) channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels2 : ('channel_index_width) channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 max_index index serviced_request.
  max_index = device_characteristics.dma_characteristics.max_index /\
  channels2 = append_reply_remove_request_channels channels1 max_index serviced_request /\
  VALID_CHANNEL_ID device_characteristics index
  ==>
  IS_SOME (channels2 index)
Proof
INTRO_TAC THEN
PTAC append_reply_remove_request_channels THEN
IRTAC (REWRITE_RULE [APPENDED_REPLY_REMOVED_REQUEST_INDEXED_OR_PRESERVED_CHANNELS] APPENDED_REPLY_REMOVED_REQUEST_INDEXED_OR_PRESERVED_CHANNELS_LEMMA) THEN
ETAC DEFINED_PRESERVED_CHANNELS THEN
IRTAC state_lemmasTheory.VALID_CHANNEL_ID_IMPLIES_LEQ_MAX_LEMMA THEN
AIRTAC THEN
STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_CHANNELS_IMPLIES_EQ_IS_SOME_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (channels1 : ('channel_index_width) channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels2 : ('channel_index_width) channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 max_index channel_id serviced_request.
  max_index = device_characteristics.dma_characteristics.max_index /\
  channels2 = append_reply_remove_request_channels channels1 max_index serviced_request /\
  ~VALID_CHANNEL_ID device_characteristics channel_id
  ==>
  IS_SOME (channels2 channel_id) = IS_SOME (channels1 channel_id)
Proof
INTRO_TAC THEN
PTAC append_reply_remove_request_channels THEN
IRTAC (REWRITE_RULE [APPENDED_REPLY_REMOVED_REQUEST_INDEXED_OR_PRESERVED_CHANNELS] APPENDED_REPLY_REMOVED_REQUEST_INDEXED_OR_PRESERVED_CHANNELS_LEMMA) THEN
ETAC DEFINED_PRESERVED_CHANNELS THEN
ETAC PRESERVED_CHANNELS THEN
IRTAC state_lemmasTheory.NOT_VALID_CHANNEL_ID_IMPLIES_INDEX_GT_MAX_LEMMA THEN
AIRTAC THEN
AIRTAC THEN
AIRTAC THEN
STAC
QED

Theorem APPEND_REPLY_REMOVE_REQUEST_CHANNELS_IMPLIES_APPENDED_REPLY_REMOVED_REQUEST_CHANNEL_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (channels1 : ('channel_index_width) channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 (channels2 : ('channel_index_width) channel_id_type -> ('bd_type, 'interconnect_address_width, 'tag_width) channel_state_type option)
 max_index serviced_request.
  max_index = device_characteristics.dma_characteristics.max_index /\
  channels2 = append_reply_remove_request_channels channels1 max_index serviced_request
  ==>
  !index channel1 channel2.
    VALID_CHANNEL_ID device_characteristics index /\
    channel1 = THE (channels1 index) /\
    channel2 = THE (channels2 index) 
    ==>
    APPENDED_REPLY_REMOVED_REQUEST_CHANNEL channel1 channel2 serviced_request
Proof
INTRO_TAC THEN
INTRO_TAC THEN
PTAC append_reply_remove_request_channels THEN
IRTAC (REWRITE_RULE [APPENDED_REPLY_REMOVED_REQUEST_INDEXED_OR_PRESERVED_CHANNELS] APPENDED_REPLY_REMOVED_REQUEST_INDEXED_OR_PRESERVED_CHANNELS_LEMMA) THEN
ETAC APPENDED_REPLY_REMOVED_REQUEST_CHANNELS THEN
AITAC THEN
PTAC APPENDED_REPLY_REMOVED_REQUEST_INDEXED_CHANNEL THEN
IRTAC state_lemmasTheory.VALID_CHANNEL_ID_IMPLIES_LEQ_MAX_LEMMA THEN
AIRTAC THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_IS_SOME_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 serviced_request.
  device2 = dma_request_served device_characteristics device1 serviced_request
  ==>
  !channel_id channels2.
    VALID_CHANNEL_ID device_characteristics channel_id /\
    channels2 = device2.dma_state.channels
    ==>
    IS_SOME (channels2 channel_id)
Proof
INTRO_TAC THEN
INTRO_TAC THEN
PTAC dma_request_served THEN
IRTAC APPEND_REPLY_REMOVE_REQUEST_CHANNELS_IMPLIES_IS_SOME_LEMMA THEN
LRTAC THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_CHANNELS_SOME_PRESERVED_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 serviced_request.
  device2 = dma_request_served device_characteristics device1 serviced_request
  ==>
  !channel_id channels1 channels2.
    ~VALID_CHANNEL_ID device_characteristics channel_id /\
    channels1 = device1.dma_state.channels /\
    channels2 = device2.dma_state.channels
    ==>
    IS_SOME (channels2 channel_id) = IS_SOME (channels1 channel_id)
Proof
INTRO_TAC THEN
INTRO_TAC THEN
PTAC dma_request_served THEN
IRTAC APPEND_REPLY_REMOVE_REQUEST_CHANNELS_IMPLIES_EQ_IS_SOME_LEMMA THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 serviced_request.
  device2 = dma_request_served device_characteristics device1 serviced_request
  ==>
  !channels1 channels2 channel_id channel1 channel2.
    VALID_CHANNEL_ID device_characteristics channel_id /\
    channels1 = device1.dma_state.channels /\
    channels2 = device2.dma_state.channels /\
    channel1 = THE (channels1 channel_id) /\
    channel2 = THE (channels2 channel_id)
    ==>
    APPENDED_REPLY_REMOVED_REQUEST_CHANNEL channel1 channel2 serviced_request
Proof
INTRO_TAC THEN
INTRO_TAC THEN
PTAC dma_request_served THEN
IRTAC APPEND_REPLY_REMOVE_REQUEST_CHANNELS_IMPLIES_APPENDED_REPLY_REMOVED_REQUEST_CHANNEL_LEMMA THEN
AIRTAC THEN
LRTAC THEN
LRTAC THEN
RECORD_TAC THEN
RLTAC THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_PRESERVES_FUNCTION_STATES_LEMMA:
!device1 device2 device_characteristics serviced_request.
  device2 = dma_request_served device_characteristics device1 serviced_request
  ==>
  device2.function_state = device1.function_state
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_request_served THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_PRESERVES_INTERNAL_STATES_LEMMA:
!device_characteristics device1 device2 serviced_request.
  device2 = dma_request_served device_characteristics device1 serviced_request
  ==>
  device2.dma_state.internal_state = device1.dma_state.internal_state
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_request_served THEN
ALL_LRTAC THEN
RECORD_TAC THEN
STAC
QED


Theorem DMA_REQUEST_SERVED_APPEND_REPLY_REMOVE_REGISTER_RELATED_REPLY_LEMMA:
!device_characteristics device1 device2 serviced_request.
  device2 = dma_request_served device_characteristics device1 serviced_request
  ==>
  (device2.dma_state.pending_register_related_memory_requests, device2.dma_state.pending_register_related_memory_replies) =
  append_reply_remove_register_related_reply
    serviced_request
    device1.dma_state.pending_register_related_memory_requests
    device1.dma_state.pending_register_related_memory_replies
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_request_served THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_REPLIES_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device11 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device12 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 serviced_request.
  device12 = dma_request_served device_characteristics device11 serviced_request /\
  device22 = dma_request_served device_characteristics device21 serviced_request /\
  device21.dma_state.pending_register_related_memory_requests = device11.dma_state.pending_register_related_memory_requests /\
  device21.dma_state.pending_register_related_memory_replies  = device11.dma_state.pending_register_related_memory_replies
  ==>
  device22.dma_state.pending_register_related_memory_requests = device12.dma_state.pending_register_related_memory_requests /\
  device22.dma_state.pending_register_related_memory_replies  = device12.dma_state.pending_register_related_memory_replies
Proof
INTRO_TAC THEN
IRTAC DMA_REQUEST_SERVED_APPEND_REPLY_REMOVE_REGISTER_RELATED_REPLY_LEMMA THEN
IRTAC DMA_REQUEST_SERVED_APPEND_REPLY_REMOVE_REGISTER_RELATED_REPLY_LEMMA THEN
LRTAC THEN
LRTAC THEN
RLTAC THEN
EQ_PAIR_ASM_TAC THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_PRESERVES_MEMORY_REQUESTS_REPLIES_EQ_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device11 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device21 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device12 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device22 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 serviced_request.
  device12 = dma_request_served device_characteristics device11 serviced_request /\
  device22 = dma_request_served device_characteristics device21 serviced_request /\
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device11 device21
  ==>
  MEMORY_REQUESTS_REPLIES_EQ device_characteristics device12 device22
Proof
INTRO_TAC THEN
ETAC stateTheory.MEMORY_REQUESTS_REPLIES_EQ THEN
REPEAT CONJ_TAC THENL
[
 INST_IMP_TAC DMA_REQUEST_SERVED_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_REPLIES_LEMMA THEN STAC
 ,
 INST_IMP_TAC DMA_REQUEST_SERVED_PRESERVES_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_REPLIES_LEMMA THEN STAC
 ,
 INTRO_TAC THEN
 AITAC THEN
 IRTAC DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
 AITAC THEN
 IRTAC DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
 AITAC THEN
 ETAC stateTheory.schannel THEN
 INST_IMP_TAC internal_operation_lemmasTheory.APPENDED_REPLY_REMOVED_REQUEST_CHANNEL_TRANSFERS_PENDING_ACCESSES_LEMMA THEN
 STAC
]
QED

Theorem DMA_REQUEST_SERVED_NOT_ADDING_PENDING_REGISTER_RELATED_MEMORY_REQUESTS_LEMMA:
!device_characteristics device1 device2 serviced_request.
  device2 = dma_request_served device_characteristics device1 serviced_request
  ==>
  LIST1_IN_LIST2 device2.dma_state.pending_register_related_memory_requests device1.dma_state.pending_register_related_memory_requests
Proof
INTRO_TAC THEN
PTAC operationsTheory.dma_request_served THEN
LRTAC THEN
RECORD_TAC THEN
PTAC operationsTheory.append_reply_remove_register_related_reply THENL
[
 EQ_PAIR_ASM_TAC THEN
 IRTAC internal_operation_lemmasTheory.REMOVE_PENDING_REQUEST_IMPLIES_LIST1_IN_LIST2_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 ASM_REWRITE_TAC [lists_lemmasTheory.LIST1_IN_LIST2_REFL_LEMMA]
]
QED

Theorem DMA_REQUEST_SERVED_PRESERVES_PIPELINES_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 channel_id serviced_request.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  device2 = dma_request_served device_characteristics device1 serviced_request
  ==>
  (schannel device2 channel_id).queue = (schannel device1 channel_id).queue
Proof
INTRO_TAC THEN
IRTAC DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
AIRTAC THEN
RW_HYPS_TAC stateTheory.schannel THEN
PTAC operationsTheory.APPENDED_REPLY_REMOVED_REQUEST_CHANNEL THEN
PTAC operationsTheory.append_reply_remove_request_channel THEN
LRTAC THEN
RECORD_TAC THEN
STAC
QED

Theorem DMA_REQUEST_SERVED_NOT_ADDING_REQUESTS_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 serviced_request requests1 requests2.
  device2 = dma_request_served device_characteristics device1 serviced_request /\
  requests1 = channel_requests device_characteristics device1 /\
  requests2 = channel_requests device_characteristics device2
  ==>
  LIST1_IN_LIST2 requests2 requests1
Proof
INTRO_TAC THEN
PTAC listsTheory.LIST1_IN_LIST2 THEN
ETAC listTheory.EVERY_MEM THEN
INTRO_TAC THEN
BETA_TAC THEN
FIRTAC dma_pending_requests_lemmasTheory.MEM_DMA_PENDING_REQUESTS_CHANNELS_IMP_SOME_VALID_CHANNEL_LEMMA THEN
AXTAC THEN
IRTAC DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
AITAC THEN
ETAC (GSYM stateTheory.schannel) THEN
ETAC operationsTheory.APPENDED_REPLY_REMOVED_REQUEST_CHANNEL THEN
IRTAC APPEND_REPLY_REMOVE_REQUEST_CHANNEL_NOT_EXPANDING_PENDING_REQUESTS_LEMMA THEN
PTAC operationsTheory.collect_pending_requests THEN
LRTAC THEN
ETAC listTheory.MEM_APPEND THEN
RW_HYPS_TAC listTheory.MEM THEN
SPLIT_ASM_DISJS_TAC THENL
[
 PTAC operationsTheory.collect_pending_fetch_bd_request THENL
 [
  EQ_PAIR_ASM_TAC THEN
  LRTAC THEN
  ETAC listTheory.MEM THEN
  SOLVE_F_ASM_TAC
  ,
  EQ_PAIR_ASM_TAC THEN
  LRTAC THEN
  ETAC listTheory.MEM THEN
  REMOVE_F_DISJUNCTS_TAC THEN
  RLTAC THEN
  AIRTAC THEN
  REPEAT (WEAKEN_TAC is_forall) THEN
  IRTAC dma_pending_requests_lemmasTheory.SOME_PENDING_FETCHING_BD_REQUEST_IMPLIES_MEM_CHANNEL_REQUESTS_LEMMA THEN
  STAC
 ]
 ,
 EQ_PAIR_ASM_TAC THEN
 WEAKEN_TAC is_forall THEN
 AIRTAC THEN
 WEAKEN_TAC is_forall THEN WEAKEN_TAC is_forall THEN
 IRTAC dma_pending_requests_lemmasTheory.MEM_UPDATING_BD_REQUEST_IMPLIES_MEM_CHANNEL_REQUESTS_LEMMA THEN
 STAC
 ,
 EQ_PAIR_ASM_TAC THEN
 WEAKEN_TAC is_forall THEN WEAKEN_TAC is_forall THEN
 AIRTAC THEN
 WEAKEN_TAC is_forall THEN
 IRTAC dma_pending_requests_lemmasTheory.MEM_TRANSFERRING_DATA_REQUEST_IMPLIES_MEM_CHANNEL_REQUESTS_LEMMA THEN
 STAC 
 ,
 EQ_PAIR_ASM_TAC THEN
 WEAKEN_TAC is_forall THEN WEAKEN_TAC is_forall THEN WEAKEN_TAC is_forall THEN
 AIRTAC THEN
 IRTAC dma_pending_requests_lemmasTheory.MEM_WRITING_BACK_BD_REQUEST_IMPLIES_MEM_CHANNEL_REQUESTS_LEMMA THEN
 STAC
]
QED

Theorem DMA_WRITE_REQUEST_SERVED_PRESERVED_PENDING_ACCESSES_REPLIES_FETCHING_BD_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 tag bytes channel_id address_bytes tag_write.
   VALID_CHANNEL_ID device_characteristics channel_id /\
   device2 = dma_request_served device_characteristics device1 ([], request_write address_bytes tag_write) /\
   SOME (bytes, tag) = (schannel device2 channel_id).pending_accesses.replies.fetching_bd
   ==>
   SOME (bytes, tag) = (schannel device1 channel_id).pending_accesses.replies.fetching_bd
Proof
INTRO_TAC THEN
IRTAC DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
AIRTAC THEN
ETAC (GSYM stateTheory.schannel) THEN
PTAC operationsTheory.APPENDED_REPLY_REMOVED_REQUEST_CHANNEL THEN
PTAC operationsTheory.append_reply_remove_request_channel THEN
LRTAC THEN
RECORD_TAC THEN
ETAC listTheory.FOLDL THEN
ETAC operationsTheory.append_reply_remove_request_operation THEN
ETAC internal_operation_lemmasTheory.APPEND_REPLY_REMOVE_REQUEST_WRITING_BACK_BD_PRESERVES_PENDING_ACCESSES_REPLIES_FETCHING_BD_LEMMA THEN
ETAC internal_operation_lemmasTheory.APPEND_REPLY_REMOVE_REQUEST_TRANSFERRING_DATA_PRESERVES_PENDING_ACCESSES_REPLIES_FETCHING_BD_LEMMA THEN
ETAC internal_operation_lemmasTheory.APPEND_REPLY_REMOVE_REQUEST_UPDATING_BD_PRESERVES_PENDING_ACCESSES_REPLIES_FETCHING_BD_LEMMA THEN
PTAC operationsTheory.append_reply_remove_request_fetching_bd THEN (TRY STAC) THEN
LRTAC THEN
PTAC operationsTheory.fetching_bd_request_served THEN
SOLVE_F_ASM_TAC
QED

Theorem DMA_REQUEST_SERVED_NOT_REMOVED_IMPLIES_PRESTATE_REQUEST_LEMMA:
!(device_characteristics : ('bd_type, 'channel_index_width, 'environment_type, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_characteristics_type)
 (device1 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 (device2 : ('bd_type, 'channel_index_width, 'function_state_type, 'interconnect_address_width, 'internal_state_type, 'tag_width) device_state_type)
 served_request channel_id request.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  device2 = dma_request_served device_characteristics device1 ([], served_request) /\
  (schannel device2 channel_id).pending_accesses.requests.fetching_bd = SOME request
  ==>
  (schannel device1 channel_id).pending_accesses.requests.fetching_bd = SOME request
Proof
INTRO_TAC THEN
IRTAC DMA_REQUEST_SERVED_APPENDS_REPLY_REMOVES_REQUEST_ALL_CHANNELS_LEMMA THEN
AIRTAC THEN
ETAC (GSYM stateTheory.schannel) THEN
PTAC operationsTheory.APPENDED_REPLY_REMOVED_REQUEST_CHANNEL THEN
IRTAC APPEND_REPLY_REMOVE_REQUEST_CHANNEL_NOT_EXPANDING_PENDING_REQUESTS_LEMMA THEN
AIRTAC THEN
STAC
QED

val _ = export_theory();
