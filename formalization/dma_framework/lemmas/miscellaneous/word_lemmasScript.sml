open HolKernel Parse boolLib bossLib helper_tactics;

val _ = new_theory "word_lemmas";

Theorem WORD_LEQ_INC_NEQ_ZERO_IMP_WORD_LEQ_INC_LEMMA:
!x y.
  x <=+ y /\
  y + 1w <> 0w
  ==>
  x <=+ y + 1w
Proof
INTRO_TAC THEN
CCONTR_TAC THEN
RW_HYP_LEMMA_TAC wordsTheory.WORD_NOT_LOWER_EQUAL THEN
INST_IMP_TAC wordsTheory.WORD_LOWER_LOWER_EQ_TRANS THEN
RW_HYP_LEMMA_TAC wordsTheory.WORD_ADD_COMM THEN
RW_HYP_LEMMA_TAC wordsTheory.WORD_ADD_LEFT_LO2 THEN
SPLIT_ASM_DISJS_TAC THENL
[
 SPLIT_ASM_TAC THEN
 HYP_CONTR_NEQ_LEMMA_TAC wordsTheory.WORD_LO_word_T_L
 ,
 ALL_LRTAC THEN
 RW_HYP_LEMMA_TAC wordsTheory.WORD_ADD_LINV THEN
 RW_HYP_LEMMA_TAC wordsTheory.WORD_ADD_LINV THEN
 CONTR_NEG_ASM_TAC boolTheory.EQ_REFL
]
QED

Theorem NON_ZERO_SUC_LT_IMP_LT_SUC_LEMMA:
!n (index : 'a word).
  n2w (SUC n) <> 0w : 'a word /\
  index <=+ n2w n
  ==>
  index <=+ n2w (SUC n)
Proof
INTRO_TAC THEN
ETAC wordsTheory.n2w_SUC THEN
ITAC WORD_LEQ_INC_NEQ_ZERO_IMP_WORD_LEQ_INC_LEMMA THEN
STAC
QED

(*
x < y + 1
----------
x <= y
##########Contradiction
x < y + 1
x > y
----------
F
##########
y < x
x < y + 1
----------
F
##########
y < y + 1                   //from x > y and x < y + 1
y < 1 + y                   //from above
1 <> 0 /\ (y = 0 \/ y < -1) //wordsTheory.WORD_ADD_RIGHT_LO2
y = 0 \/ y < -1             //from previous
#########
y < x
x < y + 1
y = 0 \/ y < -1
---------------
y < x
x < y + 1
y < -1
--------------
y < x
x < y + 1
y < UINT_MAXw //wordsTheory.WORD_NEG_1
-------------
y < x
x < y + 1
y <> UINT_MAXw //wordsTheory.WORD_LOWER_NOT_EQ
--------------
w2n y < w2n x        //wordsTheory.WORD_LO
w2n x < w2n (y + 1)  //wordsTheory.WORD_LO
y <> UINT_MAXw
--------------
w2n y < w2n x
w2n x < w2n (y + 1)
w2n (y + 1) = if y = UINT_MAXw then dimword (: 'a) else w2n (y + 1) //y <> UINT_MAXw
-------------
w2n y < w2n x
w2n x < if y = UINT_MAXw then dimword (: 'a) else w2n (y + 1) //rewrite with equality.
-------------
w2n y < w2n x
w2n x < w2n y + 1  //wordsTheory.w2n_plus1
-----------------****
w2n y < w2n x
w2n x = w2n y \/ w2n x < w2n y //prim_recTheory.LESS_THM
-----------------
Case:
-w2n y < w2n x /\ w2n x = w2n y: w2n y < w2n y. 
-w2n y < w2n x /\ w2n x < w2n y: w2n y < w2n y (arithmeticTheory.LESS_TRANS)
Contradiction by prim_recTheory.LESS_REFL
*)
Theorem LT_MINUS_ONE_IMPLIES_W2N_SUC_EQ_W2N_PLUS_ONE_LEMMA:
!y.
  y <+ -1w
  ==>
  w2n (y + 1w) = w2n y + 1
Proof
INTRO_TAC THEN
ETAC wordsTheory.WORD_NEG_1 THEN
IRTAC wordsTheory.WORD_LOWER_NOT_EQ THEN
ETAC wordsTheory.w2n_plus1 THEN
ASM_REWRITE_TAC []
QED

Theorem MIDDLE_WORD_IMPLIES_F_LEMMA:
!x y.
  x <+ 1w + y /\
  y <+ x /\
  y <+ -1w
  ==>
  F
Proof
INTRO_TAC THEN
IRTAC LT_MINUS_ONE_IMPLIES_W2N_SUC_EQ_W2N_PLUS_ONE_LEMMA THEN
RW_HYP_LEMMA_TAC wordsTheory.WORD_ADD_COMM THEN
ETAC wordsTheory.WORD_LO THEN
LRTAC THEN
ETAC (GSYM arithmeticTheory.ADD1) THEN
ETAC prim_recTheory.LESS_THM THEN
SPLIT_ASM_DISJS_TAC THENL
[
 LRTAC THEN
 IRTAC prim_recTheory.LESS_REFL THEN
 STAC
 ,
 FIRTAC arithmeticTheory.LESS_TRANS THEN
 IRTAC prim_recTheory.LESS_REFL THEN
 STAC
]
QED

Theorem WORD_LT_SUC_IMPLIES_LEQ_LEMMA:
!x y.
  x <+ y + 1w
  ==>
  x <=+ y
Proof
INTRO_TAC THEN
CCONTR_TAC THEN
ETAC wordsTheory.WORD_NOT_LOWER_EQUAL THEN
RW_HYP_LEMMA_TAC wordsTheory.WORD_ADD_COMM THEN
FITAC wordsTheory.WORD_LOWER_TRANS THEN
IRTAC ((GEN_ALL o #1 o EQ_IMP_RULE o SPEC_ALL) wordsTheory.WORD_ADD_RIGHT_LO2) THEN
WEAKEN_TAC is_neg THEN
SPLIT_ASM_DISJS_TAC THENL
[
 LRTAC THEN
 ASSUME_TAC (GSYM wordsTheory.word_T_not_zero) THEN
 ETAC ((GSYM o last o CONJUNCTS) wordsTheory.WORD_LO_word_T) THEN
 IRTAC MIDDLE_WORD_IMPLIES_F_LEMMA THEN
 STAC
 ,
 IRTAC MIDDLE_WORD_IMPLIES_F_LEMMA THEN
 STAC
]
QED

Theorem WORD_LEQ_SUC_IMPLIES_LEQ_OR_EQ_SUC_LEMMA:
!x y.
  x <=+ y + 1w
  ==>
  x <=+ y \/ x = y + 1w
Proof
INTRO_TAC THEN
RW_HYP_LEMMA_TAC wordsTheory.WORD_LOWER_OR_EQ THEN
SPLIT_ASM_DISJS_TAC THENL
[
 IRTAC WORD_LT_SUC_IMPLIES_LEQ_LEMMA THEN STAC
 ,
 STAC
]
QED

Theorem SUC_NEQ_LEMMA:
!x. x + 1w <> x
Proof
INTRO_TAC THEN
CCONTR_TAC THEN
ETAC wordsTheory.WORD_ADD_INV_0_EQ THEN
RW_HYP_LEMMA_TAC (GSYM wordsTheory.WORD_NEG1_MUL_LCANCEL) THEN
ETAC wordsTheory.WORD_MULT_CLAUSES THEN
HYP_CONTR_NEQ_LEMMA_TAC wordsTheory.word_T_not_zero
QED

Theorem NEQ_ZERO_IMPLIES_PRE_LT_LEMMA:
!i.
  i <> 0w
  ==>
  i - 1w <+ i
Proof
INTRO_TAC THEN
CCONTR_TAC THEN
ETAC wordsTheory.WORD_NOT_LOWER THEN
ETAC wordsTheory.word_sub_def THEN
RW_HYP_LEMMA_TAC wordsTheory.WORD_ADD_COMM THEN
ETAC wordsTheory.WORD_ADD_RIGHT_LS2 THEN
SPLIT_ASM_DISJS_TAC THENL
[
 CONTR_ASMS_TAC
 ,
 HYP_CONTR_NEQ_LEMMA_TAC wordsTheory.word_T_not_zero
 ,
 ETAC wordsTheory.WORD_NEG_NEG THEN
 ETAC wordsTheory.WORD_LO THEN
 ETAC wordsTheory.w2n_eq_0 THEN
 ETAC wordsTheory.word_1_n2w THEN
 ETAC arithmeticTheory.ONE THEN
 IRTAC prim_recTheory.LESS_SUC_IMP THEN
 AIRTAC THEN
 HYP_CONTR_NEQ_LEMMA_TAC prim_recTheory.NOT_LESS_0
]
QED

Theorem LEQ_NOT_ZERO_IMPLIES_PRE_LEQ_LEMMA:
!x y.
  x <=+ y /\
  x <> 0w
  ==>
  x - 1w <=+ y
Proof
INTRO_TAC THEN
IRTAC NEQ_ZERO_IMPLIES_PRE_LT_LEMMA THEN
IRTAC wordsTheory.WORD_LOWER_LOWER_EQ_TRANS THEN
IRTAC wordsTheory.WORD_LOWER_IMP_LOWER_OR_EQ THEN
STAC
QED

Theorem LE_IMPLIES_NOT_ZERO_LEMMA:
!x y.
  x <+ y
  ==>
  y <> 0w
Proof
INTRO_TAC THEN
CCONTR_TAC THEN
ETAC boolTheory.NOT_CLAUSES THEN
LRTAC THEN
HYP_CONTR_NEQ_LEMMA_TAC wordsTheory.WORD_LO_word_0R
QED

Theorem LE_IMPLIES_LEQ_PRED_LEMMA:
!x y.
  x <+ y
  ==>
  x <=+ y - 1w
Proof
INTRO_TAC THEN
ITAC LE_IMPLIES_NOT_ZERO_LEMMA THEN
CCONTR_TAC THEN
ETAC wordsTheory.WORD_NOT_LOWER_EQUAL THEN
ETAC wordsTheory.WORD_LO THEN
IRTAC wordsTheory.SUC_WORD_PRED THEN
RLTAC THEN
ETAC arithmeticTheory.ADD1 THEN
ETAC arithmeticTheory.LE_LT1 THEN
ETAC arithmeticTheory.LESS_OR_EQ THEN
SPLIT_ASM_DISJS_TAC THENL
[
 IRTAC arithmeticTheory.LESS_IMP_LESS_OR_EQ THEN
 IRTAC arithmeticTheory.LESS_EQ_LESS_TRANS THEN
 IRTAC prim_recTheory.LESS_REFL THEN
 STAC
 ,
 RLTAC THEN
 IRTAC prim_recTheory.LESS_REFL THEN
 STAC
]
QED

Theorem NEQ_ZERO_LE_IMPLIES_PRED_LE_LEMMA:
!x y.
  x <> 0w /\
  x <+ y
  ==>
  x - 1w <+ y
Proof
INTRO_TAC THEN
ETAC wordsTheory.WORD_LO THEN
IRTAC wordsTheory.SUC_WORD_PRED THEN
RLTAC THEN
IRTAC prim_recTheory.SUC_LESS THEN
STAC
QED

Theorem NEQ_ZERO_EQ_IMPLIES_PRE_LE_LEMMA:
!x y.
  x <> 0w /\
  x = y
  ==>
  x − 1w <+ y
Proof
INTRO_TAC THEN
ETAC wordsTheory.WORD_LO THEN
LRTAC THEN
IRTAC wordsTheory.SUC_WORD_PRED THEN
RLTAC THEN
REWRITE_TAC [prim_recTheory.LESS_SUC_REFL]
QED

Theorem NEQ_ZERO_IMPLIES_GT_PRED_LEMMA:
!x.
  x <> 0w
  ==>
  x >+ x - 1w
Proof
INTRO_TAC THEN
MATCH_MP_TAC (REWRITE_RULE [GSYM wordsTheory.WORD_HIGHER] NEQ_ZERO_EQ_IMPLIES_PRE_LE_LEMMA) THEN
STAC
QED

Theorem NEQ_ZERO_GT_IMPLIES_GT_PRED_LEMMA:
!x y.
  x <> 0w /\
  y >+ x
  ==>
  y >+ x - 1w
Proof
INTRO_TAC THEN
ETAC wordsTheory.WORD_HIGHER THEN
IRTAC NEQ_ZERO_LE_IMPLIES_PRED_LE_LEMMA THEN
STAC
QED




(*
open integerTheory
open arithmeticTheory
open prim_recTheory
open wordTheory;
open numeral_wordTheory;


wordsTheory.w2n_n2w             ∀n. w2n (n2w n) = n MOD dimword (:α)
wordsTheory.n2w_mod             ∀n. n2w (n MOD dimword (:α)) = n2w n
wordsTheory.n2w_dimword         n2w (dimword (:α)) = 0w
wordsTheory.UINT_MAX_def        UINT_MAX (:α) = dimword (:α) − 1
wordsTheory.word_T_def          UINT_MAXw = n2w (UINT_MAX (:α))
wordsTheory.ZERO_LT_UINT_MAX    0 < UINT_MAX (:α)
wordsTheory.WORD_LS_T           ∀w. w ≤₊ UINT_MAXw
wordsTheory.word_eq_n2w         ∀n. n2w n = -1w ⇔ MOD_2EXP_MAX (dimindex (:α)) n
wordsTheory.w2n_plus1           ∀a. w2n a + 1 = if a = UINT_MAXw then dimword (:α) else w2n (a + 1w)
wordsTheory.w2w_lt              ∀w. w2n (w2w w) < dimword (:α)

CASE: n2w y = -1w
SUC y < dimword (: 'a)
n2w y = -1w


SUC y < dimword (: 'a)
n2w y = -1w
----------------------
SUC y < dimword (: 'a)
w2n (n2w y) = w2n -1w = dimword (:α) − 1 ==> [since 0 < dimword] 
w2n (n2w y) + 1 = (w2n -1w) + 1 = (dimword (:α) − 1) + 1 = dimword

w2n (n2w y) + 1 = dimword

SUC y < SUC (w2n (n2w y)) [since sUC y < dimword and w2n (n2w y) + 1 = dimword]

y < (w2n (n2w y)) = y MOD dimword (: 'a) = y [since y < dimword]

y < y
Contradiction by prim_recTheory.LESS_REFL
*)
Theorem SUC_LT_DIMWORD_AND_N2w_EQ_MINUS_ONE_IMPLIES_SUC_W2N_N2W_EQ_DIMWORD_LEMMA:
!x.
  SUC x < dimword (: 'a) /\
  n2w x = (-1w : 'a word)
  ==>
  SUC (w2n (n2w x : 'a word)) = dimword (: 'a)
Proof
INTRO_TAC THEN
ETAC wordsTheory.w2n_11 THEN
(fn (A, t) =>
 let val from_dim_type_variable = (hd o type_vars o type_of o #2 o dest_comb o #2 o dest_comb o #1 o dest_comb o last o #2 o strip_comb o concl) wordsTheory.w2n_minus1 in
 let val from_w2n_type_variable = (hd o type_vars o type_of o #1 o dest_comb o lhs o concl) wordsTheory.w2n_minus1 in
 let val assumption = hd (filter (not o is_eq) A) in
 let val to_type_variable = (hd o type_vars o type_of o #2 o dest_comb o #2 o dest_comb) assumption in
 let val new_assumption_theorem = INST_TYPE [from_dim_type_variable |-> to_type_variable, from_w2n_type_variable |-> to_type_variable] wordsTheory.w2n_minus1 in
   ASSUME_TAC new_assumption_theorem (A, t)
 end end end end end) THEN
LRTAC THEN
(fn (A, t) =>
 let val from_type_variable = (hd o type_vars o type_of o #2 o dest_comb o #2 o dest_comb o concl) wordsTheory.ZERO_LT_dimword in
 let val assumption = hd (filter is_eq A) in
 let val to_type_variable = (hd o type_vars o type_of o #2 o dest_comb o hd o #2 o strip_comb o rhs) assumption in
 let val new_assumption_theorem = INST_TYPE [from_type_variable |-> to_type_variable] wordsTheory.ZERO_LT_dimword in
   ASSUME_TAC new_assumption_theorem (A, t)
 end end end end) THEN
RW_HYP_LEMMA_TAC (GSYM prim_recTheory.INV_SUC_EQ) THEN
IRTAC (SPEC “0 : num” arithmeticTheory.LESS_OR) THEN
ETAC arithmeticTheory.ADD1 THEN
ETAC arithmeticTheory.ADD THEN
IRTAC arithmeticTheory.SUB_ADD THEN
LRTAC THEN
STAC
QED

Theorem SUC_W2N_N2W_EQ_DIMWORD_SUC_LT_DIMWORD_IMPLIES_LT_W2N_N2W_LEMMA:
!x.
  SUC (w2n (n2w x : 'a word)) = dimword (: 'a) /\
  SUC x < dimword (: 'a)
  ==>
  x < w2n (n2w x : 'a word)
Proof
INTRO_TAC THEN
RLTAC THEN
ETAC arithmeticTheory.LESS_MONO_EQ THEN
STAC
QED

Theorem LT_DIMWORD_IMPLIES_ID_MOD_LEMMA:
!x y.
  y = dimword (: 'α) /\
  x < y
  ==>
  x = x MOD y
Proof
INTRO_TAC THEN
IRTAC arithmeticTheory.LESS_MOD THEN
STAC
QED

Theorem SUC_LT_DIMWORD_AND_SUC_W2N_N2W_EQ_DIMWORD_IMPLIES_LT_ITSELF_LEMMA:
!x.
  SUC x < dimword (: 'a) /\
  SUC (w2n (n2w x : 'a word)) = dimword (: 'a)
  ==>
  x < x
Proof
INTRO_TAC THEN
ITAC prim_recTheory.SUC_LESS THEN
IRTAC SUC_W2N_N2W_EQ_DIMWORD_SUC_LT_DIMWORD_IMPLIES_LT_W2N_N2W_LEMMA THEN
ITAC LT_DIMWORD_IMPLIES_ID_MOD_LEMMA THEN
ETAC wordsTheory.w2n_n2w THEN
RLTAC THEN
STAC
QED

Theorem SUC_LT_DIMWORD_AND_N2W_EQ_MINUS_ONE_IMPLIES_F_LEMMA:
!x.
  SUC x < dimword (: 'a) /\
  n2w x = (-1w : 'a word)
  ==>
  F
Proof
INTRO_TAC THEN
ITAC SUC_LT_DIMWORD_AND_N2w_EQ_MINUS_ONE_IMPLIES_SUC_W2N_N2W_EQ_DIMWORD_LEMMA THEN
ITAC SUC_LT_DIMWORD_AND_SUC_W2N_N2W_EQ_DIMWORD_IMPLIES_LT_ITSELF_LEMMA THEN
HYP_CONTR_NEQ_LEMMA_TAC prim_recTheory.LESS_REFL
QED

Theorem SUC_EQ_ZERO_IMPLIES_F_LEMMA:
!n.
  SUC n < dimword (: 'a) /\
  n2w n + 1w = 0w : 'a word
  ==>
  F
Proof
INTRO_TAC THEN
ETAC wordsTheory.WORD_ADD_EQ_SUB THEN
ETAC wordsTheory.WORD_SUB_LZERO THEN
IRTAC SUC_LT_DIMWORD_AND_N2W_EQ_MINUS_ONE_IMPLIES_F_LEMMA THEN
SOLVE_F_ASM_TAC
QED

(*
n2w y + 1w <+ x
x <=+ n2w y
----
F
=================
n2w y + 1w <+ x
x <=+ n2w y
n2w y + 1w <+ n2w y
----
F
=================wordsTheory.WORD_ADD_LEFT_LO2
n2w y + 1w <+ x
x <=+ n2w y
n2w y <> 0w
-1w <+ n2w y \/ n2w y = -1w
----
F
#################

CASE: -1w <+ n2w y
SUC y < dimword (: 'a) /\
n2w y <> 0w
-1w <+ n2w y

Contradiction by wordsTheory.WORD_LO_word_T_L
*)

Theorem GT_SUC_IMPLIES_GT_LEMMA:
!(x : 'a word) y.
  SUC y < dimword (: 'a) /\
  x >+ n2w y + 1w
  ==>
  x >+ n2w y
Proof
INTRO_TAC THEN
CCONTR_TAC THEN
ETAC wordsTheory.WORD_NOT_HIGHER THEN
ETAC wordsTheory.WORD_HIGHER THEN
IRTAC wordsTheory.WORD_LOWER_LOWER_EQ_TRANS THEN
RW_HYP_LEMMA_TAC wordsTheory.WORD_ADD_COMM THEN
ETAC wordsTheory.WORD_ADD_LEFT_LO2 THEN
WEAKEN_TAC is_neg THEN
SPLIT_ASM_DISJS_TAC THENL
[
 HYP_CONTR_NEQ_LEMMA_TAC wordsTheory.WORD_LO_word_T_L
 ,
 IRTAC SUC_LT_DIMWORD_AND_N2W_EQ_MINUS_ONE_IMPLIES_F_LEMMA THEN STAC
]
QED

Theorem LEQ_MAX_IMPLIES_DISTINCT_GT_MAX_LEMMA:
!n (index : 'b word).
  SUC n < dimword (: 'b) /\
  index <=+ n2w n
  ==>
  index <> n2w n + 1w
Proof
INTRO_TAC THEN
CCONTR_TAC THEN
ETAC boolTheory.NOT_CLAUSES THEN
LRTAC THEN
ETAC wordsTheory.WORD_LOWER_OR_EQ THEN
SPLIT_ASM_DISJS_TAC THENL
[
 RW_HYP_LEMMA_TAC wordsTheory.WORD_ADD_COMM THEN
 ETAC wordsTheory.WORD_ADD_LEFT_LO2 THEN
 SPLIT_ASM_DISJS_TAC THENL
 [
  HYP_CONTR_NEQ_LEMMA_TAC wordsTheory.WORD_LO_word_T_L
  ,
  IRTAC SUC_LT_DIMWORD_AND_N2W_EQ_MINUS_ONE_IMPLIES_F_LEMMA THEN
  STAC
 ]
 ,
 HYP_CONTR_NEQ_LEMMA_TAC SUC_NEQ_LEMMA
]
QED

Theorem GT_SUC_IMPLIES_NEQ_SUC_LEMMA:
!n (index : 'channel_index_width_read word).
  SUC n < dimword (:'channel_index_width_read) /\
  index >+ n2w n + 1w
  ==>
  index <> n2w n + 1w
Proof
INTRO_TAC THEN
ETAC wordsTheory.WORD_HIGHER THEN
IRTAC wordsTheory.WORD_LOWER_NOT_EQ THEN
ASM_REWRITE_TAC [boolTheory.EQ_SYM_EQ]
QED

Theorem EQ_SUC_IMPLIES_GT_LEMMA:
!n (index : 'b word).
  SUC n < dimword (: 'b) /\
  index = n2w n + 1w
  ==>
  index >+ n2w n
Proof
INTRO_TAC THEN
CCONTR_TAC THEN
ETAC wordsTheory.WORD_NOT_HIGHER THEN
IRTAC LEQ_MAX_IMPLIES_DISTINCT_GT_MAX_LEMMA THEN
CONTR_ASMS_TAC
QED

Theorem LEQ_GT_SUC_IMPLIES_F_LEMMA:
!(x : 'a word) n.
  SUC n < dimword (: 'a) /\
  x <=+ n2w n /\
  x >+ n2w n + 1w
  ==>
  F
Proof
INTRO_TAC THEN
IRTAC GT_SUC_IMPLIES_GT_LEMMA THEN
ETAC wordsTheory.WORD_HIGHER THEN
IRTAC (ONCE_REWRITE_RULE [(GEN_ALL o SYM o last o CONJUNCTS o SPEC_ALL) boolTheory.IMP_CLAUSES] (SPECL [“n2w n : 'a word”, “x : 'a word”] wordsTheory.WORD_LOWER_EQ_ANTISYM)) THEN
STAC
QED

Theorem LEQ_IMPLIES_LEQ_SUC_LEMMA:
!n index.
  SUC n < dimword (: 'a) /\
  index <=+ n2w n : 'a word
  ==>
  index <=+ n2w (SUC n)
Proof
INTRO_TAC THEN
REWRITE_TAC [wordsTheory.n2w_SUC] THEN
CCONTR_TAC THEN
ETAC wordsTheory.WORD_NOT_LOWER_EQUAL THEN
ETAC wordsTheory.WORD_HIGHER THEN
IRTAC LEQ_GT_SUC_IMPLIES_F_LEMMA THEN
STAC
QED

Theorem SUC_LEQ_IMPLIES_LEQ_LEMMA:
!n (x : 'a word).
  SUC n < dimword (: 'a) /\
  n2w (SUC n) <=+ x
  ==>
  n2w n <=+ x
Proof
INTRO_TAC THEN
ETAC wordsTheory.n2w_SUC THEN
CCONTR_TAC THEN
ETAC wordsTheory.WORD_NOT_LOWER_EQUAL THEN
IRTAC wordsTheory.WORD_LOWER_EQ_LOWER_TRANS THEN
RW_HYP_LEMMA_TAC wordsTheory.WORD_ADD_COMM THEN
ETAC wordsTheory.WORD_ADD_LEFT_LO2 THEN
WEAKEN_TAC is_neg THEN
SPLIT_ASM_DISJS_TAC THENL
[
 HYP_CONTR_NEQ_LEMMA_TAC wordsTheory.WORD_LO_word_T_L
 ,
 IRTAC SUC_LT_DIMWORD_AND_N2W_EQ_MINUS_ONE_IMPLIES_F_LEMMA THEN STAC
]
QED

val _ = export_theory();

