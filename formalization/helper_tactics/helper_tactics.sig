signature helper_tactics =
sig

  (* Helper functions used to develop tactics. *)
  val has_subterm_property: (Term.term -> bool) -> Term.term -> (Term.term * Term.term * Term.term) option;
  val is_subterm: Term.term -> Term.term -> bool;
  val is_in : Term.term list -> Term.term -> bool;
  val not_in : Term.term list -> Term.term -> bool;
  val common_term : Term.term list -> Term.term list -> bool;
  val disjoint_terms : Term.term list -> Term.term list -> bool;
  val split_list : int -> 'a list -> ('a list * 'a list);
  val split_list_some_property : ('a -> 'b option) -> ('a list) -> ('b list * 'a list);
  val has_terms_subterm_property: (Term.term -> bool) -> Term.term list -> (Term.term * Term.term * Term.term * Term.term) option;
  val has_specified_function_application: string -> Term.term list -> (Term.term * Term.term * Term.term * Term.term) option;
  val instantiate_exist: Term.term -> Term.term list -> (Term.term * Term.term * Term.term) option;
  val instantiate_exists: Term.term -> Term.term list -> (Term.term * (Term.term * Term.term) list);
  val instantiate_specified_exist: Term.term -> Term.term -> Term.term list -> (Term.term * Term.term * Term.term) option;
  val is_instantiatable_variable : Term.term list -> Term.term -> bool;
  val substitute_term: Term.term -> Term.term -> Term.term -> Term.term;
  val substitute_terms: Term.term list -> Term.term -> Term.term -> Term.term list;

  val remove_first_occurrence: Term.term -> Term.term list -> Term.term list;

  val reverse_substitute: (Term.term list * Term.term) -> Thm.thm -> Thm.thm -> Thm.thm;
  val choose_applications: (Term.term * Term.term) list -> Term.term -> Thm.thm -> Thm.thm;
  val substitution_subgoal_validation: (Term.term -> Thm.thm) -> Term.term -> Term.term list * Term.term -> (Term.term list * Term.term) list * (Thm.thm list -> Thm.thm);
  val function_application_conv: Term.term -> Thm.thm;
  val SPECIFIC_REWRITE_TACTIC_TEMPLATE: string -> string -> string -> (Term.term list -> (Term.term * Term.term * Term.term * Term.term) option) -> (Term.term -> Thm.thm) -> (Term.term list * Term.term, Thm.thm) Abbrev.gentactic;
  val CASE_PATTERN_TO_APP_TAC: Abbrev.tactic;
  val SPLIT_SCALAR_CASE_PATTERN_TAC : bool -> Abbrev.tactic;
  val APP_SCALAR_TAC: Abbrev.tactic;
  val find_instantiation_xbody: Term.term list -> Term.term -> Term.term list -> (Term.term * Term.term option) list;
  val INSTS_EXISTS_TAC: (Term.term * Term.term option) list -> Abbrev.tactic;
  val find_matching: Term.term -> Term.term -> {redex: Term.term, residue: Term.term} list option;
  val let_conv: Term.term -> Thm.thm;
  val merge_type_matchings: {redex: Type.hol_type, residue: Type.hol_type} list -> {redex: Type.hol_type, residue: Type.hol_type} list -> {redex: Type.hol_type, residue: Type.hol_type} list option;
  val merge_term_matchings: {redex: Term.term, residue: Term.term} list -> {redex: Term.term, residue: Term.term} list -> {redex: Term.term, residue: Term.term} list option;
  val find_explicit_type_variable_instantiation: Term.term -> Term.term -> {redex: Type.hol_type, residue: Type.hol_type} list option;
  val find_explicit_variable_instantiation: Term.term list -> Term.term -> Term.term -> ({redex: Term.term, residue: Term.term} list * {redex: Type.hol_type, residue: Type.hol_type} list) option;
  val ASM_SIMP_IMP_ASM_TAC: Term.term * Term.term * ({redex: Term.term, residue: Term.term} list * {redex: Type.hol_type, residue: Type.hol_type} list) -> Term.term list * 'a -> Term.term list * 'a * (Thm.thm -> Thm.thm) * Term.term;
  val find_qimp_instantiation : Term.term -> Term.term -> ({redex : Term.term, residue : Term.term} list * {redex : Type.hol_type, residue : Type.hol_type} list) option;
  val ADD_RHS_COMPONENT_LET_PAIR_TAC : Term.term -> Term.term list * Term.term -> (Term.term list * Term.term * (Thm.thm -> Thm.thm) * Term.term);
  val SUBST_ASM_OR_CON_TAC : Term.term -> Term.term -> Term.term -> Term.term -> Abbrev.tactic;
  val genvar_term : Term.term -> Term.term;
  val SUBST_CON_TAC : Term.term -> Term.term -> Term.term ->              Abbrev.tactic;
  val SUBST_ASM_TAC : Term.term -> Term.term -> Term.term -> Term.term -> Abbrev.tactic;
  val MERGE_PAIR_EXPANSIONS_TAC : Term.term option -> Term.term -> Term.term list * Term.term -> Term.term list * Term.term * (Thm.thm -> Thm.thm) * Term.term;
  val ADD_LET_VAR_EQ_COMPONENT_ASM_TAC : Term.term -> (Term.term list * Term.term) -> (Term.term list * Term.term * (Thm.thm -> Thm.thm) * Term.term);
  val take_first : ('a -> bool) -> 'a list -> 'a list * 'a * 'a list;
  val not_var_nor_const : Term.term -> bool;
  val SUBST_SUBTERM_TAC : Term.term -> Term.term -> Term.term -> Term.term -> Term.term -> (Term.term list * Term.term) -> (Term.term list * Term.term * (Thm.thm -> Thm.thm) * Term.term * Term.term);
  val same_term : Term.term -> Term.term -> bool;
  val not_same_term : Term.term -> Term.term -> bool;
  val RW_SUBTERM_TAC : Thm.thm -> Term.term -> Term.term -> Term.term -> (Term.term list * Term.term) -> (Term.term list * Term.term * (Thm.thm -> Thm.thm) * Term.term * Term.term);
  val ADD_SUBST_VAR_EQ_CASE_COND_TAC : Term.term -> Term.term -> Term.term -> Term.term -> (Term.term list * Term.term) -> (Term.term list * Term.term * (Thm.thm -> Thm.thm) * Term.term * Term.term);
  val SUBST_SUBTERM_REFL_TAC : Term.term -> Term.term -> Term.term -> Term.term -> Term.term -> (Term.term list * Term.term) -> (Term.term list * Term.term * (Thm.thm -> Thm.thm) * Term.term * Term.term);
  val is_let_scalar : Term.term -> bool;
  val is_let_pair : Term.term -> bool;
  val REDUCE_LET_SCALAR_TAC : Term.term -> Term.term -> Term.term -> Term.term -> (Term.term list * Term.term) -> (Term.term list * Term.term * (Thm.thm -> Thm.thm) * Term.term * Term.term);
  val REDUCE_LET_VECTOR_TAC : Term.term -> Term.term -> Term.term -> Term.term -> (Term.term list * Term.term) -> (Term.term list * Term.term * (Thm.thm -> Thm.thm) * Term.term * Term.term);
  val REMOVE_XEQ_TAC : Term.term -> Term.term list -> (Term.term list * Term.term) -> (Term.term list * Term.term * (Thm.thm -> Thm.thm) * Term.term);
  val COMPOSE_SUBGOALS_GOAL_TAC : ('a list * ('b list -> 'c)) list -> ('c list -> 'd) -> 'a list * ('b list -> 'd);
  val ANT_CONJ_TO_HYP_RULE : Term.term -> Thm.thm -> Thm.thm;
  val HYPS_IMP_TO_CONJS_IMP_RULE : Thm.thm -> Term.term list -> Thm.thm;
  val neg_conj_disj_imp_simp_conv : Term.term -> Thm.thm option;
  val SIMP_ANT_RULE : Thm.thm -> Thm.thm
  val find_mismatching_instantiation :
    Term.term list ->
    {redex: Type.hol_type, residue: Type.hol_type} list ->
	{redex: Term.term, residue: Term.term} list ->
	Type.hol_type list ->
    Term.term list ->
    Term.term ->
    Term.term ->
    ({redex : Type.hol_type, residue : Type.hol_type} list *
     {redex : Term.term, residue : Term.term} list *
     Type.hol_type list *
     Term.term list *
     Term.term *
     ((Term.term * {redex: Term.term, residue: Term.term} * Term.term * ({redex : Term.term, residue : Term.term} list) * bool) list) *
     Term.term list) option;
  val is_meet :
    {redex: Type.hol_type, residue: Type.hol_type} list ->
	{redex: Term.term, residue: Term.term} list ->
	Type.hol_type list ->
	Term.term list ->
	Term.term list ->
	Term.term ->
	Term.term ->
	({redex: Type.hol_type, residue: Type.hol_type} list *
     {redex: Term.term, residue: Term.term} list *
     Type.hol_type list *
     Term.term list *
     Term.term *
     ((Term.term * {redex: Term.term, residue: Term.term} * Term.term * ({redex : Term.term, residue : Term.term} list) * bool) list) *
     bool *
     Term.term list) option;

  val ADD_RW_ASM_REFL_TAC :
	Term.term ->
	bool ->
	Term.term ->
	((Term.term * {redex: Term.term, residue: Term.term} * Term.term * ({redex : Term.term, residue : Term.term} list) * bool) list) ->
	(Term.term list * Term.term) ->
	(Term.term list * Term.term * (Thm.thm -> Thm.thm) * Term.term);

  val find_equality_instantiations : string list -> string list -> Term.term -> Term.term -> Term.term list -> Term.term list -> Type.hol_type list -> Type.hol_type list ->
                                    ({redex : Type.hol_type, residue : Type.hol_type} list *
                                     {redex : Type.hol_type, residue : Type.hol_type} list *
                                     {redex : Term.term, residue : Term.term} list *
                                     {redex : Term.term, residue : Term.term} list *
                                     Type.hol_type list *
                                     Term.term list) option;

  val uniquify_qimp_qvs : string list -> Thm.thm -> Thm.thm * (Term.term list);
  val union_lists : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list;
  val same_type : Type.hol_type -> Type.hol_type -> bool;
  val not_same_type : Type.hol_type -> Type.hol_type -> bool;
  val rename_tevs : string list -> Term.term list -> (Term.term list * string list);
  val find_tyvs : Term.term list -> Type.hol_type list;
  datatype bvar_match_type = FAIL | MATCH | FREE;
  val bvar_match : Term.term -> Term.term -> (Term.term * Term.term) list -> bvar_match_type;

(*  val is_record : Term.term -> bool;*)
  val RECORD_WITHS_ACCESS_TO_RECORD_TYPE_TAC : Abbrev.tactic;
  val RECORD_TYPE_WITH_TO_RECORD_TYPE_K_APPS_TAC : Abbrev.tactic;
  val RECORD_TYPE_K_APPS_TO_RECORD_TYPE_FIELDS_TAC : Abbrev.tactic;
  val RECORD_TYPE_FIELD_ACCESS_TO_VALUE_TAC : Abbrev.tactic;


(*  val RECORD_UPDATE_ACCESS_TAC : Abbrev.tactic;
  val RECORD_TYPE_FIELDS_UPDATE_TAC : Abbrev.tactic;
  val RECORD_TYPE_FIELDS_K_TAC : Abbrev.tactic;
  val RECORD_TYPE_FIELDS_ACCESS_TAC : Abbrev.tactic;*)
(*  val has_record_with_accesses : Term.term list -> (Term.term * Term.term * Term.term * Term.term) option;*)
(*  val is_field_access : Term.term -> bool;
  val is_record_type_fields : Term.term -> bool;
  val record_update : Term.term -> string list * Term.term list * Term.term;
  val field_update_names : (string * Term.term) list -> Term.term -> string list * Term.term list * Term.term;
  val record_eq_record_type_xthm : Term.term -> Thm.thm;
  val r_eq_r_type_fs_hyp_r_update_eq_r_type_f_update : Term.term -> Term.term -> string list -> Term.term list -> Thm.thm;*)

(*  val REDUCE_BODY_TAC : Term.term list -> Term.term list -> Term.term list * Term.term * Term.term -> Abbrev.goal list * Abbrev.validation;*)

  (* Prints execution time of a tactic.
   *)
  val BENCH_TAC : Abbrev.tactic -> Abbrev.tactic;

  (* Removes exactly one occurrence of the given term from the assumption list.
   *)
  val REMOVE_ASM_TAC : Term.term -> Abbrev.tactic;

  (*   A u {old = new} ?- t
   * ------------------------
   * A[new/old] ?- t[new/old]
   *)
  val ASM_RW_OTHERS_TAC : bool -> Term.term -> Abbrev.tactic;

  (* A u {...l..., ..., ...l..., l = r} ?- t
   * ---------------------------------------t rewritten to t' if l occurs in t
   * A u {...r..., ..., ...r...} ?- t'
   *)
  val LRTAC : Abbrev.tactic;
  val NLLRTAC : Abbrev.tactic;
  val NLRTAC : Int.int -> Abbrev.tactic;
  val ASM_LR_RW_OTHERS_KEEP_TAC : Abbrev.tactic;
  val ALL_LRTAC : Abbrev.tactic;
  val ALL_ASM_LR_RW_OTHERS_KEEP_TAC : Abbrev.tactic;

  (* A u {...r..., ..., ...r..., l = r} ?- t
   * ---------------------------------------t rewritten to t' if r occurs in t
   * A u {...l..., ..., ...l...} ?- t'
   *)
  val RLTAC : Abbrev.tactic;
  val NRLTAC : Int.int -> Abbrev.tactic;
  val ASM_RL_RW_OTHERS_KEEP_TAC : Abbrev.tactic;
  val ALL_RLTAC : Abbrev.tactic;
  val ALL_ASM_RL_RW_OTHERS_KEEP_TAC : Abbrev.tactic;

  (*
   * Uses the first term to rewrite the second term, both in the assumption
   * list.
   *)
  val ASM_RW_ASM_TAC : bool -> Term.term -> Term.term -> Abbrev.tactic;

  (*
   * Uses the first term to rewrite the second term, both in the assumption
   * list. The first term is removed from the assumption list.
   *)
  val RM_ASM_RW_ASM_TAC : Term.term -> Term.term -> Abbrev.tactic;

  (*
   * Uses the first term to rewrite the second term, both in the assumption
   * list. The first term is not removed from the assumption list.
   *)
  val KEEP_ASM_RW_ASM_TAC : Term.term -> Term.term -> Abbrev.tactic;

  (*
   * The assumption x = y is rewritten to y = x.
   *)
  val REFL_ASM_TAC : Term.term -> Abbrev.tactic;

  (*
   * All conjunctions in the assumption list are split into individual terms in
   * the assumption list.
   *)
  val SPLIT_ASM_TAC : Abbrev.tactic;

  (* Removes universal quantifiers and dischcharges the assumption of a
   * universally quantified implication, and splits the assumption in case it is
   * a conjunction into its conjuncts and adds them to the assumption list.
   *)
  val INTRO_TAC : Abbrev.tactic;

  (* Solves a goal with F among the assumptions.
   *)
  val SOLVE_F_ASM_TAC : Abbrev.tactic;

  (*
   * Given a theorem of the form A /\ B /\ C ==> D, returns a theorem of the
   * form A, B, C |- D. The nesting of conjuncts in the antecedent does not
   * matter.
   *)
  val CONJ_ANT_TO_HYP : Thm.thm -> Thm.thm;

  val CONJS_TAC : Abbrev.tactic;

  (* A u {P, P ==> Q} ?- t
   * ---------------------ADTAC
   *     A u {Q} ?- t
   *)
  val ADTAC : bool -> Abbrev.tactic;

  (* Adds P v1...vn w1...wm to the assumption list given a lemma of the form
   * '|- !x1...xn. C1 x1..xn /\ ... /\ Cm x1..xn ==> P x1...xn w1...wm', and
   * where there are assumptions in the assumption list Ci v1...vn.
   *)
  val INST_IMP_TAC : Thm.thm -> Abbrev.tactic;

  (* Transforms a goal of the form A u {!x1...xn. P ==> Q} | R to A u {Q} | R if
   * P can be instantiated to match an assumption in A.
   *)
  val INST_IMP_ASM_TAC : Abbrev.tactic;

  (* Transforms a goal of the form 'A |- t'
   * with a lemma of the form '!x1...xn. P /\ yi = fi x1...ym ==> Q'
   * to a goal of the form
   * A u {Q} u {yi = fi values} |- t[yi/fi values],
   * if A ⊇ P with appropriately instantiated xi.
   *)
  val INST_IMP_EQ_TAC : Thm.thm -> Abbrev.tactic;

  (* 'A |- t' + '|- !X. s ==> t'
   * ==>
   * A |- ?X'. s[V/(X\X')]
   *
   * V, X, X' are terms/variables, V is inferred by matching subterms of s to
   * subterms of A. X' ⊆ X are unmatched X variables.
   *)
  val INST_IMP_ASM_GOAL_TAC : Abbrev.tactic;

  (* A u {!XY. P XY ==> t(XY)} ?- t(V)
   * --------------------------------- where Y is matched against V and X against other assumptions in A.
   *      A ?- ?X'. P X'V
   *)
  val INST_IMP_ASM_MP_CON_TAC : Abbrev.tactic;

  val INST_ASM_TAC : {redex: Term.term, residue: Term.term} list * (Type.hol_type, Type.hol_type) Term.subst -> Term.term -> Term.term list * 'a -> (Term.term list * 'a * (Thm.thm -> Thm.thm) * Term.term);

  (* A u {A1, ..., An} ?- t
   * ----------------------!x1...xm. A1 x1...xm /\ ... /\ An x1...xm ==> t x1...xm
   *           -
   *)
  val IMP_LEMMA_SOLVE_GOAL_TAC : Thm.thm -> Abbrev.tactic;

  (* A u {...a...} ?- t
   * ------------
   * A u {...b...} ?- t
   *
   * a and b are subterms of an assumption.
   *
   * asm = '...a...'
   *
   * lemma: 'B |- !x1...xn. t1 /\ ... /\ (a = b)[x1...xn] /\ ... /\ tn, B is subset of A.
   *)
  val RW_ASM_LEMMA_TAC : Term.term -> Thm.thm -> Abbrev.tactic;

  (* Transforms a goal of the form 'A |- t'
   * with a lemma of the form
   * '!x1...xn. lhs = rhs'
   * to a goal of the form
   * A[rhs/lhs] |- t[rhs/lhs],
   * with appropriately instantiated xi.
   *)
  val ETAC : Thm.thm -> Abbrev.tactic;

  (* A u {...old...} ?- t
   * --------------------
   * A u {...new...} ?- t
   *
   * lemma is of the form
   * 'B |- !x1...xn. (!y11...y1m. t1) /\ ... /\ (!yp1...ypk. tp)
   * and can be instantiated to 'B |- old = new'.
   *)
  val RW_HYP_LEMMA_TAC : Thm.thm -> Abbrev.tactic;

  (* Repeteadly rewrites assumptions with given lemma.
   *)
  val ASETAC : Thm.thm -> Abbrev.tactic;

(*  val LEMMA_DISJ_NEG_TAC : Thm.thm -> Abbrev.tactic;*)

  (*  A u {a1, ..., an} ?- t
   * -----------------------
   * A u {b1, ..., bn} ?- t'
   *
   * lemma: A' |- !X. (!X1. l1 = r1) /\ ... /\ (!Xm. lm = rm), A' subset of A.
   * each ai = lj[Vj/XjX] and bi = rj[Vj/XjX], and
   * t = lj[Vj/XjX] and t' = rj[Vj/XjX] or t = t'.
   *)
(*  val LEMMA_EQ_ONCE_TAC : Thm.thm -> Abbrev.tactic;*)

  (*  A u {a1, ..., an} ?- t
   * -----------------------
   * A u {b1, ..., bn} ?- t'
   *
   * lemma: A' |- !X. (!X1. l1 = r1) /\ ... /\ (!Xm. lm = rm), A' subset of A.
   * each ai = lj[Vj/XjX] and bi = rj[Vj/XjX], and
   * t = lj[Vj/XjX] and t' = rj[Vj/XjX] or t = t'.
   *)
(*  val LEMMA_EQ_TAC : Thm.thm -> Abbrev.tactic;*)

  val LEMMA_ASM_TAC : Thm.thm -> Abbrev.tactic;

  (*  A u {a1, ..., an} ?- t
   * -----------------------
   * A u {b1, ..., bn} ?- t'
   *
   * lemma: A' |- !X. (!X1. l1 = r1) /\ ... /\ (!Xm. lm = rm), A' subset of A.
   * each ai = lj[Vj/XjX] and bi = rj[Vj/XjX], and
   * t = lj[Vj/XjX] and t' = rj[Vj/XjX] or t = t'.
   *)
  val LEMMA_TAC : Thm.thm -> Abbrev.tactic;

  (* Adds 'P v1...vn w1...wm' to the assumption list given a lemma of the form
   * '|- !x1...xn. C1 x1..xn /\ ... /\ Cm x1..xn ==> P x1...xn w1...wm', and
   * where there are assumptions in the assumption list satisfying some of
   * 'Ci v1...vn', and where the other 'Cj x1...xn' are instantiated such that
   * REWRITE_RULE [] can simplify them to true which is removed from the
   * conjuncts of the assumption of the resulting instantiated implication
   *)
  val PART_INST_IMP_TAC : Thm.thm -> Abbrev.tactic;

  (* Adds 't v1...vn' to the assumption list given a lemma of the form
   * '|- !x1...xn. t x1..xn', where instantiation_strings contains the string
   * names in order of v1...vn, with v1...vn type instantiated to match the
   * current assumption list and goal.
   *)
  val ADD_INST_TAC : Thm.thm -> string list -> Abbrev.tactic;

  (* Reduces a goal of the form A u {!x1..xn. P ==> Q} |- Q to A |- P with
   * x1...xn appropriately instantiated.
   *)
  val MATCH_MP_ASM_TAC : Term.term -> Abbrev.tactic;

  (* Instantiates a universally quantified assumption with the given term. *)
  val SPEC_ASM_TAC : Term.term -> Term.term list * Term.term -> Abbrev.goal list * Abbrev.validation;

  (* Instantiates the existentially quantified assumption matching the given
   * term with a fresh variable.
   *)
  val INST_EXIST_ASM_TAC : Term.term -> Term.term list * Term.term -> Abbrev.goal list * Abbrev.validation;

  (* Instantiates all existantially quantified assumptions with fresh variables.
   *)
  val AXTAC : Abbrev.tactic;

  (* Transforms an assumption of the form '~!x1 ... xn. P x1 ... xn' to an
   * assumption of the form 'P y1 x... yn', where yi are fresh variables.
   * This transformation is based on ~!x. P x <=> ?x. ~P x, where the fresh
   * variables are introduced when instantiation the existential term.
   *)
  val NEG_FORALL_TAC : Abbrev.tactic;

  (* Instantiates all existentially quantified variables in the goal with the
   * same names as the corresponding quantified variables.
   *)
  val INST_EXISTS_TAC : Abbrev.tactic;

  (*      A ?- ?X. t
   * ---------------------
   * A |- ?X'. t[V/(X\X')]
   *
   * V, X, X' are vectors of terms and variables, where V are identified via a
   * matching of subterms of t with subterms of A. X' is the existentially
   * quantified variables of X for which no matching was found.
   *)
  val PAXTAC : Abbrev.tactic;

  (* Instantiates the existentially quantified variables of the conclusion of a
   * goal with the names in the order the names are listen in the first
   * argument.
   *)
  val INST_EXISTS_NAMES_TAC : string list -> Abbrev.tactic;

  (* Transforms a goal of the form A |- ?x1...xn. t to A |- t such that x1...xn
   * are substituted with v1...vn and t[v1...vn/x1...xn] is in A.
   *)
  val INST_EXISTS_WITH_ASM_TAC : Abbrev.tactic;

  (* 'A ?- ?x. x = y' or 'A ?- ?x. y = x'
   * ==>
   * 'A ?- y = y
   *)
  val INST_SCALAR_EQ_EXISTS_TAC : Abbrev.tactic

  (* 'A ?- ?XY. XY' = X'Y
   * ==>
   * 'A ?- X'Y' = X'Y', where X, X', Y, X' are vectors of variables.
   *)
  val INST_VECTOR_EQ_EXISTS_TAC : Abbrev.tactic

  (* 'A ?- ?XY. XY' = X'Y
   * ==>
   * 'A ?- X'Y' = X'Y', where X, X', Y, X' are one scalar variable or vectors of
   * variables. Some existentially quantified variables occur on the left hand
   * side (X and other on the right hand side (Y), and may be interleaved
   * arbitrarily in the sense that not all left hand side variables must occur
   * first in the quantification (X) and then all right hand side variables (Y).
   *)
  val INST_EQ_EXISTS_TAC : Abbrev.tactic;

  (* A ?- ?x. t(x) = t(t1)    A ?- ?x. t(x) = t(t1)
   * --------------------- or ---------------------
   *         -                         -
   *)
  val EXISTS_PAT_TAC : Abbrev.tactic;

  (* A u {~?x. P x} ?- t
   * -------------------
   * A u {!x. ~P x} ?- t
   *)
  val ASM_NOT_EXISTS_TO_FORALL_NOT_TAC : Abbrev.tactic;

  val EXISTS_CONNECTIVE_TAC : Abbrev.tactic;

  (* A ?- ?x1...xi...xj...xn. ... @ xi = ti @ ... @ tj = xj @ ...
   * ----------------------------------------------------------------------------
   * A ?- ?x1...xi-1, xi+1...xj-1, xj+1...xn. ... @ ti = ti @ ... @ tj = tj @ ...
   *
   * @ stands for a logical connective (negation, conjunction, disjunction,
   * implication, exists, forall.
   *
   * Instantiates existantially quantified variables occurring on one side of an
   * equation with the term on the other side, and performs this operation as
   * long as such equations occur as connectives in the conclusion of the goal,
   * and then removes those equations.
   *)
  val EXISTS_EQ_TAC : Abbrev.tactic;

  (* Splits a all disjunctions in the assumptions into subgoals.
   *)
  val SPLIT_ASM_DISJS_TAC : Abbrev.tactic;

  (* '{A, ..., B} |- C'
   * ==>
   * '|- A /\ B ==> C'
   *)
  val HYP_TO_CONJ_RULE : Thm.thm -> Thm.thm;

  (* '|- A /\ ... lhs = rhs ... /\ B ==> C'
   * ==>
   * '|- A /\ ... /\ B ==> C', with lhs not occuring anywhere else in the goal.
   *)
  val RM_ANT_CONJ_SINGLE_LHS_EQS_ANT_RULE : Thm.thm -> Thm.thm;

  (* '{a, ..., a} u ... u {b, ..., b} u A ?- t'
   * ==>
   * 'A ?- t'
   *)
  val REMOVE_DUPLICATE_ASMS_TAC : Abbrev.tactic;

  (* 'A u {l1 = r1...ln = rn} ?- t'
   * ==>
   * 'A ?- t', where each li does not occur in any other assumption nor t. There
   * might be equations whose left hand side occurs in another assumption whose
   * left hand side does not occur in another assumption nor the conclusion, in
   * that case both these equations are removed.
   *)
  val RM_SINGLE_LHS_ASMS_TAC : Abbrev.tactic;

  (* '{var1 = t1, ..., tn = varn} u A ?- t'
   * ==>
   * 'A ?- t',
   *
   * where vi only ony occurs only among all assumptions and the conclusion t.
   *)
  val REMOVE_SINGLE_VAR_EQ_ASMS_TAC : Abbrev.tactic;

  (* A u {t1 = t1, ..., tn = tn} ?- t
   * ==>
   * A ?- t
   *)
  val RM_ASM_IDS_TAC : Abbrev.tactic;

  (* '|- !x1...xn. A /\ ... /\  B /\ ... /\ C ==> D' +
   * '|- !x1...xn. A /\ ... /\ ~B /\ ... /\ C ==> D'
   * ==>
   * '|- !x1...xn. A /\ ... /\ C ==> D'
   *)
  val MERGE_IMP_LEM_RULE : Thm.thm -> Thm.thm -> Thm.thm;

  (* '|- !x1...xn y. ...A /\ y = c1 /\ B... ==> C'
   * ...
   * '|- !x1...xn y. ...A /\ y = cm /\ B... ==> C'
   * ==>
   * '|- !x1...xn. ...A /\ B... ==> C'
   *
   * Where the possible values of f x1...xn are {c1...cm}, and n may be 0 and y
   * may or may not be quantified.
   *)
  val MERGE_IMP_BOOL_CASE_RULE : Thm.thm list -> Thm.thm;

  (* '|- !X y. A /\ ... y = f X value1 ... /\ B ==> C'
   * ...
   * '|- !X y. A /\ ... y = f X valuen ... /\ B ==> C'
   * ==>
   * '|- !name_of_quantifier X y. A /\ ... y = f X name_of_quantifier ... /\ B ==> C'
   *
   * where value1...valuen are all possible values of the last argument to f.
   *)
  val MERGE_IMP_FUN_ARG_CASE_RULE : string -> Thm.thm list -> Thm.thm;

  (* '|- !x1...xn y. A /\ ... y = construct1 x1...xn ... /\ B ==> C'
   * ...
   * '|- !x1...xn y. A /\ ... y = constructm x1...xn ... /\ B ==> C'
   * ==>
   * '|- !X. A /\ ... /\ B ==> C',
   *
   * where the datatype constructi x1...xn have m forms, and X are x1...xn
   * without those variables only occurring in the constructors.
   *)
  val MERGE_IMP_EQ_CASES_RULE : Thm.thm list -> Thm.thm;





  (* (record with fi := e).fj)
   * ---------------------------
   * if fi ≠ fj then 'vj' else e
   *)
  val RECORD_TAC : Term.term list * Term.term -> Abbrev.goal list * Abbrev.validation;

  (*    A u {recordl = recordr} ?- t
   * ----------------------------------, where fi has the name given by the first argument.
   * A u {recordl.fi = recordr.fi} ?- t
   *)
  val ADD_RECORD_ACCESSOR_ASM_TAC : string -> Abbrev.tactic;

  (* 'function_name a1...an'
   * ==>
   * 'function_body[a1/p1...an/pn]'
   *)
  val UNFOLD_FUN_TAC : string -> Term.term list * Term.term -> Abbrev.goal list * Abbrev.validation;

  (* 'function_name a1...an'
   * ==>
   * 'function_namefunction_name (cons x1m...x1m)...(cons xn1...xnp)'
   *)
  val UNFOLD_ARGS_TAC : string -> Term.term list * Term.term -> Abbrev.goal list * Abbrev.validation;

  (* 'function_name a1...an'
   * ==>
   * 'function_body[cons x1m...x1m, ..., cons xn1...xnp/a1...an]'
   *)
  val UNFOLD_FUN_ARGS_TAC : string -> Term.term list * Term.term -> Abbrev.goal list * Abbrev.validation;

  (*         A ?- t
   * ---------------------Where term whose string is equal to term_name is expanded according to its nchotomy theorem.
   * A1 ?- t1 ... An ?- tn
   *)
  val EXPAND_TERM_TAC : string -> Abbrev.tactic;

  (* A u {(l1, ..., ln) = (r1, ..., rn)} ?- t
   * ----------------------------------------
   *     A u {l1 = r1, ..., ln = rn} ?- t
   *)
  val EQ_PAIR_ASM_TAC : Term.term list * Term.term -> Abbrev.goal list * Abbrev.validation;

  (* A ?- (l1, ..., ln) = (r1, ..., rn)
   * ----------------------------------
   *   A ?- l1 = r1 /\ ... /\ ln = rn
   *)
  val EQ_PAIR_TAC : Abbrev.tactic;

  (* 'A u {lhs1 = rhs1, lhs2 = rhs2} |- t'
   * ==>
   * 'A u {lhs1 = rhs2} |- t'
   *)
  val EQ_TRANS_ASM_TAC : Abbrev.tactic;

  (* A u {l = r} ?- t
   * ----------------
   * A u {r = l} ?- t
   *)
  val REFL_ASM_EQ_TAC : Abbrev.tactic;

  (* 'A u {lhs1 = rhs1, lhs2 = rhs2} |- t'
   * ==>
   * 'A u {lhs1 = rhs2} |- t'
   *)
  val REFL_ASM_IN_GOAL_TAC : Abbrev.tactic;

  (* '{l1 = r1', ... ln = rn'} u A ?- t'
   * ==>
   * '{r1' = l1, ... rn' = ln} u A ?- t'
   *)
  val REFL_PRIMED_RHS_ASMS_TAC : Abbrev.tactic;

  (* A u {l = functiona0_ai-1 ai...an} ?- t
   * --------------------------------------string is "functiona0_ai"
   * A u {functiona0_ai-1 ai...an = l} ?- t
   *)
  val REFL_EQ_FUN_ASM_TAC : string -> Abbrev.tactic;

  (* A u {l = r} ?- t
   * ----------------substring is a substring of "l = r"
   * A u {r = l} ?- t
   *)
  val REFL_SUBSTRING_TAC : string -> Abbrev.tactic

  (* 'A u {lhs = rhs, ...lhs...} |- t'
   * ==>
   * 'A u {...rhs...} |- t'
   *)
  val ASM_EQ_RW_ASM_TAC : Abbrev.tactic;

  (* 'A u {lhs = rhs, ...lhs...} |- t'
   * ==>
   * 'A u {lhs = rhs, ...rhs...} |- t'
   *)
  val KEEP_ASM_EQ_RW_ASM_TAC : Abbrev.tactic;

  (* A u {l1=r1...ln=rn} u {...l1...ln} ?- t
   * ---------------------------------------
   *      A u {...r1...rn} ?- t[ri/li]
   *)
  val RM_ASM_EQS_RW_TAC : Abbrev.tactic;

  (* A u {lhs = rhs} u {...rhs...} ?- t
   * ----------------------------------
   * A u               {...lhs...} ?- t
   *)
  val ASM_RHS_RW_ASM_TAC : Abbrev.tactic;

  (* A u {lhs = rhs} u {...lhs..., ..., ...lhs...} ?- t
   * --------------------------------------------------
   * A u               {...rhs..., ..., ...rhs...} ?- t
   *)
  val ASM_RHS_RW_ASMS_TAC : Abbrev.tactic;

  (* '{v1=v2 ... v(n-1)=vn} u {...v1... ... ...v(n-1)...} u A ?- t'
   * ==>
   * '{...v2... ... ...vn...} u A ?- t'
   *)
  val ASM_VAR_EQ_RW_ASMS_TAC : Abbrev.tactic;

  (* A u {...L X..., ...L Y...} u {!V. L V = R V} ?- ...L Z...
   * ---------------------------------------------------------
   * A u {...R X..., ...R Y...} ?- ...R Z...
   *)
  val QLRTAC : Abbrev.tactic;

  (* A u {...R X..., ...R Y...} u {!V. L V = R V} ?- ...R Z...
   * ---------------------------------------------------------
   * A u {...L X..., ...L Y...} ?- ...L Z...
   *)
  val QRLTAC : Abbrev.tactic;

  (* A u {...L X..., ...L Y...} u {!V. L V = R V} ?- ...L Z...
   * ---------------------------------------------------------
   * A u {...R X..., ...R Y...} u {!V. L V = R V} ?- ...R Z...
   *)
  val QEQ_RW_LHS_ASM_KEEP_TAC : Abbrev.tactic;

  (* A u {...R X..., ...R Y...} u {!V. L V = R V} ?- ...R Z...
   * ---------------------------------------------------------
   * A u {...L X..., ...L Y...} u {!V. L V = R V} ?- ...L Z...
   *)
  val QEQ_RW_RHS_ASM_KEEP_TAC : Abbrev.tactic;

  (* Rewrites hypotheses with given theorem, which can contain multiple rewrite
   * theorems in a conjunction. Can remove conjuncts if rewrites contain
   * opposite boolean value.
   *)
  val RW_HYPS_TAC : Thm.thm -> Abbrev.tactic;

  (*'A u {P} u {!x1...xn. A /\ ...P... /\ B ==> C} |- t'
   * ==>
   * 'A u {A /\ ... /\ B ==> C}[v1...vn/x1...xn] |- t'
   *)
  val ASM_INST_ASM_TAC : Abbrev.tactic;

  (*'A u {P} u {!x1...xn. A /\ ...P... /\ B ==> C} |- t'
   * ==>
   * 'A u {P} u {A /\ ... /\ B ==> C}[v1...vn/x1...xn] |- t'
   *)
  val KEEP_ASM_INST_ASM_TAC : Abbrev.tactic;

  (* A u {P, !x1...xm y1...yn. A /\ ... /\ B /\ P(x1...xm) /\ C /\ ... /\ D ==> E} ?- t
   * ----------------------------------------------------------------------------------
   * A u {P, !y1...yn.         A /\ ... /\ B /\               C /\ ... /\ D ==> E} ? -t
   *
   * An implication is simplified by removing one conjunct from the antecedent
   * that occur among the assumptions.
   *)
  val ASM_INST_IMP_ASM_ONCE_TAC : Abbrev.tactic;

  (* A u {Ai, ..., Aj, !x1...xm y1...yn. A /\ ... /\ Ai /\ ... /\ C /\ ... /\ Aj /\ ... /\ D ==> E} ?- t
   * ---------------------------------------------------------------------------------------------------
   * A u {Ai, ..., Aj, !        y1...yn. A /\ ... /\ ...       /\ C /\ ... /\           /\ D ==> E} ? -t
   *
   * An implication is simplified as much as possible by removing conjuncts from
   * the antecedent that occur among the assumptions.
   *)
  val ASM_INST_IMP_ASM_TAC : Abbrev.tactic;

  (* A u {P, !X . Q X  , !Y . ... /\ P Y   /\ ... /\ Q Y   /\ ... ==> R Y  } ?- t
   * ----------------------------------------------------------------------------
   * A u {P, !X'. Q VX', !Y'. ... /\ P VY' /\ ... /\ Q VY' /\ ... ==> R VY'} ?- t
   *
   * That is, assumptions, quantified or not, are used to simplify implications,
   * quantified or not.
   *)
  val ASMS_SIMP_QIMP_TAC : Abbrev.tactic;

  (* A u {l1 = r1, ..., ln = rn, Ai r1...ln, !X Y. A1 X Y /\ ... /\ Ai Y l1...rn /\ ... /\ Am X Y ==> A X Y} ?- t
   * ------------------------------------------------------------------------------------------------------------
   * A u {l1 = r1, ..., ln = rn, Ai r1...ln, !X Y. A1 X Y /\              ...           /\ Am X Y ==> A X Y} ?- t
   *
   * That is, Ai r1...ln is used to simplify a universally quantified
   * implication by removing one conjunct in the antecedent, causing a part of
   * the universally quantified implication to be instantiated.
   *)
  val ASM_EQ_INST_ASM_IMP_ONCE_TAC : Abbrev.tactic;

  (* A u {l1 = r1, ..., ln = rn, Ai r1...ln, !X Y. A1 X Y /\ ... /\ Ai Y l1...rn /\ ... /\ Am X Y ==> A X Y} ?- t
   * ------------------------------------------------------------------------------------------------------------
   * A u {l1 = r1, ..., ln = rn, Ai r1...ln, !X Y. A1 X Y /\              ...           /\ Am X Y ==> A X Y} ?- t
   *
   * That is, Ai r1...ln, for i in I = {a, ..., k} are used to simplify a
   * universally quantified implication by removing a conjunct in the antecedent
   * that is also instantiated among the assumptions. However, there may be
   * mismatches between the arguments of the instantiated assumption and the
   * antecedent conjunct, as long as there are equations among the assumptions
   * between these mismatches.
   *)
  val ASM_EQ_INST_ASM_IMP_TAC : Abbrev.tactic;

  (*    A ?- t
   * --------------lemma: B |- !X. C1 X /\ ... /\ Cn X ==> C X, B subset of A.
   * A u {C V} ?- t
   *
   * Where V is an instantiation of X, based on all Ci in A, and equalities
   * l = r in A enabling substitutions of hypotheses in A to discharge all Ci.
   *
   * Equalitites in lemma conjuncts (e.g. Ck: l = r or r = l does not matter, if
   * l = r or r = l is in A.
   *)
  val ITAC : Thm.thm -> Abbrev.tactic;
  val IRTAC : Thm.thm -> Abbrev.tactic;
  val FITAC : Thm.thm -> Abbrev.tactic;
  val FIRTAC : Thm.thm -> Abbrev.tactic;
  (* The following four tactics simplify only the antecedent of the lemma, not the succedent as the above four tactics also simplfy. *)
  val SAITAC : Thm.thm -> Abbrev.tactic;
  val SAIRTAC : Thm.thm -> Abbrev.tactic;
  val SAFITAC : Thm.thm -> Abbrev.tactic;
  val SAFIRTAC : Thm.thm -> Abbrev.tactic;

  (* A u {!X. C1 /\.../\ Cn ==> C} ?- t
   * ----------------------------------
   *         A u {C} ?- t
   *
   * If Ci are in A or can be derived to be in A by means of equations in A.
   *)
  val AITAC : Abbrev.tactic;
  val AIRTAC : Abbrev.tactic;
  val FAITAC : Abbrev.tactic;
  val FAIRTAC : Abbrev.tactic;

  (* A u {!x1...xn. ... /\ xi = si /\ ... ==> s} ?- t
   * ----------------------------------------------
   * A u {!x1...xn. ... @ ... ==> s} ?- t
   *
   * Instantiates xi to si and removes the corresponding conjunct being part of
   * an implication which may contain other connectives.
   *)
  val SIMP_QIMP_ASM_TAC : Abbrev.tactic;

  (* 'let x = e in body'
   * ==>
   * '(\f x. f x) (\x. body) e'
   *)
  val ONCE_LETS_TAC : Term.term list * Term.term -> Abbrev.goal list * Abbrev.validation;
  val ONCE_LETS_ASM_TAC : Abbrev.tactic;
  val BSIM_ONCE_LETS_TAC : Abbrev.tactic;
  val LETS_TAC : Term.term list * Term.term -> Abbrev.goal list * Abbrev.validation;

  (* 'case p x1..xn of ...| pi -> funi x1...xn | ... '
   * ==>
   * 'funi x1...xn' if p matches pi.
   *)
  val CASE_PATTERN_TAC : Term.term list * Term.term -> Abbrev.goal list * Abbrev.validation;

  (* 'if t0 then t1 else t2'
   * ==>
   * 't1' or 't2', depending on whether 't0' or '¬t0' is an assumption.
   *)
  val COND_TAC : Term.term list * Term.term -> Abbrev.goal list * Abbrev.validation;

  (* 'if t0 then t1 else t2'
   * -----------------------
   *     't1' or 't2'
   *
   *  depending on whether t0 or ¬t0 is an assumption or t0 is of the form x = x.
   *)
  val CONDS_TAC : Term.term list * Term.term -> Abbrev.goal list * Abbrev.validation;

  (* 'if t0 then t1 else t2'
   * ==>
   * 't1' and 't2'.
   *)
  val IF_SPLIT_TAC : Abbrev.tactic;

  (*                                  A ?- t
   * -------------------------------------------------------------------
   * A[r_name/l_name] ?- t[r_name/l_name]    A u {l_name <> r_name} ?- t
   *)
  val CASE_EQ_TAC : string -> string -> Abbrev.tactic;

  (* '(c1, ..., cn) = (v1, ..., vm)'
   * ==>
   * '(c1, ..., cn) = (v1, ..., vm, ..., vn)', including let expressions.
   *)
  val UNFOLD_TUPLE_VARS_TAC : Abbrev.tactic;

  (*              'A u B ?- t'
   * -------------------------------------
   * 'A u C1 ?- s1' + ... + 'A u Cm ?- sm'
   *
   * where B = {... (case x of p1 => t1 | ... | pn => tn) ...} or
   * t = '... (case x of p1 => t1 | ... | pn => tn) ...' and
   * Ci = {...ti...} or si = '...ti...'
   *)
  val SPLIT_SCALAR_CASE_KEEP_EQ_TAC : Abbrev.tactic;	(* Does not rewrite assumptions with case pattern. *)

  val SPLIT_SCALAR_CASE_TAC : Abbrev.tactic;

  val SPLIT_VECTOR_CASE_TAC : Abbrev.tactic;

  val CASE_VECTOR_TAC : Abbrev.tactic;

  (* A u {B \/ ... \/ F \/ ... \/ C} ?- t
   * ------------------------------------
   *      A u {B \/ ... \/ C} ?- t
   *)
  val REMOVE_F_DISJUNCTS_TAC : Abbrev.tactic;

  (*        A ?- t
   * ---------------------
   * A1 ?- t1 ... An ?- tn
   *
   * Ai ?- ti corresponds to every "execution path" of the function with the
   * name given by the first argument.
   *)
  val FUN_PATHS_TAC : string -> Abbrev.tactic;

  val PTAC : Thm.thm -> Abbrev.tactic;

  (* A u {l1 = r1, l2 = r2} ?- t
   * ---------------------------
   *            -
   *
   * Solves goal if l1 = l2, l1 = r2, r1 = l2, or r1 = r2, and
   * lemma states r1 <> r2, r2 <> r1, or ...
   *)
  val CONTR_EQ_ASMS_TAC : Thm.thm -> Abbrev.tactic;

  (* A u {...substring...} ?- t
   * --------------------------
   *          A ?- t
   *)
  val REMOVE_SUBSTRING_ASMS_TAC : string -> Abbrev.tactic;

  (* A u {...substring1..., ..., ...substringn...} ?- t
   * --------------------------------------------------
   *                      A ?- t
   *)
  val REMOVE_SUBSTRINGS_ASMS_TAC : string list -> Abbrev.tactic;

  (* A u {P, ~P} ?- t
   * ----------------
   *       -
   *)
  val CONTR_ASMS_TAC : Abbrev.tactic;

  (* A u {P} ?- t
   * ------------P = ~P' or ~P = P'.
   *     -
   *
   * lemma: B |- !x1...xn. P'[x1...xn], B is a subset of A.
   *)
  val HYP_CONTR_NEQ_LEMMA_TAC : Thm.thm -> Abbrev.tactic;

  (* A u {t(X), eq1, ..., eqn} ?- t(Y)
   * ---------------------------------
   *                   -
   *
   * If there exists eqi in A such that t[eqi/X] = t(Y), and eqi = 'xi = yi' or
   * eqi = 'yi = xi'.
   *)
  val ASMS_IMP_CON_TAC : Abbrev.tactic;

  (* Attempts to solve a goal by rewriting assumptions and then derive the
   * conclusion from the rewritten assumptions.
   *)
  val STAC : Abbrev.tactic;

  (* A u {!X. ~P X} ?- t
   * -------------------B |- !Y. P Y, where B is a subset of A.
   *         -
   *)
  val CONTR_NEG_ASM_TAC : Thm.thm -> Abbrev.tactic;

  (*                    A ?- t
   * ---------------------------------------------
   * A u {case_term} ?- t    A u {~case_term} ?- t
   *)
  val NEW_CASE_TAC : Term.term -> Abbrev.tactic;

  (*                 A ?- t
   * ----------------------------------------
   * A u {r', s1'} ?-t    A u {~r', s2'} ?- t
   *
   * lemma1: |- !x1...xn. C1 /\ ... /\  r /\ ... Cm ==> s1
   * lemma2: |- !x1...xn. D1 /\ ... /\ ~r /\ ... Dp ==> s2
   *
   * Instantiates lemma1 and lemma2 so their assumption conjuncts match the
   * assumptions in A.
   *)
  val INST_IMP_CASE_TAC : Thm.thm -> Thm.thm -> Abbrev.tactic;

  (*     A ?- !x. ...x...
   * ------------------------
   * A ?- !x. (\x. ...x...) x
   *)
  val ABS_APP_TAC : Abbrev.tactic;

  (*         A ?- t
   * ---------------------- LTAC B |- !X. C1 X /\ ... /\ Cn X ==> C X,
   * A u {!X'. C I X'} ?- t
   *
   * If possible to derive Ci I X' from A by means of (potentially quantified)
   * predicates and equations in A, and B a subset of A, where I is necessary
   * instantiations of variables in X to derive Ci I X' from A.
   *
   * Otherwise an exception is generated.
   *)
  val LTAC : Thm.thm -> Abbrev.tactic;
end
