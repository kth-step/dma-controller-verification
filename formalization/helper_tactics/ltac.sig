signature ltac =
sig

  val same_type : Type.hol_type -> Type.hol_type -> bool;

  val not_same_type : Type.hol_type -> Type.hol_type -> bool;

  (* If the quantified implication is of the form
   * {..., A x1...x...xn, ...} |- !x X. P x X (the quantified variable is free
   * among the assumptions, then it needs to be renamed to avoid name clashing
   * when removing the quantified variables, which is what this function does.
   *)
  val uniquify_qimp_qvs : string list -> Thm.thm -> Thm.thm * (Term.term list);

  val union_lists : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list;

  val rename_tevs : string list -> Term.term list -> (Term.term list * string list);

  datatype bvar_match_type = FAIL | MATCH | FREE;

  val bvar_match : Term.term -> Term.term -> (Term.term * Term.term) list -> bvar_match_type;

  val find_tyvs : Term.term list -> Type.hol_type list;

  (* Given two terms term1 and term2, with instantiable term and type variables
   * in itevs (unioned from two disjoint sets, meaning that instantiable term
   * variables in term 1 and instantiable term variables in term 2 must be
   * disjoint) and ityvs (bvars denotes a stack with paired bounded variables
   * that must match each other, which is initially empty), returns:
   * -SOME (SOME tei, tyis): If it was found that to make @term1 and @term2
   *  equal, the term instantiation tei and type instantiations tyis (which may
   *  be empty) must be applied, where tyis must be applied on both the
   *  instantiated variable and the instantiated value of tei.
   * -SOME (NONE, tyi::tyis): If it was found that to make @term1 and @term2
   *  equal, some type instantiations tyi::tyis must be applied. 
   * -SOME (NONE, []): If @term1 and @term2 are equal except for uninstantiated
   *  instantiable variables.
   * -NONE: If it is impossible to make @term1 and @term2 equal by instantiating
   *  term and type variables in @itevs and @ityvs.
   *)
  val find_term_instantiation :
    Term.term ->                    (* Term 1 @term1 to be made equal to *)
    Term.term ->                    (* term 2 @term2. *)
    Term.term list ->               (* Instantiable term variables @itevs in term 1 and term 2. *)
    Type.hol_type list ->           (* Instantiable type variables @ityvs in term 1 and term 2. *)
    (Term.term * Term.term) list -> (* Bounded variables that occur in term 1 and term2 that must occur at corresponding positions. *)
    (({redex : Term.term, residue : Term.term} option) * Type.hol_type * Type.hol_type * ({redex : Type.hol_type, residue : Type.hol_type}  list)) option;

  (* Given two terms with their instantiable type and term variables, if
   * possible finds type and term variable instantiations that make the terms
   * equal including their types.
   *)
  val find_equality_instantiations : string list -> string list -> Term.term -> Term.term -> Term.term list -> Term.term list -> Type.hol_type list -> Type.hol_type list ->
                                    ({redex : Type.hol_type, residue : Type.hol_type} list *
                                     {redex : Type.hol_type, residue : Type.hol_type} list *
                                     {redex : Term.term, residue : Term.term} list *
                                     {redex : Term.term, residue : Term.term} list *
                                     Type.hol_type list *
                                     Term.term list) option;

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
