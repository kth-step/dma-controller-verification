structure ltac :> ltac =
struct

  open HolKernel Parse boolLib bossLib;

(*
################################################################################
#Algorithm depth-first search left##############################################
################################################################################

0. Let (t1, ivs1) and (t2, ivs2) be input, where ivs1 and ivs2 are
   instantiable variables of t1 and t2 that can be instantiated to make t1 and
   t2 equal.

1. Rename instantiable variables in t1 and t2 so that no instantiable	//Instantiations may contain instantiable variables 
   variable in t1 has a common name with an instantiable variable in t2, and	//of the other term.
   such that no new variable becomes captured.

   This transforms the inputs (t1, ivs1) and (t2, ivs2) to (n1, nivs1) and
   (n2, nivs2) with a mappings from nivs1 to ivs1 and from nivs2 to ivs1.

2. Is = ∅: No instantiations yet.

3. Traverse n1 and n2 in parallel and inspect their syntactic structure at the	//Termination: Finite set of instantiable variables.
   current node:
   -Structures differ: Return NONE.
   -instantiable variable (not bounded) v (in nivs1 or nivs2) occurs at a
    position matching a subterm s:
    *If v occurs in s: Return NONE (cyclic instantiation).
    *Otherwise: Perform subsitutions on existing instantiations and n1 and n2
     and add the new instantiation:
     i)   Let uivs be the uninstantiated instantiable variables currently
          occurring in s (depending on whether s occurs in n1 or n2; exist in
          nivs1 or nivs2).
     ii)  Let i = {v = v, e = s, ivs = uivs}.
     iii) Update every existing instantiation j ∈ Is:
          If i.v is an instantiable variable occurring in j.e (i.v ∈ j.ivs)
          then substitute i.e for i.v in j.e and update the uninstantiated

          j.v cannot occur in i.ivs and become cyclic, since j is an already
          existing instantiation and has already instantiated n1 and n2 before v
          matched s, and therefore cannot occur in n1 or n2, and thus not in the
          new instantiation value i.e = s.
     iv)  Substitute i.e for i.v in n1 and n2.
     v)   Go to 3.
   -Otherwise all instantiations have been computed. Go to 4.

4. Collect all uninstantiation pairs:
   UIs = ∅
   Traverse the syntactical structure of the instantiated versions of n1 and n2
   in parallel and if corresponding nodes are instantiable variables u and v:
   -If u or v exists in vs ∈ UIs, remove vs from UIs and merge vs with u and v
    and add the result to UIs: UIs = (UIs \ {vs}) ∪ {vs ∪ {u} ∪ {v}}
   -Otherwise, add u and v to UIs: UIs = UIs ∪ {{u, v}}

5. Find representatives for all equivalence classes of uninstantiated
   instantiable variables, create substitutions for uninstantiated variables
   to the representative, and collect all uninstantiated representatives that
   are uninstantiated after the instantiation.
   Set UIRs = ∅, suivs1 = ∅, suivs2 = ∅, uivs1 = ∅, uivs2 = ∅.
   For each equivalence class ui ∈ UIs:
   -Find a representative for t1 and one for t2:
    UIRs = UIRs ∪ {(rep1, rep2, ui)}
   -Create a substitution for each old variable being mapped to a variable in ui
    to the corresponding representative: rep1 if the old variable occurs in t1
    and rep2 if the old variable occursin t2. Add these to suivs1 and suivs2
    respectively.
    *suivs1 = suivs1 ∪ {old_v |-> rep1}:
     If v ∈ ui ∧ new_to_old v = old_v, old_v ∈ ivs1.
    *suivs2 = suivs2 ∪ {old_v |-> rep2}:
     If v ∈ ui ∧ new_to_old v = old_v, old_v ∈ ivs2.
   -Collect the representatives as uninstantiated:
    *uivs1 = uivs1 ∪ {rep1}
    *uivs2 = uivs2 ∪ {rep2}

6. Form instantiations with respect to original variable names:
   is1 = ∅: Instantiations of t1.
   uis1 = ∅: No uninstantiated variable equivalence class representative yet.
   is2 = ∅: Instantiations of t2.
   uis2 = ∅: No uninstantiated variable equivalence class representative yet.

   Rename instantiations:
   for each i ∈ Is
     case (vms1 i.v, vms2 i.v) of
       (SOME old_v1, _):
         e = i.e
         for each new_v ∈ i.ivs					//For each new variable in ivs of the
           for each (rep1, rep2, vs) ∈ RUIs		//instantiation find its representative
             if new_v ∈ vs then					//and replace the new variable with the
               e = e[rep1/new_v]				//representative, if the new variable
         is1 = is1 ∪ {v = old_v1, e = e}		//ivs not needed for actual instantiation.
       (_, SOME old_v2):
         e = i.e
         for each new_v ∈ i.ivs
           for each (rep1, rep2, vs) ∈ RUIs
             if new_v ∈ vs then
               e = e[rep2/new_v]
         is2 = is2 ∪ {v = old_v1, e = e}
       (_, _): ()								//No operation: Should not happen.

7. Return										//is1 and is2 are instantiations for t1 and t2.
   SOME (suis1 ∪ is1, uivs1,					//suis1 and suis2 are instantiations/substitutions
         suis2 ∪ is2, uivs2)					//for renaming uninstantiated instantiable
												//variables in t1 and t2 that remain uninstantiated
												//after the instantiation. uis1 and uis2 contain
												//uninstantiated variable equivalence class
												//representatives remaining instantiable and
												//universally quantified. instantiable variables
												//not occurring in t1 and t2 are not included in
												//neither the instantiations nor in the uninstantiations.


  
Correctness:
-Invariant:
 a) The instantiations are a subset of the final correct instantiations.
 b) n1 and n2 can be instantiated to become identical with respect to remaining
    instantiable variables.

-Each iteration preservers the invariant:
 If instantiable variable x matches s, then x must be instantiated to a term
 whose supertree is s. Otherwise, the subtree replacing x in one term will not
 be equal to the corresponding subtree in the other term.

 Preservation of a):
 If an instantiation r of y contains the instantiable variable x, then it
 means that y shall be instantiated to r but with each occurrence of x replaced
 by s. Therefore, the instantiation of y must be updated accordingly. (It is
 also possible to imagine y pointing to subtrees of n1 and n2 that previously
 was y, and which are now extended with s, and therefore r must be updated.) By 
 replacing each ocurrence of x by s in the instantiations and adding the
 instantiation of x, the instantiations are still a subset of the final correct
 instantiations.

 Preservation of b):
 By replacing each occurrence of x by s in n1 and n2, which is necessary for n1
 and n2 to be equal, the resulting n1 and n2 can still become identical by
 instantiating remaining instantiable variables approprietaly.

-Invariant implies correctness:
 When there is no instantiable variables matching structures left in n1 and
 n2, then the instantiation is complete, and the invariant implies that the
 instantiations are correct (and that n1 and n2 are equal).

-Remaining uninstantiated variables:
 The instantiable variables not instantiated, remain uninstantiated, indicated
 by replacing them with their variable equivalence class representative, which
 takes the role of the uninstantiated instantiable (quantified) variable.

################################################################################
#End of Algorithm depth-first search left#######################################
################################################################################
*)







  (* Unions two lists without duplicates with the first argument identity
   * determining whether two elements are the same or not.
   *)
  fun union_lists id es1 [] = es1
    | union_lists id es1 (e::es2) =
      let val unioned_lists = union_lists id es1 es2 in
        if exists (id e) unioned_lists then (* No duplicates. *)
          unioned_lists
        else
          (e::unioned_lists)
      end

  (* True if and only if element is in the list, where identity indicates
   * whether two elements are the same.
   *)
  fun is_in identity elements element = exists (identity element) elements

  (* Exactly the same types.
   *)
  fun same_type type1 type2 = Type.compare (type1, type2) = EQUAL

  fun not_same_type type1 type2 = Type.compare (type1, type2) <> EQUAL

  (* Removes the first occurrence of element in the given list.
   *)
  fun remove_first_occurrence identity element [] = []
    | remove_first_occurrence identity element (e::es) =
      if identity element e then
        es
      else
        e::(remove_first_occurrence identity element es)

 (* 0. Let (t1, ivs1) and (t2, ivs2) be input, where ivs1 and ivs2 are
  *    instantiable variables of t1 and t2 that can be instantiated to make t1
  *    and t2 equal.
  *
  * 1. Rename instantiable variables in t1 and t2 such that no instantiable
  *    variable in t1 has a common name with an instantiable variable in t2,
  *    and such that no new variable becomes captured.
  *
  * NOTE: Computed instantiations may contain instantiable variables of the other term.
  *
  * This transforms the inputs (t1, ivs1) and (t2, ivs2) to (n1, nivs1) and
  * (n2, nivs2), where old_to_new1: nivs1 → ivs1, old_to_new1: nivs1 → ivs1
  *)
  fun old_instantiable_type_variables_new type1 type2 ivs1 ivs2 =
    let fun rename_and_extend_map (old_v, (type_to_rename, new_to_old_vs, new_vs)) =
        let val new_v = gen_tyvar () in
          (type_subst [old_v |-> new_v] type_to_rename, (new_v, old_v)::new_to_old_vs, new_v::new_vs)
        end in
    let val (new_type1, new_to_old1, nivs1) = foldr rename_and_extend_map (type1, [], []) ivs1 in
    let val (new_type2, new_to_old2, nivs2) = foldr rename_and_extend_map (type2, [], []) ivs2 in
      (new_type1, new_type2, nivs1, nivs2, new_to_old1, new_to_old2)
    end end end

  (* Finds next instantiation by traversing type1 and type2 in parallel
   * depth-first left search.
   * -If distinct structures are encountered, NONE is returned.
   * -If an instantiation is encountered,
   *  SOME SOME (instantiatied_variable, instantiated_value) is returned.
   * -Otherwise, the types have identical structure apart from potentially
   *  matched uninstantiated variables, and SOME NONE is returned.
   *
   * NOTE: THE SAME instantiable VARIABLE MAY OCCUR IN BOTH type1 and type2.
   *
   * Each instantiation consists of the instantiated variable, the value the
   * variable is instantiated to, and the uninstantiated instantiable
   * variables occurring in the instantiation value.
   *)
  fun find_type_instantiation type1 type2 ivs =
    if is_vartype type1 orelse is_vartype type2 then                            (* At least one variable. *)
      if is_vartype type1 andalso is_vartype type2 then                         (* Both are variables. *)
        if is_in same_type ivs type1 andalso is_in same_type ivs type2 then     (* Both instantiable. *)
          SOME NONE                                                             (* No failure but no instantiation. *)
        else if is_in same_type ivs type1 then                                  (* Only type1 instantiable. *)
          SOME (SOME (type1, type2))                                            (* No failure but instantiation. *)
        else if is_in same_type ivs type2 then                                  (* Only type2 instantiable. *)
          SOME (SOME (type2, type1))                                            (* No failure but instantiation. *)
        else if same_type type1 type2 then                                      (* Neither instantiable: Must be equal. *)
          SOME NONE                                                             (* No failure but no instantiation. *)
        else                                                                    (* Neither instantiable: Not equal. *)
          NONE                                                                  (* Failure due to unequal uninstantiable variables. *)
      else if is_vartype type1 then                                             (* Only type1 is a variable. *)
        if is_in same_type ivs type1 then                                       (* Only type1 is a variable, and which is instantiable. *)
          SOME (SOME (type1, type2))                                            (* No failure and instantiation. *)
        else                                                                    (* type1 is an uninstantiable variable but type2 is not a variable. *)
          NONE                                                                  (* Failure. *)
      else                                                                      (* Only type2 is a variable. *)
        if is_in same_type ivs type2 then                                       (* Only type2 is a variable, and which is instantiable. *)
          SOME (SOME (type2, type1))                                            (* No failure and instantiation. *)
        else                                                                    (* type2 is an uninstantiable variable but type1 is not a variable. *)
          NONE                                                                  (* Failure. *)
    else                                                                        (* Both are type operators. *)
      let val {Thy = thy1, Tyop = op1, Args = args1} = dest_thy_type type1
          val {Thy = thy2, Tyop = op2, Args = args2} = dest_thy_type type2 in
      if thy1 = thy2 andalso op1 = op2 andalso length args1 = length args2 then (* Same theory guarantees same type, since same name may occur in diffirent theories. *)
        let fun find_type_instantiation_rec [] [] = SOME NONE                   (* No different structure among corresponding arguments. *)
              | find_type_instantiation_rec [] (_::_) = NONE                    (* Different number of arguments means different structure. *)
              | find_type_instantiation_rec (_::_) [] = NONE                    (* Different number of arguments means different structure. *)
              | find_type_instantiation_rec (type1::types1) (type2::types2) =
                  case find_type_instantiation type1 type2 ivs of
                    NONE => NONE                                                (* Failure due to different structural in current subtrees: Return failure. *)
                  | SOME NONE => find_type_instantiation_rec types1 types2      (* No instantiation found in current subtree: Check next. *)
                  | SOME (SOME (instantiated_variable, instantiation_value)) => (* An instantiation found: Return it. *)
                    SOME (SOME (instantiated_variable, instantiation_value)) in
          find_type_instantiation_rec args1 args2                               (* Check if there is any instantiation in arguments. *)
        end
      else                                                                      (* Failure due to distinct type operators. *)
        NONE
     end

  (* The instantiation value and uninstantiated variables in each instantiation
   * is updated with respect to the given instantiation.
   *)
  fun update_instantiations instantiate _            _         [                     ] = []
    | update_instantiations instantiate new_variable new_value ({redex = variable, residue = value}::is) =
      let val updated_instantiations = update_instantiations instantiate new_variable new_value is in
      let val updated_value = instantiate [new_variable |-> new_value] value in (* Substitute new value for new variable in existing instantiation. *)
        {redex = variable, residue = updated_value}::updated_instantiations
      end end

  (* 2 and 3. Traverse n1 and n2 in parallel and inspect their syntactic
   * structure at the current node:
   * -Structures differ: Return NONE.
   * -instantiable variable (not bounded) v (in nivs1 or nivs2) occurs at a
   *  position matching a subterm s:
   *  *If v occurs in s: Return NONE (cyclic instantiation).
   *  *Otherwise: Perform subsitutions on existing instantiations and n1 and n2
   *   and add the new instantiation:
   *   i)   Let uivs be the uninstantiated instantiable variables currently
   *        occurring in s (depending on whether s occurs in n1 or n2; exist in
   *        nivs1 or nivs2).
   *   ii)  Let i = {v = v, e = s, ivs = uivs}.
   *   iii) Update every existing instantiation j ∈ Is:
   *        If i.v is an instantiable variable occurring in j.e (i.v ∈ j.ivs)
   *        then substitute i.e for i.v in j.e and update the uninstantiated
   *        instantiable variables of j: j.ivs = j.ivs \ {i.v} ∪ i.ivs.
   *
   *        j.v cannot occur in i.ivs and become cyclic, since j is an already
   *        existing instantiation and has already instantiated n1 and n2 before
   *        v matched s, and therefore cannot occur in n1 or n2, and thus not in
   *        the new instantiation value i.e = s.
   *   iv)  Substitute i.e for i.v in n1 and n2.
   *   v)   Go to 3.
   * -Otherwise all instantiations have been computed. Go to 4.
   *
   * NOTE: ivs is instantiable variables in both type1 and type2.
   *)
  fun find_type_instantiations type1 type2 ivs =
    let fun find_instantiations_rec is type1 type2 ivs =
      case find_type_instantiation type1 type2 ivs of
        NONE => NONE                                                              (* Failure due to different structures. *)
      | SOME NONE => SOME (type1, type2, is)                                      (* No additional instantiations: Returns partially instantiated types, with only uninstantiated variables left in each type, and all accumulated instantiations.*)
      | SOME (SOME (variable, value)) =>                                          (* New instantiation. *)
        let val type_variables = type_vars value in                               (* type_vars returns no duplicate elements. *)
          if is_in same_type type_variables variable then                         (* Cyclic instantiation: Failure. *)
            NONE
          else
            let val updated_is = update_instantiations type_subst variable value is (* Updates current instantiations. *)
                val new_i = {redex = variable, residue = value}                   (* New instantiation. *)
                val new_type1 = type_subst [variable |-> value] type1             (* Apply new instantiation on the types. *)
                val new_type2 = type_subst [variable |-> value] type2 in
              find_instantiations_rec (new_i::updated_is) new_type1 new_type2 ivs (* Check for more instantiations. *)
            end
        end in
      find_instantiations_rec [] type1 type2 ivs
    end

  (* Returns a list of all members of equivalence classes having a member in
   * common with vs1, and one list with the given list without those classes.
   * vs1 are not inserted in any list, but may be included in any list.
   *)
  fun collect_merge_remove_uis identity _   _   []                              = (([], [], [], []), [])
    | collect_merge_remove_uis identity vs1 vs2 ((if11, if12, if21, if22)::uis) =
      let val ((mif11, mif12, mif21, mif22), uis_without_merges) = collect_merge_remove_uis identity vs1 vs2 uis in
        if exists (fn v1 => exists (identity v1) (if11 @ if21)) vs1 orelse
           exists (fn v2 => exists (identity v2) (if12 @ if22)) vs2 then
          (* Append does not cause duplicates since the members of uis do not
           * overlap.
           *)
          ((if11 @ mif11, if12 @ mif12, if21 @ mif21, if22 @ mif22), uis_without_merges)
        else
          (* (if11, if12, if21, if22) has no member in common with (vs1, vs2),
           * and are therefore not included in the merge.
           *)
          ((mif11, mif12, mif21, mif22), (if11, if12, if21, if22)::uis_without_merges)
      end

  (* Merges two lists of variable equivalence classes.
   *)
  fun merge_uninstantiations identity uis1 [] = uis1
    | merge_uninstantiations identity uis1 ((if11, if12, if21, if22)::uis2) =
      let val merged_uis = merge_uninstantiations identity uis1 uis2 in
      let val ((mif11, mif12, mif21, mif22), unmerged) = collect_merge_remove_uis identity (if11 @ if21) (if12 @ if22) merged_uis in
      let val if11m = union_lists identity if11 mif11
          val if12m = union_lists identity if12 mif12
          val if21m = union_lists identity if21 mif21
          val if22m = union_lists identity if22 mif22 in
        (if11m, if12m, if21m, if22m)::unmerged
      end end end

  (* Given a new variable and a mapping from new to old variables, returns true
   * if and only if the new variable is mapped.
   *)
  fun is_new_v_mapped _ [] = false
    | is_new_v_mapped new_variable ((new_v, old_v)::new_old_vs) =
      if same_type new_variable new_v then
        true
      else
        is_new_v_mapped new_variable new_old_vs

  (* 4. Collects all uninstantiation equivalence classes in the form of lists of
   *    lists, where each member list is an equivalence class, including
   *    singelton classes.
   *
   * Input are the instantiated types, and are traversed in parallel. Since the
   * inputs are instantiated to be equal, except not necessarily for
   * uninstantiated pairs (a variable being instantiated to a subterm results in
   * two subterms being equal, including uninstantiated variables in the
   * subterm), only occurring uninstantiated variables remain, which this
   * procedure finds.
   *
   * Each returned equivalance class is represented as a quadruple
   * (in1_from1, in1_from2, in2_from1, in2_from2):
   * -in1_from1: Variables occurring in type1 and originating from type1.
   * -in1_from2: Variables occurring in type1 and originating from type2. 
   * -in2_from1: Variables occurring in type2 and originating from type1. 
   * -in2_from2: Variables occurring in type2 and originating from type2.
   *)
  fun find_type_uivs_classes new_to_old1 new_to_old2 itype1 itype2 ivs =
    if is_vartype itype1 orelse is_vartype itype2 then
      if is_vartype itype1 andalso is_in same_type ivs itype1 andalso
         is_vartype itype2 andalso is_in same_type ivs itype2 then        (* Uninstantiation pair.                    *)
        case (is_new_v_mapped itype1 new_to_old1, is_new_v_mapped itype2 new_to_old2) of
          (false, false) => [([      ], [itype1], [itype2], [      ])]
        | (false, true ) => [([      ], [itype1], [      ], [itype2])]
        | (true , false) => [([itype1], [      ], [itype2], [      ])]
        | (true , true ) => [([itype1], [      ], [      ], [itype2])]
      else if is_vartype itype1 andalso is_in same_type ivs itype1 then   (* Only itype1 is uninstantiated.           *)
        raise (mk_HOL_ERR "ltac" "find_type_uivs_classes" "Uninstantiated type1 variable corresponding to uninstantiable variable after instantiation.")
      else if is_vartype itype2 andalso is_in same_type ivs itype2 then   (* Only itype2 is uninstantiated.           *)
        raise (mk_HOL_ERR "ltac" "find_type_uivs_classes" "Uninstantiated type2 variable corresponding to uninstantiable variable after instantiation.")
      else
        []                                                                (* Not uninstantiation pair.                *)
    else                                                                  (* Both are type operators.                 *)
      let val args1 = (#2 o dest_type) itype1
          val args2 = (#2 o dest_type) itype2 in
      let fun find_uninstantiations_rec [] [] = []
            | find_uninstantiations_rec [] (_::_) = raise (mk_HOL_ERR "ltac" "find_type_uivs_classes" "Matching type operators with different number of type arguments.")
            | find_uninstantiations_rec (_::_) [] = raise (mk_HOL_ERR "ltac" "find_type_uivs_classes" "Matching type operators with different number of type arguments.")
            | find_uninstantiations_rec (itype1::itypes1) (itype2::itypes2) =
              let val uninstantiations = find_type_uivs_classes new_to_old1 new_to_old2 itype1 itype2 ivs
                  val uninstantiations_rec = find_uninstantiations_rec itypes1 itypes2 in
                merge_uninstantiations same_type uninstantiations uninstantiations_rec
              end
      in
        find_uninstantiations_rec args1 args2
      end end

  (* Inputs:
   * -instantiable variables of the type for which a representative shall be
   *  generated.
   * -A representative of the other type which is the preferred name for the
   *  generated representative of this name. The representative must be renamed
   *  if one of the instantiable variables of this type has the same name.
   *
   * Output: A primed version of the given old representative until the name of
   * it does not occur among the instantiable old variables.
   *)
  fun generate_type_representative invalid_rs preferred_r =
    let val invalid_rs_string = map (hd o tl o String.explode o dest_vartype) invalid_rs
        val preferred_r_string = (hd o tl o String.explode o dest_vartype) preferred_r in
    let fun generate_old_r_string r =
      if exists (fn iv => r = iv) invalid_rs_string then
        generate_old_r_string (Char.succ r)
      else
        let val new_r = (mk_vartype o String.implode) [#"'", r] in (new_r, new_r::invalid_rs) end in
      generate_old_r_string preferred_r_string
    end end

  (* All old uninstantiated variables in a type being members of the same
   * equivalence class shall be replaced by the representative for that type of
   * that class. This is redundant for singleton equivalence classes with respect
   * to that type (the two lists contain exactly one element).
   *)
  fun generate_old_to_r_ui_class old_r [] new_member = raise (mk_HOL_ERR "ltac" "generate_old_to_r_ui" "old variable unmapped.")
    | generate_old_to_r_ui_class old_r ((new_v, old_v)::new_old_vs) new_member =
      if same_type new_member new_v then
        {redex = old_v, residue = old_r}
      else
        generate_old_to_r_ui_class old_r new_old_vs new_member

  (* Inputs:
   * -invalid_rs1: Invalid representatives for type1.
   * -invalid_rs2: Invalid representatives for type2.
   * -new_to_old1: Given a new variable originating from type1, returns the old
   *  variable corresponding to the new variable.
   * -new_to_old2: Given a new variable originating from type1, returns the old
   *  variable corresponding to the new variable.
   * -(if11, if12, if21, if22): An equivalence class with new type variables.
   *
   * Outputs an equivalence class:
   * (r1, invalid_rs1, iuis1, r2, invalid_rs2, iuis2).
   * -r1: Old representative type variable to be substitutited for all members
   *  appearing in type1.
   * -invalid_rs1: Invalid representatives for type1, including the returned r1.
   * -iuis1: Substitutions of old variables to old representatives for type1 (it
   *  may occur that two old variables become members of the same equivalence
   *  class, and at least one of them must be replaced by the representative).
   * -r2: Old representative type variable to be substitutited for all members
   *  appearing in type2.
   * -invalid_rs2: Invalid representatives for type1, including the returned r1.
   * -iuis2: Substitutions of old variables to old representatives for type2.
   * 
   *
   * Consider one of the types having been instantiated.
   * Then some variables will remain, which are uninstantiated.
   * Some variable originate from this type, while others originate from the
   * other type.
   * -If a variable originates from this type: Then that variable must be
   *  instantiated to the same value as all other variables in the same
   *  equivalence class. Therefore, all variables originating from and occurring
   *  in this type shall be replaced by the old representative for this type of
   *  this class.
   * -If a variable originates from the other type: Then that variable was
   *  transferred from the other type to this type due to an instantiation, and
   *  will therefore appear after instantiation, since uninstantiated variables
   *  occurr in the instantiations but renamed with their representatives.
   *
   * Therefore, to get a correct instantiation, the uninstantiated new variables
   * occurring in an instantiated type and originating from that type, must be
   * replaced by the old variable representative of which the uninstantiated new
   * variable is a member of.
   *)
  (* (in1_from1, in1_from2, in2_from1, in2_from2) *)
  fun find_representative invalid_rs1 invalid_rs2 new_to_old1 new_to_old2 (if11, if12, if21, if22) =
    let fun new_to_old new_v [] = raise (mk_HOL_ERR "ltac" "find_representative" "New representative unmapped.")
          | new_to_old new_v ((new, old)::new_to_old_maps) = if same_type new_v new then old else new_to_old new_v new_to_old_maps in
    let val vs1 = if11 @ if21                                                   (* New variables in the equivalence class originating from type1. *)
        val vs2 = if12 @ if22 in                                                (* New variables in the equivalence class originating from type2. *)
      if           List.null vs1  andalso not (List.null vs2) then              (* Generate representative for type1, use member for type2.     *)
        let val r2 = new_to_old (hd vs2) new_to_old2 in                         (* Old representative for type2. *)
        let val (r1, invalid_rs1) = generate_type_representative invalid_rs1 r2 in (* Old representative for type1. *)
        let val iuis1 = map (generate_old_to_r_ui_class r1 new_to_old1) if11    (* Substitutions for replacing old variables with old representative from type1. *)
            val iuis2 = map (generate_old_to_r_ui_class r2 new_to_old2) if22 in (* Substitutions for replacing old variables with old representative from type2. *)
          (r1, invalid_rs1, iuis1, r2, invalid_rs2, iuis2)                      (* r1 cannot be used again when a representative must be generated. *)
        end end end
      else if not (List.null vs1) andalso      List.null vs2  then              (* Use member for type1, generate representative for type2. *)
        let val r1 = new_to_old (hd vs1) new_to_old1 in                         (* Old representative for type1. *)
        let val (r2, invalid_rs2) = generate_type_representative invalid_rs2 r1 in (* Old representative for type2. *)
        let val iuis1 = map (generate_old_to_r_ui_class r1 new_to_old1) if11    (* Substitutions for replacing old variables with old representative from type1. *)
            val iuis2 = map (generate_old_to_r_ui_class r2 new_to_old2) if22 in (* Substitutions for replacing old variables with old representative from type2. *)
          (r1, invalid_rs1, iuis1, r2, invalid_rs2, iuis2)                      (* r2 cannot be used again when a representative must be generated. *)
        end end end
      else if not (List.null vs1) andalso not (List.null vs2) then              (* Use member for type1, use member for type2.  *)
        let val r1 = new_to_old (hd vs1) new_to_old1
            val r2 = new_to_old (hd vs2) new_to_old2 in
        let val iuis1 = map (generate_old_to_r_ui_class r1 new_to_old1) if11    (* Substitutions for replacing old variables with old representative from type1. *)
            val iuis2 = map (generate_old_to_r_ui_class r2 new_to_old2) if22 in (* Substitutions for replacing old variables with old representative from type2. *)
          (r1, invalid_rs1, iuis1, r2, invalid_rs2, iuis2)
        end end
      else
        raise (mk_HOL_ERR "ltac" "find_representative" "Empty variable equivalence class.")
    end end

  (* 5. Find representatives for all equivalence classes of uninstantiated
   *    instantiable variables, create substitutions for uninstantiated
   *    variables to the representative, and collect all uninstantiated
   *    representatives that are uninstantiated after the instantiation.
   *
   * Given a list of variable equivalence classes (list of list, where each
   * member list is a variable equivalance class of new variables, each of which
   * originates from type1 or type2), returns a list of the classes, but with
   * two old variable name representatives: one for type1 and one for type2.
   *
   * Reasoning:
   * All variables in an equivalence class are uninstantiated and shall have the
   * same value, meaning they can be merged to the same universally quantified
   * variable.
   *
   * Choose two representatives for each class, one for type1 and one for type2.
   *
   * When remapping from new to old variables, two different old variables in
   * two different equivalence classes will not be mapped to the same
   * representative (due to the same old variable occuring both in type1 and
   * type2), and unintentially be forced to be instantiated to the same value.
   *
   * If a new variable occurs in an instantiation, then the new variable should
   * be mapped to the corresponding representative. This causes all variables
   * occurring in the same instantiation (for type1 or type2) in the same
   * equivalence class to be mapped to the same old variable.
   *)
  fun generate_old_representatives_new_classes invalid_rs1 invalid_rs2 new_to_old1 new_to_old2 []        = ([], [], [], [], [])
    | generate_old_representatives_new_classes invalid_rs1 invalid_rs2 new_to_old1 new_to_old2 ((if11, if12, if21, if22)::new_ui_classes) =
      let val (r1, updated_invalid_rs1, iuis1, r2, updated_invalid_rs2, iuis2) =
          find_representative invalid_rs1 invalid_rs2 new_to_old1 new_to_old2 (if11, if12, if21, if22) in
      let val (r_classes, uivs1_rec, iuis1_rec, uivs2_rec, iuis2_rec) =
          generate_old_representatives_new_classes updated_invalid_rs1 updated_invalid_rs2 new_to_old1 new_to_old2 new_ui_classes in
      (* Uninstantiated instantiable representative variables occurring in the
       * instantiation of type1 and type2.
       * No duplicates can occur due to non-overlapping equivalence classes.
       *)
      let val uivs1 = if List.null (if11 @ if12) then uivs1_rec else r1::uivs1_rec
          val uivs2 = if List.null (if21 @ if22) then uivs2_rec else r2::uivs2_rec in
        (* Substitutions of uninstantiated old variables to old representatives
         * can be appended, without creating duplicates or inconsistencies,
         * since equivalence classes do not overlap.
         *)
        ((if11, if12, r1, if21, if22, r2)::r_classes, uivs1, iuis1 @ iuis1_rec, uivs2, iuis2 @ iuis2_rec)
      end end end

  (* Given a new variable and a list of old representative new equivalence
   * classes, returns the old representatives of the new variable.
   *)
  fun new_to_old_representative type1_or_type2 new_v [] = raise (mk_HOL_ERR "ltac" "new_to_old_representative" "New variable has no representative. All uninstantiated variables belong to a class (which may be a singleton class).")
    | new_to_old_representative type1_or_type2 new_v ((if11, if12, r1, if21, if22, r2)::r_uis) =
      if exists (same_type new_v) (if11 @ if12 @ if21 @ if22) then
        if type1_or_type2 then (* Representative for type1. *)
          r1
        else                   (* Representative for type2. *)
          r2
      else
        new_to_old_representative type1_or_type2 new_v r_uis

  (* Given a new variable and a mapping from new to old variables, returns true
   * if and only if the new variable is mapped.
   *)
  fun new_to_old _ [] = NONE
    | new_to_old new_variable ((new_v, old_v)::new_old_vs) =
      if same_type new_variable new_v then
        SOME old_v
      else
        new_to_old new_variable new_old_vs

  (* Renames an instantiation (instantiated variable and the uninstantiated
   * variables occurring in the instantiation value).
   *)
  fun new_instantiation_old new_to_old1 new_to_old2 old_r_new_classes new_v new_value nivs =
    let fun rename_type type1_or_type2 type_to_rename [] = type_to_rename
          | rename_type type1_or_type2 type_to_rename (tyv::tyvs) =
            if is_in same_type nivs tyv then
              let val old_v = new_to_old_representative type1_or_type2 tyv old_r_new_classes in
              let val renamed_type = type_subst [tyv |-> old_v] type_to_rename in
                rename_type type1_or_type2 renamed_type tyvs
              end end
            else
              rename_type type1_or_type2 type_to_rename tyvs
        val tyvs = type_vars new_value in
      case (new_to_old new_v new_to_old1, new_to_old new_v new_to_old2) of
        (NONE      , NONE      ) => raise (mk_HOL_ERR "ltac" "new_instantiation_old" "New instantiation variable unmapped.")
      | (NONE      , SOME old_r) => (false, old_r, rename_type false new_value tyvs) (* Renames instantiated variable and the instatiation value for type2. *)
      | (SOME old_r, NONE      ) => (true , old_r, rename_type true  new_value tyvs) (* Renames instantiated variable and the instatiation value for type1. *)
      | (SOME old1 , SOME old2 ) => raise (mk_HOL_ERR "ltac" "new_instantiation_old" "New instantiation variable double mapped.")
    end

 (* 6. Rename instantiations from new to original variable names.
  *)
  fun new_ty_instantiations_old nivs new_to_old1 new_to_old2 old_r_new_classes [] = ([], [])
    | new_ty_instantiations_old nivs new_to_old1 new_to_old2 old_r_new_classes ({redex = new_v, residue = new_value}::is) =
      let val (is1, is2) = new_ty_instantiations_old nivs new_to_old1 new_to_old2 old_r_new_classes is in
        case new_instantiation_old new_to_old1 new_to_old2 old_r_new_classes new_v new_value nivs of
          (true,  old_r1, old_value) => ({redex = old_r1, residue = old_value}::is1, is2)
        | (false, old_r2, old_value) => (is1, {redex = old_r2, residue = old_value}::is2)
      end

  (* 7. Combine previous steps and return the result.
   * 
   * Inputs:
   * -type1: A type.
   * -type2: A type.
   * -ivs1: instantiable type variables in type1.
   * -ivs2: instantiable type variables in type2.
   *
   * Outputs:
   * -SOME (is1, is2, uivs1, uivs2): If it is possible instantiate
   *  instantiable variables ivs1 and ivs2 in type1 and type2 to make
   *  type1[is1] equal to type2[is2], ignoring uninstantiated variables uivs1 in
   *  type1 and uivs2 in type2 (variables that did not need to be instantiated
   *  to make type1 and type2 equal).
   * -NONE: If it is not possible to instantiate instantiable variables ivs1
   *  and ivs2 of type1 and type2 to make type1 and type2 equal.
   *)
  fun has_type_instantiation type1 type2 ivs1 ivs2 =
    (* Renames ivs1 and ivs2 to to not overlap each other. *)
    let val (type1_new, type2_new, ivs1_new, ivs2_new, new_to_old_map1, new_to_old_map2) =
          old_instantiable_type_variables_new type1 type2 ivs1 ivs2 in
    let val ivs_new = ivs1_new @ ivs2_new in
    let val type_instantiations = find_type_instantiations type1_new type2_new ivs_new in
      if isSome type_instantiations then (* Instantiation found. *)
        let val (itype1, itype2, new_is) = valOf type_instantiations in
        (* Computes variable equivalence classes with new names. This includes singleton classes. *)
        let val uivs_classes_new = find_type_uivs_classes new_to_old_map1 new_to_old_map2 itype1 itype2 ivs_new in
        (* Uninstantiation classes with old representatives, uninstantiated
         * variables, and substitutions of old variables for new representatives.
         *)
        let val (old_r_new_classes, uis1, iuis1, uis2, iuis2) = generate_old_representatives_new_classes ivs1 ivs2 new_to_old_map1 new_to_old_map2 uivs_classes_new in
        (* Instantiations and uninstantiations with old renamed representatives. *)
        let val (is1, is2) = new_ty_instantiations_old ivs_new new_to_old_map1 new_to_old_map2 old_r_new_classes new_is in
          SOME (iuis1 @ is1, uis1, iuis2 @ is2, uis2)
        end end end end
      else
        NONE
    end end end

(* Test cases:
val type1 = “: ('a -> 'b) -> 'a”
val ivs1 = [“: 'a”, “: 'b”]
val type2 = “: 'a -> 'b”
val ivs2 = [“: 'a”, “: 'b”]
has_type_instantiation type1 type2 ivs1 ivs2


val type1 = “: ('a -> 'k) -> 'b -> ('c # (num -> bool) # 'e) -> (bool # 'g # 'h # num # 'b) option”
val type2 = “: 'i         -> 'j -> 'k                        -> (bool # 'k # num # 'h # 'm) option”
val ivs1 = [“: 'a”, “: 'k”, “: 'b”, “: 'c”, “: 'e”, “: 'g”, “: 'h”]
val ivs2 = [“: 'i”, “: 'j”, “: 'k”, “: 'h”, “: 'm”]
has_type_instantiation type1 type2 ivs1 ivs2


val type1 = “: ('a -> 'k) -> 'b -> ('c # (num -> bool) # 'e) -> (bool # 'g # 'h # num) option”
val type2 = “: 'i         -> 'j -> 'k                        -> (bool # 'k # num # 'h) option”
val ivs1 = [“: 'g”, “: 'h”, “: 'e”]
val ivs2 = [“: 'i”, “: 'j”, “: 'k”, “: 'h”]
has_type_instantiation type1 type2 ivs1 ivs2


val type1 = “: ('a -> 'b) -> 'c -> ('d # (num -> bool) # 'e) -> (bool # 'f # 'g # num # 'h) option”
val type2 = “: 'a         -> 'f -> 'c                        -> (bool # 'd # num # 'e # 'f) option”
val ivs1 = [“: 'a”, “: 'b”, “: 'c”, “: 'd”, “: 'e”, “: 'f”, “: 'g”, “: 'h”]
val ivs2 = [“: 'a”, “: 'c”, “: 'd”, “: 'e”, “: 'f”]
has_type_instantiation type1 type2 ivs1 ivs2
*)






(******************************************************************************)
(******************************************************************************)
(******************************************************************************)
(******************************************************************************)
(******************************************************************************)
(*Instantiation of terms to make terms equal.**********************************)
(******************************************************************************)
(******************************************************************************)
(******************************************************************************)
(******************************************************************************)
(******************************************************************************)

(*Algorithm*********************************************************************

Input:
-Terms to be made equal, including their types, and their instantiable type
 variables and instantiable term variables.

Output:
-Type instantiations to apply on the given terms.
-Term instantiations to apply on the given terms after they have been
 instantiated with the previous type instantiations.
-Intantiatable type and term variables of the type and term instantiated terms
 that were left uninstantiated, but which may be renamed in case some variables
 must be instantiated to the same values.

1. Old to new type variable substitutions:
   Create old to new type variable substitutions.

   Performed by old_instantiable_term_type_variables_new.

2. New instantiable type variables:
   Apply the old to new type variable substitutions (step 1) on the
   instantiable type variables.

   Performed by old_instantiable_term_type_variables_new.

3. Old to new term variable substitutions with old and new term variables having
   new type variables:
   a) Create old to new term variable substitutions, with both old and new term
      variables having old type variables.
   b) Apply the old to new type variable substitutions (step 1) on the old to
      new term variable substitutions (step 3a)), with respect to both the old
      and the new term variables which have old type variables.

   Performed by old_instantiable_term_variables_new.

4. Terms to be made equal with new type and new term variables:
   a) Apply the old to new type variable substitutions (step 1) on the given
      terms.
   b) Apply the old to new term variable substitutions with old and new term
      variables having new type variables (step 3) on the given terms with new
      type variables (step 4a)).

   Performed by old_instantiable_term_variables_new.

5. New instantiable term variables with new type variables:
   a) Apply the old to new type variable substitutions (step 1) on the
      instantiable term variables.
   b) Apply the old to new term variable substitutions with old and new term
      variables having new type variables (step 3) on the instantiable term
      variables with new type variables (step 5a)).

   Performed by old_instantiable_term_variables_new.


----Front-end done


6. a) Type and term instantiations with new type and term variables:
      Compute the term and type instantiations with new type and term variables,
      based on step 4.

      Performed by find_term_instantiations.

   b) Uninstantiated instantiable type and term variables, with terms being
      type instantiated with the computed type instantiations, based on steps 2
      and 5:
      Type instantiate uninstantiated instantiable term variables, and remove
      instantiated type and term variables from the instantiable type and term
      variable lists.

      Performed by:
      -find_term_instantiations (find uninstantiated variables)
       type instantiations).

   c) New uninstantiated instantiable type variable equivalence classes:
      Collect new uninstantiated instantiable type variable equivalence
      classes, based on step 6a).

      Performed by find_term_instantiations.

   d) The terms resulting from applying the term and type instantiations:
      Apply the computed term and type instantiations (step 6a)) on the given
      terms (step 4).

      Performed by find_term_instantiations.


----Back-end starts (with steps 8 to 15 performed by new_instantiations_old)


7. New uninstantiated instantiable term variable equivalence classes with new
   type variables:
   Traverse the instantiated terms (step 6d)) and compute term variable
   equivalence classes.

   Performed by find_tervecs.

8. New to old type substitutions:
   Find new to old substitutions for the new type variables that remain
   uninstantiated, based on the old to new type substitutions (step 1) and the
   type variable equivalence classes of which all members should have the same
   old name since they must be instantiated to the same type value (step 6c)).

9. Old type instantiations:
   Apply the new to old type substitutions (step 8) on the computed new type
   variable instantiations (step 6a)).

10.Old uninstantiated instantiable type variables:
   Apply the new to old type substitutions (step 8) on the remaining
   uninstantiated instantiable new type variables (step 6b)).

11.New to old term variable substitutions with both new and old term variables
   having NEW and INSTANTIATED type variables:
   Find new to old substitutions for the remaining uninstantiated instantiable
   new term variables with both the new and the old variables having NEW
   INSTANTIATED type variables. These substitutions are based on:
   -the old to new term substitutions with uninstantiated new type variables
    (step 2),
   -the computed type instantiations (step 6a), to remove instantiated type
    variables which is necessary to make the types of the term variables of
    these old to new substitutions equal to the:
    *term variables in the term instantiations (step 6a)),
    *remaining uninstantiated new term variables (step 6b)),
    *term variable equivalence classes (step 7),
    all of which have been type instantiated, and
   -the term variable equivalence classes of which all members should have the
    same old name since they must be instantiated to the same value (step 7).

12.Term variable instantiations with old term variables and new instantiated
   type variables:
   Apply the type instantiated new to old term substitutions (step 11) on the
   new term instantiations which are type instantiated (step 6a)).

13.Term variable instantiations with old term variables and old instantiated
   type variables:
   Apply the new to old type substitutions (step 8) on the term instantiations
   with old term variables and new instantiated type variables (step 12).

14.Old uninstantiated instantiable term variables with new instantiated type
   variables:
   Apply the type instantiated new to old term substitutions (step 11) on the
   uninstantiated instantiable new term variables which are type instantiated
   (step 6b)).

15.Old uninstantiated instantiable term variables with old instantiated type
   variables:
   Apply the new to old type substitutions (step 8) on the old uninstantiated
   instantiable term variables with new instantiated type variables (step 14).

The outputs are computed at the following steps:
   9:  Old type instantiations.
   10: Old uninstantiated instantiable type variables.
   13: Term variable instantiations with old term variables and old instantiated
       type variables.
   15: Old uninstantiated instantiable term variables with old instantiated
       type variables.
*******************************************************************************)

  fun same_term t1 t2 = Term.compare (t1, t2) = EQUAL

  fun not_same_term t1 t2 = Term.compare (t1, t2) <> EQUAL

  (* 1 and 2. Renames instantiable old type variables to new unique type
   * variables and creates old to new type substitutions.
   *)
  fun old_instantiable_term_type_variables_new otyivs1 otyivs2 =
    let fun generate_old_new [] = ([], [])
          | generate_old_new (otyiv::otyivs) =
            let val (old_new_ty, ntyivs) = generate_old_new otyivs in
            let val ntyiv = gen_tyvar () in
              ({redex = otyiv, residue = ntyiv}::old_new_ty, ntyiv::ntyivs)
            end end in
    let val (old_new_ty1, ntyivs1) = generate_old_new otyivs1
        val (old_new_ty2, ntyivs2) = generate_old_new otyivs2 in
      (old_new_ty1, ntyivs1, old_new_ty2, ntyivs2)
    end end

  (* 3,4 and 5. Renames instantiatable old term variables to new unique term
   * variables with new type variables, including old to new substitutions with
   * new type variables.
   *
   * 3. Old to new term variable substitutions with old and new term variables
   *    having new type variables:
   *    a) Create old to new term variable substitutions, with both old and new
   *       term variables having old type variables.
   *    b) Apply the old to new type variable substitutions (step 1) on the old
   *       to new term variable substitutions (step 3a)), with respect to both
   *       the old and the new term variables which have old type variables.
   *
   * 4. Terms to be made equal with new type and new term variables:
   *    a) Apply the old to new type variable substitutions (step 1) on the
   *       given terms.
   *    b) Apply the old to new term variable substitutions with old and new
   *       term variables having new type variables (step 3) on the given terms
   *       with new type variables (step 4a)).
   *
   * 5. New instantiable term variables with new type variables:
   *    a) Apply the old to new type variable substitutions (step 1) on the
   *       instantiable term variables.
   *    b) Apply the old to new term variable substitutions with old and new
   *       term variables having new type variables (step 3) on the instantiable
   *       term variables with new type variables (step 5a)).
   *)
  fun old_instantiable_term_variables_new old_new_ty1 old_new_ty2 ote1 ote2 oteivs1 oteivs2 =
    let fun rename_and_extend_map old_new_ty (old_v_old_ty, (term_to_rename_new_ty, old_new, new_v_new_tys)) =
      let val old_v_new_ty = inst old_new_ty old_v_old_ty in          (* Old term variable with new type variables. *)
      let val new_v_new_ty = (genvar o type_of) old_v_new_ty in       (* New term variable with new type variables. *)
        (subst [old_v_new_ty |-> new_v_new_ty] term_to_rename_new_ty, (* Term with new term variable.               *)
         {redex = old_v_new_ty, residue = new_v_new_ty}::old_new, (* Old to new term variable substitution with new type variables. *)
         new_v_new_ty::new_v_new_tys)                                 (* New term variable with new type variables. *)
      end end in
    let val ote_new_ty1 = inst old_new_ty1 ote1    (* Term 1 with old term variables and new type variables. *)
        val ote_new_ty2 = inst old_new_ty2 ote2 in (* Term 2 with old term variables and new type variables. *)
    let val (nte1, old_new_te1, nteivs1) = foldr (rename_and_extend_map old_new_ty1) (ote_new_ty1, [], []) oteivs1
        val (nte2, old_new_te2, nteivs2) = foldr (rename_and_extend_map old_new_ty2) (ote_new_ty2, [], []) oteivs2 in
      (nte1, nte2, nteivs1, nteivs2, old_new_te1, old_new_te2)
    end end end

  datatype bvar_match_type = FAIL | MATCH | FREE

  (* Inputs:
   * -nte1 and nte2 denoting two terms (variables if occur in bvars and bvars
   *  only contain bounded pairs of variables).
   * -bvars: Stack of bounded variables.
   *
   * Output:
   * -FAIL: nte1 or nte2 occur in bvars but do not match.
   * -MATCH: nte1 or nte2 occur and match in bvars.
   * -FREE: Neither nte1 nor nte2 occur in bvars.
   *)
  fun bvar_match nte1 nte2 [] = FREE
    | bvar_match nte1 nte2 ((bvar1, bvar2)::bvars) =
      case (same_term nte1 bvar1, same_term nte2 bvar2) of
        (false, false) => bvar_match nte1 nte2 bvars
      | (false, true ) => FAIL
      | (true , false) => FAIL
      | (true , true ) => MATCH

  fun find_term_instantiation_variable nte1 nte2 nteivs ntyivs bvars =
    case bvar_match nte1 nte2 bvars of
      FAIL => NONE                                                              (* nte1 or nte2 occur in bvars but do not match. *)
    | MATCH => (                                                                (* nte1 or nte2 occur and match in bvars. *)
      case find_type_instantiations (type_of nte1) (type_of nte2) ntyivs of
        NONE => NONE
      | SOME (ty1, ty2, tyis) => SOME (NONE, ty1, ty2, tyis))                   (* No term instantiation but potential type instantiations. *)
    | FREE =>                                                                   (* Neither nte1 nor nte2 occur in bvars. *)
      case (is_in same_term nteivs nte1, is_in same_term nteivs nte2) of
        (true, true) => (                                                       (* nte1 and nte2 are instantiable variables. *)
        case find_type_instantiations (type_of nte1) (type_of nte2) ntyivs of
          NONE => NONE
        | SOME (ty1, ty2, tyis) => SOME (NONE, ty1, ty2, tyis))                 (* No term instantiation but potential type instantiations. *)
      | (true, false) => (                                                      (* Only nte1 is an instantiable variable. *)
        if exists (fn bv => exists (fn v => same_term bv v) (free_vars nte2)) (map snd bvars) then
          (* nte2 contains free variable that is bounded by superterm. Must not
           * instantiate to subterm which contains bounded variables.
           *)
          NONE
        else
          case find_type_instantiations (type_of nte1) (type_of nte2) ntyivs of
            NONE => NONE
          | SOME (ty1, ty2, tyis) => SOME (SOME {redex = nte1, residue = nte2}, ty1, ty2, tyis))
      | (false, true) => (                                                      (* Only nte2 is an instantiable variable. *)
        if exists (fn bv => exists (fn v => same_term bv v) (free_vars nte1)) (map fst bvars) then
          NONE (* nte1 contains free variable that is bounded by superterm. *)
        else
          case find_type_instantiations (type_of nte1) (type_of nte2) ntyivs of
            NONE => NONE
          | SOME (ty1, ty2, tyis) => SOME (SOME {redex = nte2, residue = nte1}, ty1, ty2, tyis))
      | (false, false) =>                                                       (* Neither nte1 nor nte2 are instantiable variables. *)
        if is_var nte1 andalso is_var nte2 andalso
           term_to_string nte1 = term_to_string nte2 then                       (* Same variable except for types. *)
          case find_type_instantiations (type_of nte1) (type_of nte2) ntyivs of
            NONE => NONE
          | SOME (ty1, ty2, tyis) => SOME (NONE, ty1, ty2, tyis)                (* No term instantiation but potential type instantiations. *)
        else                                                                    (* At least one is a variable, none is instantiable, and not same variables: Failure. *)
          NONE

  fun find_term_instantiation_constant nte1 nte2 ntyivs =
    if is_const nte1 andalso is_const nte2 andalso 
       term_to_string nte1 = term_to_string nte2 then                           (* Same constant except for types. *)
      case find_type_instantiations (type_of nte1) (type_of nte2) ntyivs of
        NONE => NONE
      | SOME (ty1, ty2, tyis) => SOME (NONE, ty1, ty2, tyis)                    (* No term instantiation but potential type instantiations. *)
    else
      NONE

  fun find_term_instantiation_application find_term_instantiation nte1 nte2 nteivs ntyivs bvars =
    if is_comb nte1 andalso is_comb nte2 then
      let val (ntef1, ntea1) = dest_comb nte1
          val (ntef2, ntea2) = dest_comb nte2 in
        case find_term_instantiation ntea1 ntea2 nteivs ntyivs bvars of
          NONE => NONE
        | SOME (SOME tei, ty1, ty2, tyis) => SOME (SOME tei, ty1, ty2, tyis)
        | SOME (NONE, ty1, ty2, tyi::tyis) => SOME (NONE, ty1, ty2, tyi::tyis)
        | SOME (NONE, ty1, ty2, []) => find_term_instantiation ntef1 ntef2 nteivs ntyivs bvars
      end
    else
      NONE

  fun find_term_instantiation_abstraction find_term_instantiation nte1 nte2 nteivs ntyivs bvars =
    if is_abs nte1 andalso is_abs nte2 then
      let val (bvar1, body1) = dest_abs nte1
          val (bvar2, body2) = dest_abs nte2 in
        find_term_instantiation body1 body2 nteivs ntyivs ((bvar1, bvar2)::bvars)
      end
    else
      NONE

  (* Given two terms nte1 and nte2, with instantiable term and type variables
   * in nteivs and ntyivs (bvars denotes a stack with paired bounded variables
   * that must match each other, which is initially empty), returns:
   * -SOME (SOME tei, tyis): If it was found that to make nte1 and nte2 equal,
   *  the term instantiation tei and type instantiations tyis (which may be
   *  empty) must be applied, where tyis must be applied on both the
   *  instantiated variable and the instantiated value of tei.
   * -SOME (NONE, tyi::tyis): If it was found that to make nte1 and nte2 equal,
   *  some type instantiations tyi::tyis must be applied. 
   * -SOME (NONE, []): If nte1 and nte2 are equal except for uninstantiated
   *  instantiable variables.
   * -NONE: If it is impossible to make nte1 and nte2 by instantiating term and
   *  type variables in nteivs and ntyivs.
   *)
  fun find_term_instantiation nte1 nte2 nteivs ntyivs bvars =
    if is_var nte1 orelse is_var nte2 then
      find_term_instantiation_variable nte1 nte2 nteivs ntyivs bvars
    else if is_const nte1 orelse is_const nte2 then
      find_term_instantiation_constant nte1 nte2 ntyivs
    else if is_comb nte1 orelse is_comb nte2 then
      find_term_instantiation_application find_term_instantiation nte1 nte2 nteivs ntyivs bvars
    else (* Both must be abstractions. *)
      find_term_instantiation_abstraction find_term_instantiation nte1 nte2 nteivs ntyivs bvars

(*
val nte1 = ``x : 'a``
val nte2 = ``(p : 'b -> ('c # num)) (z : 'b)``
val nteivs = [``x : 'a``, ``p : 'b -> ('c # num)``, ``(z : 'b)``]
val ntyivs = [``: 'a``, ``: 'b``, ``: 'c``]
val bvars = []
*)

  (* True if and only if there exists a type instantiation where the
   * instantiated type variable occurs in its instantiation value.
   *)
  fun cyclic_tyis tyis = exists (fn {redex = from, residue = to} => exists (fn tyv => same_type from tyv) (type_vars to)) tyis

  (* True if and only if the term instantiated variable occurs in its
   * instantiation value.
   *
   * No additional type checking is needed when checking whether the
   * instantiated variable occyrs in the instantiation value:
   * 1. Initially, a variable occurs in one term only, and all occurrences of
   *    that variable has the same type.
   * 2. When the variable is copied to the other term, necessary type
   *    instantiations are created for making the types identical of the
   *    instantiated variable y and the instantiation value t(x)
   * 3. The algorithm applies these type instantiations on both terms, and then
   *    t(x) is copied to and replicing y in the other term.
   * 4. These means that all occurrences of x, irrespective of considered term,
   *    have the same type, when a matching y |-> t(x) is found.
   * 5. It is this matching y |-> t(x) that is checked whether y occurs in t(x).
   *    Hence, no special sort of type checking is necessary to know whether y
   *    occurs in t(x).
   *)
  fun cyclic_tei NONE = false
    | cyclic_tei (SOME {redex = from, residue = to}) =
      (* Free variables in to may be bound in the term to occurs in, but since
       * instantiable variables are unique this is not a problem.
       *)
      is_in same_term (free_vars to) from

  (* Given a type variable equivalence class uivec1 and a list of disjoint type
   *  variable equivalence classes uivecs2, returns two lists:
   * -One list contains type variable equivalence classes that has a common
   *  members with uivecs1.
   * -One list contains type variable equivalence classes that does not have a
   *  common members with uivecs1.
   *)
  fun collect_type_vecs_to_merge uivec1 [] = ([], [])
    | collect_type_vecs_to_merge uivec1 (uivec2::uivecs2) =
      let val (merged_vecs, other_vecs) = collect_type_vecs_to_merge uivec1 uivecs2 in
        if exists (fn v2 => exists (same_type v2) uivec1) uivec2 then (* Common member. *)
           (uivec2 @ merged_vecs, other_vecs) (* Since uivecs2 contains disjoint equivalence classes, they can be concatenated without creating duplicates. *)
        else
          (merged_vecs, uivec2::other_vecs)
      end

  (* Given two lists, both of which contains disjoint uninstantiated variable
   * equivalence classes, merges the two lists to one list of disjoint
   * uninstantiated variable equivalence classes.
   *)
  fun merge_ui_type_vecss uivecs1 [] = uivecs1
    | merge_ui_type_vecss uivecs1 (uivec2::uivecs2) =
      let val merged_ui_type_vecss = merge_ui_type_vecss uivecs1 uivecs2 in
      (* Retrieve other vecs in merged_ui_type_vecss with members in uivec2. *)
      let val (merged_vecs, other_vecs) = collect_type_vecs_to_merge uivec2 merged_ui_type_vecss in 
      let val merged_vec = union_lists same_type merged_vecs uivec2 in (* Add members of uivec2 without duplucation. *)
        merged_vec::other_vecs
      end end end

  (* Finds type variable equivalence classes.
   *
   * Used to find type variables that must be replaced by the same type variable
   * for term instantiations to succeed.
   *)
  fun find_ui_type_vecs itype1 itype2 ivs =
    if is_vartype itype1 orelse is_vartype itype2 then
      if is_vartype itype1 andalso is_in same_type ivs itype1 andalso
         is_vartype itype2 andalso is_in same_type ivs itype2 then        (* Uninstantiation pair.                    *)
        if same_type itype1 itype2 then                                   (* Avoid duplicates. *)
          [[itype1]]
        else
          [[itype1, itype2]]
      else if is_vartype itype1 andalso is_in same_type ivs itype1 then   (* Only itype1 is uninstantiated.           *)
        raise (mk_HOL_ERR "ltac" "find_ui_type_vecs" "Uninstantiated type1 should be instantiated.")
      else if is_vartype itype2 andalso is_in same_type ivs itype2 then   (* Only itype2 is uninstantiated.           *)
        raise (mk_HOL_ERR "ltac" "find_ui_type_vecs" "Uninstantiated type2 should be instantiated.")
      else
        []                                                                (* Not uninstantiation pair.                *)
    else                                                                  (* Both are type operators.                 *)
      let val args1 = (#2 o dest_type) itype1
          val args2 = (#2 o dest_type) itype2 in
      let fun find_uninstantiations_rec [] [] = []
            | find_uninstantiations_rec [] (_::_) = raise (mk_HOL_ERR "ltac" "find_ui_type_vecs" "Unequal number of type arguments.")
            | find_uninstantiations_rec (_::_) [] = raise (mk_HOL_ERR "ltac" "find_ui_type_vecs" "Unequal number of type arguments.")
            | find_uninstantiations_rec (itype1::itypes1) (itype2::itypes2) =
              let val uninstantiations = find_ui_type_vecs itype1 itype2 ivs
                  val uninstantiations_rec = find_uninstantiations_rec itypes1 itypes2 in
                merge_ui_type_vecss uninstantiations uninstantiations_rec
              end
      in
        find_uninstantiations_rec args1 args2
      end end

  (* Applies the second list of instantiations on the first list of
   * instantiations.
   *)
  fun instantiate_instantiations instantiate instantiations_to_instantiate [] = instantiations_to_instantiate
    | instantiate_instantiations instantiate instantiations_to_instantiate ({redex = variable, residue = value}::is) =
      let val instantiated_instantiations = update_instantiations instantiate variable value instantiations_to_instantiate in
        instantiate_instantiations instantiate instantiated_instantiations is
      end

  fun same_type_i {redex = variable1, residue = value1} {redex = variable2, residue = value2} =
    if same_type variable1 variable2 then
      if same_type value1 value2 then
        true
      else
        raise (mk_HOL_ERR "ltac" "same_type_i" "Inconsistent type variable instantiations.")
    else
      false

  (* Collects all disjoint variable equivalence classes having common elements
   * with vec, by merging their representatives and members separately.
   *)
  fun split_rsvecs nvec [] = (([], []), [])
    | split_rsvecs nvec ((rs, ms)::rsvecs) =
      let val ((merged_rs, merged_ms), irrelevant_rsvecs) = split_rsvecs nvec rsvecs in
        if exists (fn r => exists (same_type r) nvec) rs then    (* Common element. Only representatives can occur in new variable equivalence classes nvec. *)
          ((rs @ merged_rs, ms @ merged_ms), irrelevant_rsvecs) (* Append does not give duplicates since rsvecs are disjoint. *)
        else
          ((merged_rs, merged_ms), (rs, ms)::irrelevant_rsvecs)
      end

  (* Merges new equivalences without representatives with previously collected
   * variable equivalence classes with representatives.
   *
   * Algoritm:
   * -Input:
   *  *rvecs: (r1, ms1), ..., (rn, msn): Previously collected variable
   *   equivalence classes with representatives and members. The variables in msi
   *   are substituted for ri in the current type instantiations. These are
   *   disjoint.
   *  *nvecs: vec1, ..., vecm: New variable equivalence classes without
   *   representatives. These are dijsoint.
   *
   * -Output:
   *  *[(rs1, m1), ..., (rsp, mp)]: Where (rsi, mi) are the union of all
   *   previously collected equivalence classes and the new equivalence classes
   *   with a common element, with rsi are the representatives and mi are the
   *   union of all members, where mi does not overlap rsi.
   *)
  fun merge_collected_and_new_vecs rvecs [] = map (fn (r, ms) => ([r], ms)) rvecs
    | merge_collected_and_new_vecs rvecs (nvec::nvecs) =
      let val rsvecs = merge_collected_and_new_vecs rvecs nvecs in (* rsvecs may have multiple representatives. *)
      let val ((relevant_rs, relevant_ms), irrelevant_rsvecs) = split_rsvecs nvec rsvecs in
        if null relevant_rs then (* No equivalence class with a member in nvec *)
          (* Non-singleton equivalence class not overlapping collected classes:
           * Create it. All variables of the new variable equivalence class has
           * the role of a representative since they occur in the terms to be
           * instantiated, in which type variables have the same role as
           * representatives.
           *)
          (nvec, [])::irrelevant_rsvecs
        else
          (* nvec contains only representatives, some of which may not occur in
           * previously collected classes. Therefore, all members of nvec must be
           * added to create correct representative instantiations.
           *)
          let val rs = union_lists same_type relevant_rs nvec in
            (rs, relevant_ms)::irrelevant_rsvecs
          end
      end end

  (* Input: Merged type variable equivalence classes of previously collected
   * classes with representatives and new classes without representatives. These
   * merged classes have multiple representatives, but which are all disjoint
   * from the members.
   *
   * Outputs:
   * -Variable equivalence classes with representatives.
   * -Instantiations from previous representatives to new representatives.
   *)
  fun find_representatives_with_is [] = ([], [])
    | find_representatives_with_is (([], ms)::rsvecs) =
      raise (mk_HOL_ERR "ltac" "find_reprensentatives_and_is"
                        "Variable equivalence class with multiple representatives, but no representative.")
    | find_representatives_with_is ((r::rs, ms)::rsvecs) =
      let val (rvecs, ris) = find_representatives_with_is rsvecs
          val rs_to_r = map (fn previous_r => {redex = previous_r, residue = r}) rs in
        ((r, rs @ ms)::rvecs, rs_to_r @ ris)
      end

  fun remove_some_tyrvec r [] = NONE
    | remove_some_tyrvec r ((rep, ms)::rvecs) =
      if same_type r rep then
        SOME rvecs
      else
        case remove_some_tyrvec r rvecs of
          NONE => NONE
        | SOME removed_tyrvec => SOME ((rep, ms)::removed_tyrvec)

  (* Since collected_tyrvecs contain disjoint classes, the representative may
   * occur in at most one class, and therefore it is sufficient to only remove
   * the first class whose representative matches the instantiated
   * representative.
   *)
  fun remove_instantiated_tyrvecs collected_tyrvecs [] = collected_tyrvecs
    | remove_instantiated_tyrvecs collected_tyrvecs ({redex = r, residue = _}::is) =
      case remove_some_tyrvec r collected_tyrvecs of
        NONE => remove_instantiated_tyrvecs collected_tyrvecs is (* r does not occur in an equivalence class. *)
      | SOME removed_collected_tyrvecs => remove_instantiated_tyrvecs removed_collected_tyrvecs is (* class of r removed. *)

  (* Inputs:
   * -Two types: itype1 and itype2, instantiated with a given new type variable
   *  instantiation tyis.
   * -A list of instantiable type variables.
   * -A list of collected type variable.
   *
   * Outputs:
   * -A new list of type instantiations whose uninstantiated variables are not
   *  among the instantiated variables, and which is composed of the given type
   *  variable instantiation and type variable equivalence classes. This type
   *  instantiation can be applied on previous type variable instantiations and
   *  the terms to be made equal, so that all type variable instantiations are
   *  consistent (no instantiation of a type variable occurs as uninstantiated
   *  in another instantiation value) and so that the terms to be made equal
   *  have consistent types (instantiation values have types that match
   *  instantiated variables).
   *
   * Algorithm:
   * 0. If a variable has been instantiated (cannot be to another instantiable
   *    variable since that is performed by step 3 below), and the instantiated
   *    variable belongs to a previously collected type variable equivalence
   *    class (must be the representative, since the members are replaced by the
   *    representative within the terms), then the members of that class are not
   *    anymore uninstantiated, and the class shall therefore be removed.
   *
   * 1. Find type variable equivalence classes with respect to the given two
   *    type instantiations itype1 and itype2.
   *
   * 2. Merge the new type variable equivalence classes with previously
   *    collected type variable equivalence classes with representatives,
   *    forming equivalence classes with multiple representatives that are the
   *    representatives of the merged equivalence classes.
   *
   * 3. Find single representatives and make the other representatives members
   *    of the merged classes, and create instantiations from old
   *    representatives to the new single representatives, except for
   *    representatives to representatives.
   *
   * 4. Update the previous representatives in the new instantiations tyis with
   *    the new representatives from the merged type variable equivalence
   *    classes, by applying the old to new representative instantiations on
   *    tyis.
   *
   * 5. Add the new representative instantiations to the new type variable
   *    instantiations tyis.
   *
   * This results in type instantiations that can be applied on previous type
   * instantiations and the terms, such that the instantiated term variable has
   * the same type as the instantiation term value.
   *)
  fun apply_type_equivalences itype1 itype2 tyis ntyivs collected_tyrvecs =
    let val collected_tyrvecs = remove_instantiated_tyrvecs collected_tyrvecs tyis      (* 0. *)
        val nvecs = find_ui_type_vecs itype1 itype2 ntyivs in                           (* 1. *)
    let val collected_rsvecs = merge_collected_and_new_vecs collected_tyrvecs nvecs in  (* 2. *)
    let val (collected_tyrvecs, ris) = find_representatives_with_is collected_rsvecs in (* 3. *)
    let val tyis = instantiate_instantiations type_subst tyis ris in                    (* 4. *)
    let val tyis = union_lists same_type_i ris tyis in (* 5. Different subterms may involve same type variables: Avoid duplicates. *)
      (tyis, collected_tyrvecs)
    end end end end end

  (* Given a type instantiation type_variable |-> type_value, instantiations all
   * term instantiation values with this type instantiation.
   *)
  fun apply_tyi_on_teis type_variable type_value [] = []
    | apply_tyi_on_teis type_variable type_value ({redex = term_variable, residue = term_value}::teis) =
      let val updated_teis = apply_tyi_on_teis type_variable type_value teis
          val updated_tei = {redex   = inst [type_variable |-> type_value] term_variable,
                             residue = inst [type_variable |-> type_value] term_value} in
        updated_tei::updated_teis
      end

  (* Given a type instantiation type_variable |-> type_value and a new term
   * instantiation, applies the type instantiation on the term instantiation.
   *)
  fun apply_tyi_on_new_tei type_variable type_value NONE = NONE
    | apply_tyi_on_new_tei type_variable type_value (SOME {redex = term_variable, residue = term_value}) =
      SOME {redex = inst [type_variable |-> type_value] term_variable, residue = inst [type_variable |-> type_value] term_value}

  (* Given a type instantiation type_variable |-> type_value and a list of term
   * instantiations, updates term variables and term values with the new type
   * instantiation for each term instantiation.
   *)
  fun apply_tyi_on_teivs type_variable type_value [] = []
    | apply_tyi_on_teivs type_variable type_value (nteiv::nteivs) =
      let val updated_nteivs = apply_tyi_on_teivs type_variable type_value nteivs
          val updated_nteiv = inst [type_variable |-> type_value] nteiv in
        updated_nteiv::updated_nteivs
      end

  (* Updates the from and to components of a list of substitutions with another
   * substitution operator which embeds the old and new values.
   *)
  fun subst_i substitute substitutions_to_update =
    map (fn {redex = from, residue = to} => {redex = substitute from, residue = substitute to}) substitutions_to_update

  (* Apply the type instantiations tyis (last argument):
     a) Apply type instantiations tyis on previously collected type
        instantiations.
     b) Apply type instantiations tyis on collected term instantiations.
     c) Apply type instantiations tyis on the current terms being traversed to
        find instantiations.
     d) Apply type instantiations tyis on tei.
     e) Apply type instantiations tyis on the instantiable term variables
        nteivs.
   *)
  fun apply_type_instantiations collected_tyis collected_teis nte1 nte2 tei nteivs ntyivs [] =
      (collected_tyis, collected_teis, nte1, nte2, tei, nteivs, ntyivs)
    | apply_type_instantiations collected_tyis collected_teis nte1 nte2 tei nteivs ntyivs ({redex = type_variable, residue = type_value}::tyis) =
      let val collected_tyis = update_instantiations type_subst type_variable type_value collected_tyis (* a) *)
          val collected_teis = apply_tyi_on_teis type_variable type_value collected_teis                (* b) *)
          val nte1 = Term.inst [type_variable |-> type_value] nte1                                      (* c) *)
          val nte2 = Term.inst [type_variable |-> type_value] nte2                                      (* c) *)
          val tei = apply_tyi_on_new_tei type_variable type_value tei                                   (* d) *)
          val nteivs = apply_tyi_on_teivs type_variable type_value nteivs                               (* e) *)
          (* iii) No type instantiations needed for correct comparison since only
           *      type variables are compared. No duplicates in ntyivs implies
           *      that remove_first_occurrence gives the same result as filter.
           *)
          val ntyivs = remove_first_occurrence same_type type_variable ntyivs in
        (* Recursive application processing the next type instantiation. *)
        apply_type_instantiations collected_tyis collected_teis nte1 nte2 tei nteivs ntyivs tyis
      end

  (* Given a term instantiation variable |-> value, substitutes value for
   * variable in each term instantiation value of a given list of term
   * instantiations.
   *)
  fun apply_term_instantiation NONE teis = teis
    | apply_term_instantiation (SOME {redex = variable, residue = value}) [] = []
    | apply_term_instantiation (SOME {redex = variable, residue = value}) ({redex = tei_var, residue = tei_val}::teis) =
      let val updated_term_instantiations = apply_term_instantiation (SOME {redex = variable, residue = value}) teis
          val updated_term_instantiation = {redex = tei_var, residue = subst [variable |-> value] tei_val} in
        updated_term_instantiation::updated_term_instantiations
      end

  (* Given a variable equivalence class split_vec and a list of variable
   * equivalence classes vecs, returns two lists, one equivalence class resulting
   * from merging all equivalence classes having a member in common with
   * split_vec, and one list with equivalence classes having no member in common
   * with split_vec.
   *)
  fun split_rvecs sr sms [] = ([], [])
    | split_rvecs sr sms ((r, ms)::rvecs) =
      let val (merged_relevant_vec, irrelevant_rvecs) = split_rvecs sr sms rvecs in
        if exists (fn v => exists (same_term v) (sr::sms)) (r::ms) then
          ((r::ms) @ merged_relevant_vec, irrelevant_rvecs)
        else
          (merged_relevant_vec, (r, ms)::irrelevant_rvecs)
      end

  (* Given two lists with equivalence classes (disjoint within each list), merges
   * the equivalence classes.
   *)
  fun merge_rvecs tervecs1 [] = tervecs1
    | merge_rvecs tervecs1 ((sr, sms)::tervecs2) =
      let val merged_rvecs = merge_rvecs tervecs1 tervecs2 in
      let val (merged_relevant_vec, irrelevant_rvecs) = split_rvecs sr sms merged_rvecs in
      let val vec = union_lists same_term (sr::sms) merged_relevant_vec in
      let val r = hd vec
          val ms = tl vec in
        (r, ms)::irrelevant_rvecs
      end end end end

  (* Step 7.
   *
   * Inputs:
   * -nte1: Term variable instantiated term 1.
   * -nte2: Term variable instantiated term 2.
   * -unteivs: Uninstantiated instantiable term variables.
   *
   * nte1 and nte2 are equal except for matching instantiable term variables in
   * unteivs, where nte1, nte2 and the term variables in unteivs all are type
   * instantiated to have consistent types (matching subtrees have the same types
   * and the variables in unteivs have the same type as their occurrences in nte1
   * and nte2).
   *
   * Outputs: A list of term variable equivalence classes, where each class is of
   * the form (r, ms), with the representative r not among the members ms, even
   * though r is a member of the class. All members of a class must be
   * instantiated to the same variable since they occur at matching positions
   * (potentially via chains of matching positions; e.g. a matches b and b
   * matches c gives the class {a, b, c}).
   *)
  fun find_tervecs nte1 nte2 unteivs =
    (* NO NEED TO CHECK BOUNDED VARIABLES AS instantiable VARIABLES ARE UNIQUE!
     *)
    if is_var nte1 then (* nte1 has the same structure as nte2; no need to check nte2. *)
      if is_in same_term unteivs nte1 then (* instantiable variables. *)
      (* Avoid overlap between representatives and explicit members
       * (representatives are implicit members since they do not overlap the
       * explicit members).
       *)
        if same_term nte1 nte2 then
          [(nte1, [])]
        else
          [(nte1, [nte2])]
      else (* Not instantiable variables. *)
        []
    else if is_const nte1 then (* nte1 has the same structure as nte2; no need to check nte2. *)
      []
    else if is_comb nte1 then (* nte1 has the same structure as nte2; no need to check nte2. *)
      let val (ntef1, nteas1) = strip_comb nte1
          val (ntef2, nteas2) = strip_comb nte2
          fun find_tervecs_rec []      [] = []
            | find_tervecs_rec (_::_)  [] = []
            | find_tervecs_rec [] (_::_)  = []
            | find_tervecs_rec (te1::tes1) (te2::tes2) =
              let val tervecs_rec = find_tervecs_rec tes1 tes2
                  val tervecs = find_tervecs te1 te2 unteivs in
                merge_rvecs tervecs_rec tervecs
              end in
        find_tervecs_rec (ntef1::nteas1) (ntef2::nteas2)
      end
    else (* is_abs nte1 *)
      let val body1 = (#2 o dest_abs) nte1
          val body2 = (#2 o dest_abs) nte2 in
        find_tervecs body1 body2 unteivs
      end

  (* Input: Term variable equivalence classes with one representative and a
   * list of members.
   *
   * Outputs: Instantiations from members to their representative, and updated
   * list of remaining "uninstantiated" (within quotation marks since these
   * instantiations only cause change of names) variables.
   *)
  fun find_tervecs_is nteivs [] = ([], nteivs)
    | find_tervecs_is nteivs ((r, ms)::rvecs) =
      let val (ris, nteivs) = find_tervecs_is nteivs rvecs
          fun update_ris_nteivs (m, (ris, nteivs)) = ({redex = m, residue = r}::ris, remove_first_occurrence same_term m nteivs) in
      let val (ris, nteivs) = foldl update_ris_nteivs (ris, nteivs) ms in
        (ris, nteivs)
      end end

  fun is_new is_same [] v = false
    | is_new is_same ({redex = old, residue = new}::old_new) v =
      if is_same v new then
        true
      else
        is_new is_same old_new v

  fun separate_variables condition1 [] = ([], [])
    | separate_variables condition1 (v::vs) =
      let val (vs1, vs2) = separate_variables condition1 vs in
        if condition1 v then
          (v::vs1, vs2)
        else
          (vs1, v::vs2)
      end

  fun separate_instantiations condition1 [] = ([], [])
    | separate_instantiations condition1 ({redex = v, residue = i}::is) =
      let val (is1, is2) = separate_instantiations condition1 is in
        if condition1 v then
          ({redex = v, residue = i}::is1, is2)
        else
          (is1, {redex = v, residue = i}::is2)
      end

  (* Steps 6 and 7 of the algorithm:
   *
   * As long as the following procedure returns an instantiation, collect them,
   * apply them, and re-apply the procedure on the returned instantiated terms
   * to be made equal.
   *
   * Form nteivs = nteivs1 ∪ nteivs2 and ntyivs = ntyivs1 ∪ ntyivs2, since
   * instantiable variables originating in one term/type may occur in the other
   * term/type due to instantiations, and they are all unique among the
   * terms/types enabling finding the original variable corresponding to the new
   * variable.
   *
   * Traverse nte1 and nte2 in parallel with respect to their structure as
   * follows, with the stack bvars initialized to be empty:
   * -One subterm is a variable:
   *  *If nte1 is a variable:
   *   #If nte1 occurs in bvars:
   *    +If nte2 occurs in the same pair and not in any other pair above:
   *     >If the types of nte1 and nte2 can be made equal according to tyis1 and
   *      tyis2:
   *      Return SOME (NONE, tyis), meaning no term instantiation but type
   *      instantiations tyis (which may be empty).
   *     >Otherwise:
   *      Return NONE, meaning failure.
   *    +Otherwise:
   *     Return NONE, meaning failure.
   *   #If nte1 is instantiable:
   *    +If nte2 is an instantiable variable:
   *     >If the types of nte1 and nte2 can be made equal according to tyis:
   *      Return SOME (NONE, tyis), meaning no term instantiation but type
   *      instantiations tyis (which may be empty).
   *     >Otherwise:
   *      Return NONE, meaning failure.
   *    +Otherwise:
   *     >If the types of nte1 and nte2 can be made equal according to tyis:
   *      Return SOME (SOME (nte1, nte2), tyis),
   *      meaning term1 instantiation of nte1 to nte2 with type instantiations
   *      tyis.
   *     >Return NONE, meaning failure.
   *   #If nte2 is an instantiable variable:
   *    +If the types of nte1 and nte2 can be made equal according to tyis:
   *     Return SOME (SOME (nte2, nte1), tyis), meaning no term instantiation but
   *     type instantiations tyis (which may be empty).
   *    +Otherwise:
   *     Return NONE, meaning failure.
   *   #If nte1 and nte2 is the same variable:
   *    >If the types of nte1 and nte2 can be made equal according to tyis:
   *     Return SOME (NONE, tyis), meaning no term instantiation but type
   *     instantiations tyis.
   *    >Return NONE, meaning no failure.
   *   #Otherwise: Return NONE, meaning failure.
   *  *Otherwise (nte2 is a variable since at least one term is a variable and
   *   nte1 is not a variable due to the previous test):
   *   #If nte2 occurs in bvars:
   *    Return NONE, meaning failure.
   *   #If nte2 is instantiable:
   *    >If the types of nte1 and nte2 can be made equal according to tyis:
   *     Return SOME (SOME (nte2, nte1), tyis), meaning nte2 instantiated to nte1
   *     with type instantiations tyis.
   *    >Return NONE, meaning failure.
   *   #Otherwise:
   *    Return NONE, meaning failure.
   * -If one term is a constant:
   *  #If nte1 and nte2 are the same constant:
   *   >If the types of nte1 and nte2 can be made equal according to tyis:
   *    Return SOME (NONE, tyis), meaning no term instantiation but with type
   *    instantiations tyis.
   *   >Otherwise:
   *    Return NONE, meaning failure.
   *  #Otherwise:
   *   Return NONE, meaning failure.
   * -If one term is an application:
   *  #If nte1 and nte2 are both applications:
   *   Recur on arguments:
   *   +If NONE is returned, return NONE.
   *   +If SOME (tei, tyis) is returned with tei being SOME, or tyis not being
   *    empty, return SOME (tei, tyis). That is, return a result if it contains an
   *    instantiation.
   *   +Otherwise: Recur on functions and return that result.
   *  #Otherwise:
   *   Return NONE, meaning failure.
   * -Otherwise (one term is an abstraction):
   *  #If nte1 and nte2 are both abstractions:
   *   Recur on bodies with bounded variables put on the stack, and return that
   *   result.
   *  #Otherwise:
   *   Return NONE, meaning failure.
   * 
   * When a term and type instantiations tei and tyis are returned they are
   * applied as follows:
   * 1. Apply the type instantiations tyis:
   *    a) Apply type instantiations tyis on previously collected type
   *       instantiations.
   *    b) Add tyis to the previously collected type instantiations.
   *    c) Remove the instantiated type variables (tyis) from the instantiable
   *       type variables (ntyivs).
   *    d) Apply type instantiations tyis on collected term instantiations.
   *    e) Apply type instantiations tyis on the current terms being traversed to
   *       find instantiations.
   *    f) Apply type instantiations tyis on tei.
   *    g) Apply type instantiations tyis on the instantiable term variables
   *       nteivs.
   * 2. Apply the term instantiation tei:
   *    g) Apply the term instantiation tei on previously collected term
   *       instantiations.
   *    h) Add tei to previously collected term instantiations.
   *    i) Remove the instantiated term variable in tei from the instantiable
   *       term variables (nteivs).
   * 
   * When step 2 is complete, then all type instantiations are identified, and
   * all term instantiations are also identified with the terms in the
   * instantiations being type instantiated as specified by the type
   * instantiations. This means that the instantiations are directly applicable
   * on the original terms, as long as the type instantiations are applied first
   * on the original terms, if it was not for the renaming from old to new unique
   * variable names.
   *
   * When a term and type instantiations tei and tyis are returned they are
   * applied as follows:
   * i)    Remove the instantiated term variable in tei from the instantiable
   *       term variables (nteivs).
   * ii)   Find type variable equivalence classes, merge with previously
   *       collected classes, find new representatives, create instantiations
   *       from previous representatives to new representatives, and apply these
   *       representative instantiations on the new instantiations tyis, and
   *       merge the new representative instantiations with the new type
   *       instantiations tyis.
   *
   *       EVERY PREVIOUS REPRESENTATIVE IS REMOVED FROM THE LIST OF
   *       instantiable TYPE VARIABLES BY MEANS OF THE REPRESENTATIVE
   *       INSTANTIATIONS.
   *
   * iii)  Apply the type instantiations tyis on the previously collected type
   *       and term instantiations, current terms being traversed to find
   *       instantiations, the potentially found term instantiation, and the
   *       instantiable term variables.
   * iv)   Remove the instantiated type variables (tyis) from the instantiable
   *       type variables (ntyivs).
   * v)    Add tyis to the previously collected type instantiations.
   * vi)   Apply the term instantiation tei on previously collected term
   *       instantiations.
   * vii)  Apply the term instantiation tei on the terms being traversed and to
   *       be made equal.
   * viii) Add tei to previously collected term instantiations.
   *
   * When this second step is complete, then all type instantiations are
   * identified, and all term instantiations are also identified with the terms
   * in the instantiations being type instantiated as specified by the type
   * instantiations. This means that the instantiations are directly applicable
   * on the original terms, as long as the type instantiations are applied first
   * on the original terms.
   *)
  fun find_term_instantiations nte1 nte2 ntyivs nteivs old_new_ty1 old_new_ty2 old_new_te1 old_new_te2 =
    let fun find_term_instantiations_rec collected_tyis collected_tyrvecs collected_teis nte1 nte2 nteivs ntyivs =
      case find_term_instantiation nte1 nte2 nteivs ntyivs [] of
        NONE => NONE (* Failure *)
      | SOME (tei, itype1, itype2, tyis) =>
        if cyclic_tyis tyis orelse cyclic_tei tei then (* Types or term variables instantiated to a body containing themselves. *)
          NONE
        else
              (* i) Between each instantiation search, all occurrences of the same
               *    variable have the same type, and which is consistent with
               *    nteivs. This property holds at this control point of the
               *    program and is preserved by the following updates.
               *)
          let val nteivs = if isSome tei then filter (not_same_term (#redex (valOf tei))) nteivs else nteivs in
          let val (tyis, collected_tyrvecs) = apply_type_equivalences itype1 itype2 tyis ntyivs collected_tyrvecs in (* ii) *)
          let val (collected_tyis, collected_teis, nte1, nte2, tei, nteivs, ntyivs) =
                   apply_type_instantiations collected_tyis collected_teis nte1 nte2 tei nteivs ntyivs tyis in       (* iii & iv *)
          let val collected_tyis = union_lists same_type_i tyis collected_tyis                                       (* v)  *)
              val collected_teis = apply_term_instantiation tei collected_teis                                       (* vi) *)
              val nte1 = if isSome tei then subst [valOf tei] nte1 else nte1                                         (* vii) *)
              val nte2 = if isSome tei then subst [valOf tei] nte2 else nte2 in
          let val collected_teis = if isSome tei then (valOf tei)::collected_teis else collected_teis in             (* viii) *)
            if (not o isSome) tei andalso null tyis then (* No additional term or type instantiations exist: Terminate. *)
              let val old_new_te1 = subst_i (inst collected_tyis) old_new_te1    (* Update types of old_new1. *)
                  val old_new_te2 = subst_i (inst collected_tyis) old_new_te2    (* Update types of old_new2. *)

                  (* Step 7. *)
                  val tervecs = find_tervecs nte1 nte2 nteivs in (* nteivs are the variables that were not instantiated. *)
              let val (ris, nteivs) = find_tervecs_is nteivs tervecs in
              let val collected_teis = instantiate_instantiations subst collected_teis ris in
              let val collected_teis = collected_teis @ ris
                  val (nutyvs1, nutyvs2) = separate_variables (is_new same_type old_new_ty1) ntyivs
                  val (nutevs1, nutevs2) = separate_variables (is_new same_term old_new_te1) nteivs
                  val (tyis1, tyis2) = separate_instantiations (is_new same_type old_new_ty1) collected_tyis in
              let val (teis1, teis2) = separate_instantiations (is_new same_term old_new_te1) collected_teis in

                SOME (tyis1, tyis2, collected_tyrvecs, teis1, teis2, tervecs, old_new_te1, old_new_te2, nutyvs1, nutyvs2, nutevs1, nutevs2, nte1, nte2)
              end end end end end
            else
              find_term_instantiations_rec collected_tyis collected_tyrvecs collected_teis nte1 nte2 nteivs ntyivs
          end end end end end in
      find_term_instantiations_rec [] [] [] nte1 nte2 nteivs ntyivs
    end




(*

val SOME (tei, itype1, itype2, tyis) = find_term_instantiation nte1 nte2 nteivs ntyivs []
val collected_tyrvecs = [] :  (hol_type * hol_type list) list



val nte1 = ``c : 'a``
val nte2 = ``x : 'a`` (*: 'b*)
val nteivs = [``x : 'a``] (* : 'b*)
val ntyivs = [``: 'a``(*, ``: 'b``*)]
val collected_tyis = [] : (hol_type * hol_type) list
val collected_tyrvecs = [] : (hol_type * (hol_type list)) list
val collected_teis = [] : (term * term) list
find_term_instantiations nte1 nte2 nteivs ntyivs

val nte1 = ``(p : 'a -> 'b) (y : 'a)``
val nte2 = ``x : 'c``
val nteivs = [``p : 'a -> 'b``, ``y : 'a``, ``x : 'c``]
val ntyivs = [``: 'a``, ``: 'b``, ``: 'c``]
find_term_instantiations nte1 nte2 nteivs ntyivs
val SOME (tei, itype1, itype2, tyis) = find_term_instantiation nte1 nte2 nteivs ntyivs []



val nte1 = ``(f : 'b -> 'd) ((p : 'a -> 'b) (y : 'a))``
val nte2 = ``(x : 'e -> 'c) (z : 'e)``
val nteivs = [``y : 'a``, ``x : 'e -> 'c``, ``z : 'e``]
val ntyivs = [``: 'a``, ``: 'b``, ``: 'e``, ``: 'd`` (*, ``: 'c``*)]
find_term_instantiations nte1 nte2 nteivs ntyivs
x |-> f
z |-> p y

'e <-|-> 'b
'd |-> 'c
*)






  (* Generates a representative for a term/type (1 or 2; referred to as this)
   * based on the members of a variable equivalence class, since the
   * representative of the class originates from the other term/type (2 or 1;
   * referred to as other).
   *
   * Algortihm:
   * 1. If there is no member originating from the term/type (determined by
   *    this_old_new), then a representative is created based on the
   *    representative for the other term/type (other_or), where this_is_invalid
   *    and this_used_ors indicate invalid old representative names.
   * 2. Otherwise, a representative is created based on the old name of a member
   *    originating from the term/type (determined by this_old_new), renamed only
   *    if necessary.
   * 3. The generated new old substitution has its:
   *    -from component set to the new name that all members are instantiated to
   *     (other_nr).
   *    -to component set to the generated old representative.
   *)
  fun generate_unrepresentated_new_old is_same genr this_is_invalid this_old_new this_used_ors other_or other_nr ms =
    case List.find (fn {redex = old, residue = new} => exists (is_same new) ms) this_old_new of
      NONE =>
      let val (this_or, this_used_ors) = genr this_used_ors other_or in
        ({redex = other_nr, residue = this_or}, this_used_ors)
      end
    | SOME {redex = this_or, residue = _} =>
      if this_is_invalid this_used_ors this_or then
        (* this_or occurs as an uninstantiable variable name in its type/term
         * after instantiation or has been used previously. Must be renamed.
         *)
        let val (this_or, this_used_ors) = genr this_used_ors this_or in
          ({redex = other_nr, residue = this_or}, this_used_ors)
        end
      else
        (* this_or is previously unused, thus no duplicate by adding it to this_used_ors. *)
        ({redex = other_nr, residue = this_or}, this_or::this_used_ors)

  (* Given a function that generates a representative, preferrably or, an invalid
   * predicate, and used old representatives, returnes the chosen selected old
   * representative, updated used old representatives, and, if needed, an
   * instantiation for updating the old name of the representative.
   *)
  fun generate_old_representative genr is_invalid used_ors or =
    if is_invalid used_ors or then
      let val (renamed_or, used_ors) = genr used_ors or in
        (renamed_or, used_ors, [{redex = or, residue = renamed_or}])
      end
    else
      (or, or::used_ors, []) (* No renaming, or is now used as a representative, and no renaming instantiation. *)

  (* NOTE: Only representatives can occur in terms/types, in contrast to members.
   *
   * Algorithm:
   * 1. Initialize is_invalid1/is_invalid2 to be true if the given variable
   *    occurs as an uninstantiated variable among the instantiations.
   * 2. For each variable equivalence class with a representative:
   *    a) If the old variable name of the representative occurs as an
   *       uninstantiated variable for the same term/type from which the
   *       representative originated from, or the old variable has been used to
   *       rename a previous representative, then the representative must be
   *       given a new old name, which must be added to the invalids for later
   *       representatives.
   *
   *       NOTE: These accumulated used old representatives represent the old
   *       variable names that were not instantiated (motivated in b) and c)).
   *
   *    b) The representative is given a unique old name, which is added to the
   *       used list for its originating type/term. This representative occurs in
   *       at least one instantiation since it is a representative and was found
   *       when rvecs where identified. It occurs in instantiation values of its
   *       originating type/term, since a representative is never replaced, but
   *       only potentially copied to the other term/type and other subtrees of
   *       its originating type/term.
   *
   *    c) An old representative for the other term is given a unique old name,
   *       which is added to the used list for the associated type/term. The new
   *       variables mapped to this representative occurs in the other term/type
   *       due to the way variable equivalence classes are created:
   *       Uninstantiated variables occur in both terms.
   *
   *    d) If the representative changes old name, then an instantiation must be
   *       added from its old name to its new name, for the instantiated term to
   *       reflect the new old name, which shall not be renamed with new_old
   *       substitutions.
   *
   *    e) The members of a variable equivalence class are instantiated to the
   *       representative, and shall therefore have new to old substitutions from
   *       their new names to the old name of the representative for the
   *       term/type the representative occurs in.
   *
   * How shall new variables be renamed?
   * -The "from"-component of instantiations shall be the old original name for
   *  all instantiations.
   * -The "to"-component of instantiations shall be the updated old name of the
   *  representative associated with the term the representative (instantiation)
   *  occurs in, except the new instantiations whose purpose is to rename
   *  uninstantiated variables.
   *
   * This means:
   * -Instantiations renaming uninstantiated variables are unchanged.
   * -Instantiations created to make the terms equal, have their from component
   *  set to their original old names, and their to component set to the updated
   *  old name of the representative for the term/type of the instantiation.
   *
   * Inputs:
   * -is_same: Comparator for instantiation variables (terms or types).
   * -genr: Generator of representatives given invalid predicate and a preferred
   *  old representative.
   * -is_invalid1/is_invalid2: Predicates given a used representative list and a
   *  name stating whether the name is a valid old name for a representative.
   * -old_new1/old_new2: Old to new substitutions.
   * -rvecs: Variable equivalence classes with one representative.
   *
   * Outputs:
   * -new_old_r1/new_old_r2: Substitutions to be applied on the to component of
   *  previously generated instantiations to rename the uninstantiated variables
   *  to their updated old value (updated to avoid clashes with uninstantiable
   *  variables originating from the other type/term).
   * -uvs1/uvs2: All used updated old representative names, which represent the
   *  variables that were not instantiated.
   * -ris1/ris2: Representative instantiations for renaming uninstantiated
   *  variables to avoid name clashing with uninstantiable variables.
   * -iuvs: Substitutions from representatives of type2/term2 to representatives
   *  of type1/term1 for representatives belonging to the same type variable
   *  equivalence class.
   *)
  fun find_new_old_to is_same genr is_invalid old_new1 old_new2 [] = ([], [], [], [])
    | find_new_old_to is_same genr is_invalid old_new1 old_new2 ((r, ms)::rvecs) =
      let val (new_old_rec, ris1, ris2, used_ors) = find_new_old_to is_same genr is_invalid old_new1 old_new2 rvecs in
        case List.find (fn {redex = old, residue = new} => is_same r new) old_new1 of
          SOME {redex = or1, residue = nr1} =>                                        (* r originates from type1/term1. *)
          (* If or1 is a variable name of an uninstantiable variable after
           * instantiation, or it is an instantiable variable occurring only in
           * one side of an equation, or it has been used for another
           * representative, then it must be renamed.
           *)
          let val (or, used_ors, ri1) = generate_old_representative genr is_invalid used_ors or1 in
          let val new_old = {redex = nr1, residue = or} in
            (new_old::new_old_rec, ri1 @ ris1, ris2, used_ors)
          end end
        | NONE =>
        case List.find (fn {redex = old, residue = new} => is_same r new) old_new2 of
          SOME {redex = or2, residue = nr2} =>                                        (* r originates from type2/term2. *)
          let val (or, used_ors, ri2) = generate_old_representative genr is_invalid used_ors or2 in
          let val new_old = {redex = nr2, residue = or} in
            (new_old::new_old_rec, ris1, ri2 @ ris2, used_ors)
          end end
        | NONE => raise (mk_HOL_ERR "ltac" "generate_new_old" "Representative has no old variable.")
      end





  fun reverse_remove_substitutions is_same nuivs [] = []
    | reverse_remove_substitutions is_same nuivs ({redex = old, residue = new}::old_new) =
      let val reversed_removed_substitutions = reverse_remove_substitutions is_same nuivs old_new in
        if exists (is_same new) nuivs then (* new is uninstantiated; skip it since it does not occur in the from component. *)
          reversed_removed_substitutions
        else
          {redex = new, residue = old}::reversed_removed_substitutions
      end

  (* Given original new to old substitutions, and uninstantiated variables of
   * type1/term1 and type2/term2, returns substitutions for renaming the from
   * components of the instantiations, except for the instantiations for renaming
   * uninstantiated variables.
   *)
  fun find_new_old_from is_same old_new1 old_new2 nuvs1 nuvs2 =
    (reverse_remove_substitutions is_same nuvs1 old_new1, reverse_remove_substitutions is_same nuvs2 old_new2)

  (* -nutyvs1/nutyvs2: New uninstantiated type variables in type1/type2.
   *)
  fun find_new_old_from_ty old_new_ty1 old_new_ty2 nutyvs1 nutyvs2 =
    find_new_old_from same_type old_new_ty1 old_new_ty2 nutyvs1 nutyvs2

  (* -nutevs1/nutevs2: New uninstantiated term variables in term1/term2.
   *)
  fun find_new_old_from_te old_new_te1 old_new_te2 nutevs1 nutevs2 =
    find_new_old_from same_term old_new_te1 old_new_te2 nutevs1 nutevs2

  (* Inputs:
   * -Predicate stating whether a representative is invalid.
   * -A representative of the other type which is the preferred name for the
   *  generated representative of this name. The representative must be renamed
   *  if one of the instantiable variables of this type has the same name.
   *
   * Output: A primed version of the given old representative until the name of
   * it does not occur among the instantiable old variables.
   *)
  fun generate_type_representative is_invalid_or used_ors preferred_or =
    let val preferred_or_char = (hd o tl o String.explode o dest_vartype) preferred_or in
    let fun generate_or_string or =
      if is_invalid_or used_ors (String.implode [#"'", or]) then
        generate_or_string (Char.succ or)
      else
        let val renamed_or = (mk_vartype o String.implode) [#"'", or] in (renamed_or, renamed_or::used_ors) end in
      generate_or_string preferred_or_char
    end end

  (* Based on collected type variable equivalence classes with one
   * representative, returns the new to old substitutions to be applied on the to
   * componentents of the collected type instantiations and the uninstantiated
   * type variables.
   *
   * Inputs:
   * -outyvs1/outyvs2: Old uninstantiable type variables occuring among
   *  instantiation values of type1 and type2.
   * -old_new_ty1/old_new_ty2: Old to new substitutions for type1 and type2.
   * -tyrvecs: Collected type variable equivalence classes with one
   *  representative.
   *
   * Outputs:
   * -new_old_to_ty1/new_old_to_ty2: New to old substitutions for instantiations
   *  of type1 and type2.
   * -ouvs1/ouvs2: Variables that were not instantiated.
   * -ris1/ris2: Instantiations for renaming uninstantiated variables for type1
   *  and type2 (necessary for uninstantiated representatives not occurring in
   *  any instantiation value).
   * -iuvs: Instantiations from from representatives of type2/term2 to
   *  representatives of type1/term1 for representatives that belong to the same
   *  variable equivalence class.
   *
   * NOTE: outevs1/outevs2 are invalid names of uninstantiated variables in
   * term2/term1, meaning that outevs1/outevs2 must be used in invalid2/invalid1.
   *
   * Invalid names, invalid_rs, are the uninstantiable variables of eq and rw,
   * and the instantiable variables occurring only in the left handside of eq
   * and the instantiable variables occurring only in the right handside of rw.
   *)
  fun find_new_old_to_ty invalid_rs old_new_ty1 old_new_ty2 tyrvecs =
    let fun is_invalid_g used_rs r = is_in equal (invalid_rs @ (map dest_vartype used_rs)) r in
    let val is_same = same_type
        val genr = generate_type_representative is_invalid_g
        fun is_invalid used_rs r = is_in equal (invalid_rs @ (map dest_vartype used_rs)) (dest_vartype r)
        val old_new1 = old_new_ty1
        val old_new2 = old_new_ty2 in
    let val (new_old_to_ty, ris1, ris2, uvs) = find_new_old_to is_same genr is_invalid old_new1 old_new2 tyrvecs in
      (new_old_to_ty, ris1, ris2, uvs)
    end end end

  (* Given a predicate of invalid representative names and a preferred
   * representative name, returns the preferred representative name that does not
   * satisfy the predicate of invalid representative names with as few trailing
   * primes as possible.
   *)
  fun generate_term_representative is_invalid_or used_ors preferred_or =
    let val preferred_or_string = term_to_string preferred_or in
    let fun generate_or_string or =
      if is_invalid_or used_ors or then
        generate_or_string (concat [or, "'"])
      else
        let val renamed_or = mk_var (or, type_of preferred_or) in (renamed_or, renamed_or::used_ors) end in
      generate_or_string preferred_or_string
    end end

  (* -outevs1/outevs2: Variables in term1/term2 that are not instantiable.
   *
   * NOTE: outevs1/outevs2 are invalid names of uninstantiated variables in
   * term2/term1, meaning that outevs1/outevs2 must be used in invalid2/invalid1.
   *
   * Invalid names, invalid_rs, are the uninstantiable variables of eq and rw,
   * and the instantiable variables occurring only in the left handside of eq
   * and the instantiable variables occurring only in the right handside of rw.
   *)
  fun find_new_old_to_te invalid_rs old_new_te1 old_new_te2 tervecs =
    let fun is_invalid_g used_rs r = is_in equal (invalid_rs @ (map term_to_string used_rs)) r in
    let val is_same = same_term
        val genr = generate_term_representative is_invalid_g
        fun is_invalid used_rs r = is_in equal (invalid_rs @ (map term_to_string used_rs)) (term_to_string r)
        val old_new1 = old_new_te1
        val old_new2 = old_new_te2 in
    let val (new_old_to_te, ris1, ris2, uvs) = find_new_old_to is_same genr is_invalid old_new1 old_new2 tervecs in
      (new_old_to_te, ris1, ris2, uvs)
    end end end

  (* Renames instantiations. *)
  fun rename_instantiations substitute new_old_from new_old_to [] = []
    | rename_instantiations substitute new_old_from new_old_to ({redex = nv, residue = iv}::is) =
      let val renamed_instantiations = rename_instantiations substitute new_old_from new_old_to is in
        {redex = substitute new_old_from nv, residue = substitute new_old_to iv}::renamed_instantiations
      end

  (* Renames type instantiations. *)
  fun rename_tyis new_old_from_ty1 new_old_from_ty2 new_old_to_ty tyis1 tyis2 =
    (rename_instantiations type_subst new_old_from_ty1 new_old_to_ty tyis1,
     rename_instantiations type_subst new_old_from_ty2 new_old_to_ty tyis2)

  (* Renames the term variables of term instantiations, without renaming types. *)
  fun rename_teis new_old_from_te1 new_old_from_te2 new_old_to_te teis1 teis2 =
    (rename_instantiations subst new_old_from_te1 new_old_to_te teis1,
     rename_instantiations subst new_old_from_te2 new_old_to_te teis2)

  (* Renames the type variables of term instantiations.
   *
   * How to rename types in term instantiations with old variables?
   * The type variables are all new in both the "from" and the "to"-components.
   * The term instantiations shall have types that match the original given terms
   * after the type instantiation has been applied on the original terms.
   * This corresponds to the new to old substitutions for the "to"-component.
   *)
  fun rename_tetyis new_old_to_ty teis1 teis2 =
    (subst_i (inst new_old_to_ty) teis1, subst_i (inst new_old_to_ty) teis2)














  (* Old uninstantiable type variables of term 1 with types instantiated by
   * collected type instantiations.
   *)
  fun find_old_uninstantiable_variables otyvs1 otyvs2 otevs1 otevs2 otyivs1 otyivs2 oteivs1 oteivs2 =
    let val otyuivs1 = filter (fn v => all (not_same_type v) otyivs1) otyvs1
        val otyuivs2 = filter (fn v => all (not_same_type v) otyivs2) otyvs2
        val oteuivs1 = filter (fn v => all (not_same_term v) oteivs1) otevs1
        val oteuivs2 = filter (fn v => all (not_same_term v) oteivs2) otevs2 in
      (otyuivs1, otyuivs2, oteuivs1, oteuivs2)
    end

  fun remove_self_instantiations is_same [] = []
    | remove_self_instantiations is_same ({redex = v, residue = i}::is) =
      let val removed_self_instantiations = remove_self_instantiations is_same is in
        if is_same v i then
          removed_self_instantiations
        else
          {redex = v, residue = i}::removed_self_instantiations
      end

  (* Removes final type instantiations that are identity instantiations. *)
  fun remove_self_instantiations_ty tyis = remove_self_instantiations same_type tyis

  (* Removes final term instantiations that are identity instantiations. *)
  fun remove_self_instantiations_te teis = remove_self_instantiations same_term teis

  fun remove_instantiated_variables is_same instantiations [] = []
    | remove_instantiated_variables is_same instantiations (v::vs) =
      let val removed_variables = remove_instantiated_variables is_same instantiations vs in
        if exists (fn {redex = iv, residue = _} => is_same v iv) instantiations then
          removed_variables
        else
          v::removed_variables
      end


















  (* Steps 8 to 15. Renames instantiations and uninstantiated type and term
   * variables to old names:
   *  8: New to old type substitutions.
   *  9: Old type instantiations.
   * 10: Old instantiable type variables that were not instantiated.
   * 11: New to old term variable substitutions with both new and old term
   *     variables having NEW and INSTANTIATED type variables.
   * 12: Term variable instantiations with old term variables and new
   *     instantiated type variables.
   * 13: Term variable instantiations with old term variables and old
   *     instantiated type variables.
   * 14: Old instantiable term variables that were not instantiated having new
   *     instantiated type variables.
   * 15: Old instantiable term variables that were not instantiated having old
   *     instantiated type variables.
   *
   * Inputs:
   * -old_new_ty1 old_new_ty2: Old to new type substitutions.
   * -old_new_te1 old_new_te2: Old to new term substitutions, updated with
   *  respect to collected type instantiations.
   *
   * -nutyvs1 nutyvs2: New type variables that were not instantiated.
   * -nutevs1 nutevs2: New term variables that were not instantiated, updated
   *  with respect to collected type instantiations.
   *
   * -outyvs1 outyvs2: Old uninstantiable type variables.
   * -outevs1 outevs2: Old uninstantiable term variables.
   *
   * -tyrvecs tervecs: Type and term variable equivalence classes, updated with
   *  respect to collected type instantiations.
   *
   * -tyis1 tyis2: Collected type instantiations.
   * -teis1 teis2: Collected term instantiations, updated with respect to
   *  collected type instantiations.
   *
   * Outputs:
   * -Type instantiations with old variables directly applicable on the two terms
   *  to be made equal.
   * -Term instantiations with old variables directly applicable on the two terms
   *  to be made equal, after being type instantiated.
   * -Type variables that were not instantiated.
   * -Term variables that were not instantiated, type instantiated with the
   *  collected type instantiations with old variables.
   * -Instantiated terms.
   * -Substitutions from representatives of type2/term2 to representatives of
   *  type1/term1, for representatives
   *)
(* BUGGY CODE: REMOVES INSTANTIATIONS TO UNINSTANTIABLE VARIABLES WITH THE SAME NAME (SELF-INSTANTIATIONS).
  fun new_instantiations_old
    old_new_ty1 old_new_ty2
    old_new_te1 old_new_te2
    nutyvs1 nutyvs2
    nutevs1 nutevs2
    invalid_tyrs
    invalid_ters
    tyis1 tyis2
    teis1 teis2
    tyrvecs tervecs =

    (* Renaming "from"-components of type instantiations. *)
    let val (new_old_from_ty1, new_old_from_ty2) = find_new_old_from_ty old_new_ty1 old_new_ty2 nutyvs1 nutyvs2

    (* Renaming "from"-components of term instantiations. *)
        val (new_old_from_te1, new_old_from_te2) = find_new_old_from_te old_new_te1 old_new_te2 nutevs1 nutevs2

    (* Renaming "to"-components of type instantiations, remaining uninstantiated
     * variables, and renaming substitutions of uninstantiated variables.
     *)
        val (new_old_to_ty, rtyis1, rtyis2, updated_outyvs) = find_new_old_to_ty invalid_tyrs old_new_ty1 old_new_ty2 tyrvecs

    (* Renaming "to"-components of term instantiations, remaining uninstantiated
     * variables, and renaming substitutions of uninstantiated variables.
     *)
        val (new_old_to_te, rteis1, rteis2, updated_outevs) = find_new_old_to_te invalid_ters old_new_te1 old_new_te2 tervecs in

    (* Renames type instantiations. All self-instantiations (si) are removed. *)
    let val (siotyis1, siotyis2) = rename_tyis new_old_from_ty1 new_old_from_ty2 new_old_to_ty (rtyis1 @ tyis1) (rtyis2 @ tyis2)
        val (otyis1, otyis2) = (remove_self_instantiations_ty siotyis1, remove_self_instantiations_ty siotyis2)

    (* Renames the term variables of term instantiations, without renaming types. *)
        val (otentyis1, otentyis2) = rename_teis new_old_from_te1 new_old_from_te2 new_old_to_te teis1 teis2 in

    (* Renames the type variables of term instantiations. *)
    let val (sioteis1, sioteis2) = rename_tetyis new_old_to_ty (rteis1 @ otentyis1) (rteis2 @ otentyis2) in
    let val (oteis1, oteis2) = (remove_self_instantiations_te sioteis1, remove_self_instantiations_te sioteis2)

    (* Renames the type variables of uninstantiated term variables. *)
        val updated_outevntyvs = map (inst new_old_to_ty) updated_outevs in

    (* Final type instantiations and uninstantiated variables. *)
    let val (tyis1, tyis2, utyvs) = (otyis1, otyis2, updated_outyvs)

    (* Final term instantiations and uninstantiated variables. *)
        val (teis1, teis2, utevs) = (oteis1, oteis2, updated_outevntyvs) in

      (tyis1, tyis2, teis1, teis2, utyvs, utevs)
    end end end end end
*)
  fun new_instantiations_old
    old_new_ty1 old_new_ty2
    old_new_te1 old_new_te2
    nutyvs1 nutyvs2
    nutevs1 nutevs2
    invalid_tyrs
    invalid_ters
    tyis1 tyis2
    teis1 teis2
    tyrvecs tervecs =

    (* Renaming "from"-components of type instantiations. *)
    let val (new_old_from_ty1, new_old_from_ty2) = find_new_old_from_ty old_new_ty1 old_new_ty2 nutyvs1 nutyvs2

    (* Renaming "from"-components of term instantiations. *)
        val (new_old_from_te1, new_old_from_te2) = find_new_old_from_te old_new_te1 old_new_te2 nutevs1 nutevs2

    (* Renaming "to"-components of type instantiations, remaining uninstantiated
     * variables, and renaming substitutions of uninstantiated variables.
     *)
        val (new_old_to_ty, rtyis1, rtyis2, updated_outyvs) = find_new_old_to_ty invalid_tyrs old_new_ty1 old_new_ty2 tyrvecs

    (* Renaming "to"-components of term instantiations, remaining uninstantiated
     * variables, and renaming substitutions of uninstantiated variables.
     *)
        val (new_old_to_te, rteis1, rteis2, updated_outevs) = find_new_old_to_te invalid_ters old_new_te1 old_new_te2 tervecs in

    (* Renames type instantiations. All self-instantiations (si) are removed. *)
    let val (siotyis1, siotyis2) = rename_tyis new_old_from_ty1 new_old_from_ty2 new_old_to_ty (rtyis1 @ tyis1) (rtyis2 @ tyis2)
        val (otyis1, otyis2) = (siotyis1, siotyis2)
(* BUG: REMOVES instantiations to uninstantiable variables with the same name as the instantiable variable. *)
(*      val (otyis1, otyis2) =  (remove_self_instantiations_ty siotyis1, remove_self_instantiations_ty siotyis2)*)

    (* Renames the term variables of term instantiations, without renaming types. *)
        val (otentyis1, otentyis2) = rename_teis new_old_from_te1 new_old_from_te2 new_old_to_te teis1 teis2 in

    (* Renames the type variables of term instantiations. *)
    let val (sioteis1, sioteis2) = rename_tetyis new_old_to_ty (rteis1 @ otentyis1) (rteis2 @ otentyis2) in

    let val (oteis1, oteis2) = (sioteis1, sioteis2)
(* BUG: REMOVES instantiations to uninstantiable variables with the same name as the instantiable variable. *)
(*  let val (oteis1, oteis2) = (remove_self_instantiations_te sioteis1, remove_self_instantiations_te sioteis2)*)

    (* Renames the type variables of uninstantiated term variables. *)
        val updated_outevntyvs = map (inst new_old_to_ty) updated_outevs in

    (* Final type instantiations and uninstantiated variables. *)
    let val (tyis1, tyis2, utyvs) = (otyis1, otyis2, updated_outyvs)

    (* Final term instantiations and uninstantiated variables. *)
        val (teis1, teis2, utevs) = (oteis1, oteis2, updated_outevntyvs) in

      (tyis1, tyis2, teis1, teis2, utyvs, utevs)
    end end end end end














  (* The program finding instantiations of terms to make the terms equal.
   *
   * Given two terms with their instantiable type and term variables, if
   * possible finds type and term variable instantiations that make the terms
   * equal including their types.
   *
   * Inputs:
   * @invalid_ters: Invalid term variable names (strings) for uninstantiated term
   *  variables.
   * @invalid_tyrs: Invalid type variable names (strings) for uninstantiated type
   *  variables.
   * @ote1: Term 1 (containing original/old instantiable term and type variable
   *  names).
   * @ote2: Term 2 (containing original/old instantiable term and type variable
   *  names).
   * @oteivs1: Old instantiable term variables occuring in ote1.
   * @oteivs2: Old instantiable term variables occuring in ote2.
   * @otyivs1: Old instantiable type variables occuring in ote1.
   * @otyivs2: Old instantiable type variables occuring in ote2.
   * That is, instantiable type and term variables that can be used to make the terms and their typesequal.
   *
   * Outputs:
   * -tyis1: Type instantiations for ote1.
   * -tyis2: Type instantiations for ote2.
   * -teis1: Term instantiations for ote1.
   * -teis2: Term instantiations for ote2.
   * -utyvs: Uninstantiated type variables after applying the type
   *  instantiations on ote1 and ote2.
   * -utevs: Uninstantiated term variables after applying the term
   *  instantiations on ote1 and ote2.
   *)
  fun find_equality_instantiations invalid_tyrs invalid_ters ote1 ote2 oteivs1 oteivs2 otyivs1 otyivs2 =
    (* Steps 1 and 2. *)
    let val (old_new_ty1, ntyivs1, old_new_ty2, ntyivs2) = old_instantiable_term_type_variables_new otyivs1 otyivs2 in

    (* Steps 3, 4 and 5. *)
    let val (nte1, nte2, nteivs1, nteivs2, old_new_te1, old_new_te2) = old_instantiable_term_variables_new old_new_ty1 old_new_ty2 ote1 ote2 oteivs1 oteivs2 in

    (* Steps 6 and 7. *)
    let val ntyivs = ntyivs1 @ ntyivs2
        val nteivs = nteivs1 @ nteivs2 in
    let val instantiations = find_term_instantiations nte1 nte2 ntyivs nteivs old_new_ty1 old_new_ty2 old_new_te1 old_new_te2 in
      if isSome instantiations then
        let val (tyis1, tyis2, tyrvecs, teis1, teis2, tervecs, old_new_te1, old_new_te2, nutyvs1, nutyvs2, nutevs1, nutevs2, _, _) = valOf instantiations in

        (* Steps 8 to 15. *)
        let val (tyis1, tyis2, teis1, teis2, utyvs, utevs) =
                new_instantiations_old old_new_ty1 old_new_ty2
                                       old_new_te1 old_new_te2
                                       nutyvs1 nutyvs2
                                       nutevs1 nutevs2
                                       invalid_tyrs
                                       invalid_ters
                                       tyis1 tyis2
                                       teis1 teis2
                                       tyrvecs tervecs in
          SOME (tyis1, tyis2, teis1, teis2, utyvs, utevs)
        end end
      else
        NONE
    end end end end

(*******************************************************************************)
(*******************************************************************************)
(*******************************************************************************)
(*TEST CASES********************************************************************)
(*******************************************************************************)
(*******************************************************************************)
(*******************************************************************************)

(*
val ote1 = ``x (z : 'z) (z : 'z) : 'x``
val ote2 = ``f (a : 'a) (a : 'a) : 'f``
val oteivs1 = [``x : 'z -> 'z -> 'x``, ``z : 'z``]
val oteivs2 = [``f : 'a -> 'a -> 'f``, ``a : 'a``]
val otyivs1 = [``: 'z``, ``: 'x``]
val otyivs2 = [``: 'a``, ``: 'f``]
val SOME (tyis1, tyis2, teis1, teis2, utyvs1, utyvs2, utevs1, utevs2) = find_equality_instantiations ote1 ote2 oteivs1 oteivs2 otyivs1 otyivs2
val renamed_te1 = subst teis1 (inst tyis1 ote1)
val renamed_te2 = subst teis2 (inst tyis2 ote2)
*)




(*
val ote1 = ``x (y : 'y) (z : 'z) : 'x``
val ote2 = ``f (a : 'a) (a : 'a) : 'f``
val oteivs1 = [``x : 'y -> 'z -> 'x``, ``y : 'y``, ``z : 'z``]
val oteivs2 = [``f : 'a -> 'a -> 'f``, ``a : 'a``]
val otyivs1 = [``: 'y``, ``: 'z``, ``: 'x``]
val otyivs2 = [``: 'a``, ``: 'f``]
val SOME (tyis1, tyis2, teis1, teis2, utyvs1, utyvs2, utevs1, utevs2) = find_equality_instantiations ote1 ote2 oteivs1 oteivs2 otyivs1 otyivs2
val renamed_te1 = subst teis1 (inst tyis1 ote1)
val renamed_te2 = subst teis2 (inst tyis2 ote2)
*)

(*A variable occurs in both term instantiations as uninstantiated but must be renamed in one of the instantiations but not the other*)
(*
val ote1 = ``x (y : 'y) (z : 'z) : 'x``
val ote2 = ``y (a : 'a) (a : 'a) : 'y``
val otyivs1 = [``: 'z``, ``: 'x``]
val otyivs2 = [``: 'a``, ``: 'y``]
val oteivs1 = [``x : 'y -> 'z -> 'x``, ``z : 'z``]
val oteivs2 = [``y : 'a -> 'a -> 'y``, ``a : 'a``]
val SOME (tyis1, tyis2, teis1, teis2, utyvs1, utyvs2, utevs1, utevs2) = find_equality_instantiations ote1 ote2 oteivs1 oteivs2 otyivs1 otyivs2
val renamed_te1 = subst teis1 (inst tyis1 ote1)
val renamed_te2 = subst teis2 (inst tyis2 ote2)
*)





(* All term and type variables instantiable. *)
(*
val ote1 = ``x : 'a``
val ote2 = ``y : 'b``
val oteivs1 = [``x : 'a``]
val oteivs2 = [``y : 'b``]
val otyivs1 = [``: 'a``]
val otyivs2 = [``: 'b``]
find_equality_instantiations ote1 ote2 oteivs1 oteivs2 otyivs1 otyivs2
*)

(* Only first terms type variable not instantiable. *)
(*
val ote1 = ``x : 'a``
val ote2 = ``y : 'b``
val otyivs1 = [] : hol_type list
val otyivs2 = [``: 'b``]
val oteivs1 = [``x : 'a``]
val oteivs2 = [``y : 'b``]
find_equality_instantiations ote1 ote2 oteivs1 oteivs2 otyivs1 otyivs2
*)

(* Only first term and type variable not instantiable. *)
(*
val ote1 = ``x : 'a``
val ote2 = ``y : 'b``
val otyivs1 = [] : hol_type list
val otyivs2 = [``: 'b``]
val oteivs1 = []
val oteivs2 = [``y : 'b``]
find_equality_instantiations ote1 ote2 oteivs1 oteivs2 otyivs1 otyivs2
*)

(* Only first term has instantiable type variable, and second term has
 * instantiable term variable.
 *)
(*
val ote1 = ``x : 'a``
val ote2 = ``y : 'b``
val otyivs1 = [``: 'a``] : hol_type list
val otyivs2 = [] : hol_type list
val oteivs1 = [] : term list
val oteivs2 = [``y : 'b``]
val SOME (tyis1, tyis2, teis1, teis2, utyvs1, utyvs2, utevs1, utevs2) =
find_equality_instantiations ote1 ote2 oteivs1 oteivs2 otyivs1 otyivs2
*)

(* Only first term has instantiable type variable, and second term has
 * instantiable term variable.
 *)
(*
val ote1 = ``(f : 'a -> 'b) (x : 'a)``
val ote2 = ``y : 'c``
val otyivs1 = [``: 'a``, ``: 'b``] : hol_type list
val otyivs2 = [``: 'c``] : hol_type list
val oteivs1 = [] : term list
val oteivs2 = [``y : 'c``]
val SOME (tyis1, tyis2, teis1, teis2, utyvs1, utyvs2, utevs1, utevs2) =
find_equality_instantiations ote1 ote2 oteivs1 oteivs2 otyivs1 otyivs2
val renamed_te1 = subst teis1 (inst tyis1 ote1)
val renamed_te2 = subst teis2 (inst tyis2 ote2)
*)

(* f uninstantiable *)
(*
val ote1 = ``(f : 'a -> 'b) (x : 'a)``
val ote2 = ``x : 'c -> 'a``
val otyivs1 = [``: 'a``, ``: 'b``] : hol_type list
val otyivs2 = [``: 'c``, ``: 'a``] : hol_type list
val oteivs1 = [``x : 'a``] : term list
val oteivs2 = [``x : 'c -> 'a``]
val SOME (tyis1, tyis2, teis1, teis2, utyvs1, utyvs2, utevs1, utevs2) =
find_equality_instantiations ote1 ote2 oteivs1 oteivs2 otyivs1 otyivs2
val renamed_te1 = subst teis1 (inst tyis1 ote1)
val renamed_te2 = subst teis2 (inst tyis2 ote2)
*)

(* *)
(*
val f = ``f : ('a -> 'k) -> 'b -> ('c # num # 'e) -> 'g # 'h # num # 'b``
val g = ``g : 'i         -> 'j -> 'k              -> 'k # num # 'h # 'm``

val a = ``a : ('a -> 'k)``
val x = ``x : 'i``

val b = ``b : 'b``
val y = ``y : 'j``

val c = ``c : ('c # num # 'e)``
val z = ``z : 'k``

val ote1 = mk_comb (mk_comb (mk_comb (f, a), b), c)
val ote2 = mk_comb (mk_comb (mk_comb (g, x), y), z)
val otyivs1 = type_vars_in_term ote1
val otyivs2 = type_vars_in_term ote2
val oteivs1 = [f, a, b, c]
val oteivs2 = [g, x, y, z]
val SOME (tyis1, tyis2, teis1, teis2, utyvs1, utyvs2, utevs1, utevs2) =
find_equality_instantiations ote1 ote2 oteivs1 oteivs2 otyivs1 otyivs2
val renamed_te1 = subst teis1 (inst tyis1 ote1)
val renamed_te2 = subst teis2 (inst tyis2 ote2)
*)

(* *)
(*
val f = ``f : ('a -> 'k) -> 'b -> ('c # num # 'e) -> 'g # 'h # num # 'b``
val g = ``g : 'i         -> 'j -> 'k              -> 'k # num # 'h # 'm``

val a = ``a : ('a -> 'k)``
val x = ``x : 'i``

val b = ``b : 'b``
val y = ``y : 'j``

val c = ``c : 'c # num # 'e``
val z = ``z : 'k``

val ote1 = mk_comb (mk_comb (mk_comb (f, a), b), c)
val ote2 = mk_comb (mk_comb (mk_comb (g, x), y), z)
val otyivs1 = type_vars_in_term ote1
val otyivs2 = type_vars_in_term ote2
val oteivs1 = [f,   b]
val oteivs2 = [  x,   z]
val SOME (tyis1, tyis2, teis1, teis2, utyvs1, utyvs2, utevs1, utevs2) =
find_equality_instantiations ote1 ote2 oteivs1 oteivs2 otyivs1 otyivs2
val renamed_te1 = subst teis1 (inst tyis1 ote1)
val renamed_te2 = subst teis2 (inst tyis2 ote2)
*)



(* *)
(*
val f = ``f : 'b -> ('c # 'e) -> 'g # 'b``
val g = ``g : 'b -> 'c        -> 'c # 'e``

val b = ``b : 'b``
val y = ``y : 'b``

val c = ``c : ('c # 'e)``
val z = ``z : 'c``

val ote1 = mk_comb (mk_comb (f, b), c)
val ote2 = mk_comb (mk_comb (g, y), z)
val otyivs1 = type_vars_in_term ote1
val otyivs2 = remove_first_occurrence same_type ``: 'e`` (type_vars_in_term ote2)
val oteivs1 = [f,   c]
val oteivs2 = [  y   ]

let val cputimer = Timer.startCPUTimer ()
val SOME (tyis1, tyis2, teis1, teis2, utyvs1, utyvs2, utevs1, utevs2) =
find_equality_instantiations ote1 ote2 oteivs1 oteivs2 otyivs1 otyivs2
 in
let val check = Timer.checkCPUTimer cputimer in
let val _ = (print o concat) [Time.toString (#usr check), "\n"] in
1
end end end

val renamed_te1 = subst teis1 (inst tyis1 ote1)
val renamed_te2 = subst teis2 (inst tyis2 ote2)
*)


(* *)
(*
val f = ``f : ('a -> 'k) -> 'b -> ('c # num # 'e) -> 'g # 'h # num # 'b``
val g = ``g : 'a         -> 'b -> 'c              -> 'c # num # 'd # 'e``

val a = ``a : ('a -> 'k)``
val x = ``x : 'a``

val b = ``b : 'b``
val y = ``y : 'b``

val c = ``c : ('c # num # 'e)``
val z = ``z : 'c``

val ote1 = mk_comb (mk_comb (mk_comb (f, a), b), c)
val ote2 = mk_comb (mk_comb (mk_comb (g, x), y), z)
val otyivs1 = type_vars_in_term ote1
val otyivs2 = remove_first_occurrence same_type ``: 'e`` (type_vars_in_term ote2)
val oteivs1 = [f,   b]
val oteivs2 = [  x,   z]

let val cputimer = Timer.startCPUTimer ()
val SOME (tyis1, tyis2, teis1, teis2, utyvs1, utyvs2, utevs1, utevs2) =
find_equality_instantiations ote1 ote2 oteivs1 oteivs2 otyivs1 otyivs2
 in
let val check = Timer.checkCPUTimer cputimer in
let val _ = (print o concat) [Time.toString (#usr check), "\n"] in
1
end end end

val renamed_te1 = subst teis1 (inst tyis1 ote1)
val renamed_te2 = subst teis2 (inst tyis2 ote2)
*)

(*******************************************************************************)
(*******************************************************************************)
(*******************************************************************************)
(*END OF TEST CASES FOR TERM INSTANTIATIONS*************************************)
(*******************************************************************************)
(*******************************************************************************)
(*******************************************************************************)









(* Test case
val ([assumption], t) = top_goal ()

val thm = (SPEC_ALL o ASSUME) assumption
val t = concl thm
val ityvs = [] : Type.hol_type list
val itevs = (#1 o strip_forall) assumption

val target_term = (#1 o dest_imp o #2 o strip_forall o concl) boolTheory.EQ_EXT
val target_ityvs = type_vars_in_term target_term
val target_itevs = (#1 o strip_forall o concl) boolTheory.EQ_EXT
*)

(* Test case:
val t = “P (a : 'f) (b : 'g) (c : 'h) (d : 'i) (e : 'j) : bool”
val ityvs = [] : Type.hol_type list
val itevs = [“(a : 'f)”, “(b : 'g)”, “(c : 'h)”, “(d : 'i)”, “(e : 'j)”]

val target_term = “!(u : 'a) (v : 'b) (w : 'c). P u v w (x : 'd) (y : 'e)”
val target_ityvs = type_vars_in_term target_term
val target_itevs = [“(x : 'd)”, “(y : 'e)”]

val invalid_tyrs = []
val invalid_ters = []
*)
(*
    let val (target_qvs, target_term_unquantified) = strip_forall target_term in
    let val instantiation =
            find_equality_instantiations invalid_tyrs invalid_ters t target_term_unquantified itevs target_itevs ityvs target_ityvs in
      if isSome instantiation then
        let val (tyis1, tyis2, teis1, teis2, utyvs, utevs) = valOf instantiation in
        let val tyi_target_qvs = map (inst tyis2) target_qvs in
        let fun remove_qis ({redex = v, residue = i}, (teis1, qutevs)) = (* Remove instantiations to quantified target variables. *)
              if exists (same_term i) tyi_target_qvs then                (* Instantiated to quantified variable. *)
                (teis1, (i, v)::qutevs)
              else                                                       (* Instantiated to unquantified variable. *)
                ({redex = v, residue = i}::teis1, qutevs) in
        let val (teis1, qutevs) = foldl remove_qis ([], []) teis1 in
        let val utevs = filter (fn utev => all (fn (i, qutev) => not_same_term utev qutev) qutevs) utevs
            val sorted_qutevs = map (fn qv => (#2 o valOf) (List.find (fn (i, v) => same_term qv i) qutevs)) tyi_target_qvs in
          SOME (tyis1, tyis2, teis1, teis2, utevs, utyvs, sorted_qutevs, target_term_unquantified)
        end end end end end
      else
        NONE
    end end
*)
  (* Algorithm for handling target terms of the form !X. P X:
   * If the source theorem is universally quantified, and the target is
   * universally quantified, then it may be possible to instantiate the source
   * theorem and the target to become equal, by generalizing some instantiable
   * variables of the source theorem (which appears as unquantified).
   *
   * Correctness:
   * 1. Source theorem has instantiable variables, and can be made equal to the
   *    target, meaning that all instantiable variables are instantiated to
   *    values (including the quantified variables of the target) or
   *    uninstantiated.
   * 2. The instantiable variables instantiated to quantified variables of the
   *    target shall be sorted first so that the source can be quantified with
   *    the quantified variables of the source and the target occurring in the
   *    same order to make the terms equal.
   * 3. Finally the source and the target are quantified, making them equal.
   *
   * Returns equality theorem, type and term instantiations and uninstantiated
   * variables to make the source term equal to the target term, if possible.
   *
   * Inputs:
   * @target_term: Target term.
   * @thm: Unquantified theorem whose conclusion is to become the target term.
   * @target_ityvs: Instantiable type variables of the target term.
   * @ityvs: Instantiable/Quantified term variables of the current theorem @thm.
   * @target_itevs: Instantiable type variables of the target term.
   * @itevs: Instantiable/Quantified type variables of the current theorem @thm.
   *
   * Outputs, if the right handside of eq_thm can be made equal to target_term:
   * -thm: Type and term instantiated theorem whose conclusion is the target term
   *  if the target term is type and term variable instantiated.
   * -tyis2, teis2: Type and term instantiations to instantiate the target term
   *  to the conclusion of thm.
   * -utyvs, utevs: Instantiable type and term variables of thm, that were not
   *  instantiated.
   *)
(*
  fun has_final_equality invalid_tyrs invalid_ters target_term thm target_ityvs ityvs target_itevs itevs =
    let val t = concl thm
        val (target_qvs, target_term_unquantified) = strip_forall target_term in
    let val instantiation =
           find_equality_instantiations invalid_tyrs invalid_ters t target_term_unquantified itevs target_itevs ityvs target_ityvs in
      if isSome instantiation then
        let val (tyis1, tyis2, teis1, teis2, utyvs, utevs) = valOf instantiation in
        let val tyi_target_qvs = map (inst tyis2) target_qvs in
        let fun remove_qis ({redex = v, residue = i}, (teis1, qutevs)) = (* Remove instantiations to quantified target variables. *)
              if exists (same_term i) tyi_target_qvs then                (* Instantiated to quantified variable. *)
                (teis1, (i, v)::qutevs)
              else                                                       (* Instantiated to unquantified variable. *)
                ({redex = v, residue = i}::teis1, qutevs) in
        let val (teis1, qutevs) = foldl remove_qis ([], []) teis1 in
        let val utevs = filter (fn utev => all (fn (i, qutev) => not_same_term utev qutev) qutevs) utevs
            val sorted_qutevs = map (fn qv => (#2 o valOf) (List.find (fn (i, v) => same_term qv i) qutevs)) tyi_target_qvs in

          SOME (GENL sorted_qutevs (INST teis1 (INST_TYPE tyis1 thm)), tyis2, teis2, utyvs, utevs)
        end end end end end
      else
        NONE
    end end
*)
  (* thm is unquantified. *)
  fun has_final_equality invalid_tyrs invalid_ters target_term thm target_ityvs ityvs target_itevs itevs =
    let val t = concl thm
        val (target_qvs, target_term_unquantified) = strip_forall target_term in
    let val instantiation = find_equality_instantiations invalid_tyrs invalid_ters t target_term_unquantified itevs target_itevs ityvs target_ityvs in
      if isSome instantiation then
        let val (tyis1, tyis2, teis1, teis2, utyvs, utevs) = valOf instantiation in
        let val tyi_target_qvs = map (inst tyis2) target_qvs in
        let fun remove_qis ({redex = v, residue = i}, (teis1, qutevs)) = (* Function to remove instantiations to quantified target variables. *)
              if exists (same_term i) tyi_target_qvs then                (* Instantiated to quantified variable. *)
                (teis1, (i, v)::qutevs)
              else                                                       (* Instantiated to unquantified variable. *)
                ({redex = v, residue = i}::teis1, qutevs) in
        let val (teis1, qutevs) = foldl remove_qis ([], []) teis1 in     (* Removes instantiations to quantified target variables. *)
        let val utevs = filter (fn utev => all (fn (i, qutev) => not_same_term utev qutev) qutevs) utevs
            val sorted_qutevs = map (fn qv => (#2 o valOf) (List.find (fn (i, v) => same_term qv i) qutevs)) tyi_target_qvs in
          SOME (GENL sorted_qutevs (INST teis1 (INST_TYPE tyis1 thm)), tyis2, teis2, utyvs, utevs)
        end end end end end

      else if is_eq target_term andalso (is_eq o concl) thm then (* If both the target and the current theorem are equations, then they may be identical if the theorem is reflected. *)
        let val (l, r) = dest_eq t in
        let val reflected_t = mk_eq (r, l) in
        let val instantiation = find_equality_instantiations invalid_tyrs invalid_ters reflected_t target_term_unquantified itevs target_itevs ityvs target_ityvs in

          if isSome instantiation then
            let val (tyis1, tyis2, teis1, teis2, utyvs, utevs) = valOf instantiation in
            let val tyi_target_qvs = map (inst tyis2) target_qvs in
            let fun remove_qis ({redex = v, residue = i}, (teis1, qutevs)) = (* Function to remove instantiations to quantified target variables. *)
                  if exists (same_term i) tyi_target_qvs then                (* Instantiated to quantified variable. *)
                    (teis1, (i, v)::qutevs)
                  else                                                       (* Instantiated to unquantified variable. *)
                    ({redex = v, residue = i}::teis1, qutevs) in
            let val (teis1, qutevs) = foldl remove_qis ([], []) teis1 in     (* Removes instantiations to quantified target variables. *)
            let val utevs = filter (fn utev => all (fn (i, qutev) => not_same_term utev qutev) qutevs) utevs
                val sorted_qutevs = map (fn qv => (#2 o valOf) (List.find (fn (i, v) => same_term qv i) qutevs)) tyi_target_qvs in

              SOME (GENL sorted_qutevs (SYM (INST teis1 (INST_TYPE tyis1 thm))), tyis2, teis2, utyvs, utevs) (* Reflect the theorem. *)
            end end end end end        
          else
            NONE
        end end end
      else
        NONE
    end end








(*
  fun has_final_equality invalid_tyrs invalid_ters target_term thm target_ityvs ityvs target_itevs itevs =
    let val t = concl thm in
      case find_equality_instantiations invalid_tyrs invalid_ters t target_term itevs target_itevs ityvs target_ityvs of
        NONE => NONE
      | SOME (tyis1, tyis2, teis1, teis2, utyvs, utevs) =>
        SOME (INST teis1 (INST_TYPE tyis1 thm), tyis2, teis2, utyvs, utevs)
    end
*)

  (* Returns theorem and uninstantiated variables in case there is a theorem
   * whose conclusion can be made equal to the target term.
   *)
  fun has_final_equalities invalid_tyrs invalid_ters target_term target_ityvs target_itevs [] = NONE
    | has_final_equalities invalid_tyrs invalid_ters target_term target_ityvs target_itevs ((thm, ityvs, itevs)::thms) =
      case has_final_equality invalid_tyrs invalid_ters target_term thm target_ityvs ityvs target_itevs itevs of
        NONE => has_final_equalities invalid_tyrs invalid_ters target_term target_ityvs target_itevs thms
      | SOME (thm, target_tyis, target_teis, utyvs, utevs) =>
        SOME (thm, target_tyis, target_teis, utyvs, utevs)

  (* Checks if the conclusion of any theorem and the target term can be
   * instantiated to become the same term.
   *)
  fun has_final_equalitiess invalid_tyrs invalid_ters target_term target_ityvs target_itevs [] = NONE
    | has_final_equalitiess invalid_tyrs invalid_ters target_term target_ityvs target_itevs ((thms, rw_thms)::rws) =
      case has_final_equalities invalid_tyrs invalid_ters target_term target_itevs target_ityvs thms of
        NONE => has_final_equalitiess invalid_tyrs invalid_ters target_term target_ityvs target_itevs rws
      | SOME (thm, target_tyis, target_teis, utyvs, utevs) => SOME (thm, target_tyis, target_teis, utyvs, utevs)






  fun no_ityvs_variable ityvs variable =
    let val tyvs = type_vars_in_term variable in
    let val no_ityvs = filter (fn ityv => all (not_same_type ityv) tyvs) ityvs in
      no_ityvs
    end end

  fun no_ityvs_constant ityvs constant =
    let val tyvs = type_vars_in_term constant in
    let val no_ityvs = filter (fn ityv => all (not_same_type ityv) tyvs) ityvs in
      no_ityvs
    end end

  fun no_ityvs_application no_ityvs_f no_ityvs_a =
    filter (fn ityv => exists (same_type ityv) no_ityvs_a) no_ityvs_f (* Intersection. *)

  (* Remove type variables occurring in bounded variable from recursive list.
   *)
  fun no_ityvs_abstraction bvar no_ityvs_body =
    let val tyvs_bvar = type_vars_in_term bvar in
    let val no_ityvs_abstraction = filter (fn ityv => all (not_same_type ityv) tyvs_bvar) no_ityvs_body in
      no_ityvs_abstraction
    end end

  (* -If not instantiable variable: All instantiable variables
   * -If     instantiable variable: All instantiable variables except the current
   *  node variable.
   *)
  fun no_itevs_variable variable [] = []
    | no_itevs_variable variable (itev::itevs) =
      if same_term variable itev then
        itevs
      else
        itev::(no_itevs_variable variable itevs)

  (* All instantiable variables. *)
  fun no_itevs_constant itevs = itevs

  (* Intersection of recursive lists.
   *)
  fun no_itevs_application no_itevs_f no_itevs_a = filter (fn itev => exists (same_term itev) no_itevs_a) no_itevs_f

  (* -If bounded variable is instantiable (variables of the same name in the same
   *  term, bounding variable and occurrence of the variable, has the same type):
   *  Add the bounded variable to the recursive list.
   * -Otherwise: Recursive list.
   *)
  fun no_itevs_abstraction itevs bvar no_itevs_body =
    if exists (same_term bvar) itevs then
      union_lists same_term [bvar] no_itevs_body
    else
      no_itevs_body

  (* AP_TERM: term -> thm -> thm, where A |- a = a' is a returned value of the
   * right subtree (the argument a) and f is the left subtree.
   *   A |- a = a'
   * ---------------AP_TERM (f)
   * A |- f a = f a'
   *
   * AP_THM: thm -> term -> thm, where A |- f = f' is a returned value of the
   * left subtree (the function f) and a is the right subtree.
   *    A |- f = f'
   * ----------------AP_THM (a)
   * A |- f a = f' a
   *)
  fun subterm_eqs_app subterm_eqs invalid_tyrs invalid_ters t l rw_thm ityvs ityvs_rw itevs itevs_rw =
    let val (f, a) = dest_comb t in
    let val (f_thms_rec, no_ityvs_f, no_itevs_f) = subterm_eqs invalid_tyrs invalid_ters f l rw_thm ityvs ityvs_rw itevs itevs_rw
        val (a_thms_rec, no_ityvs_a, no_itevs_a) = subterm_eqs invalid_tyrs invalid_ters a l rw_thm ityvs ityvs_rw itevs itevs_rw in
    let val f_thms = map (fn (thm, tyis, rw_tyis, teis, utyvs, utevs) =>
                             (AP_THM thm (subst teis (inst tyis a)), tyis, rw_tyis, teis, utyvs, utevs)) f_thms_rec
        val a_thms = map (fn (thm, tyis, rw_tyis, teis, utyvs, utevs) =>
                             (AP_TERM (subst teis (inst tyis f)) thm, tyis, rw_tyis, teis, utyvs, utevs)) a_thms_rec in
      (f_thms @ a_thms, no_ityvs_application no_ityvs_f no_ityvs_a, no_itevs_application no_itevs_f no_itevs_a)
    end end end

  (* ABS: term -> thm -> thm
   *     A |- l = r
   * ------------------ABS (bvar)
   * A |- \b. l = \b. r
   *)
  fun subterm_eqs_abs subterm_eqs invalid_tyrs invalid_ters t l rw_thm ityvs ityvs_rw itevs itevs_rw =
    let val (bvar, body) = dest_abs t in
    (* bvar no longer instantiable, but parts of the subterm may still be
     * rewritten, motivated by the following example. Subterm equalities with
     * bounded variables allow cases where !x. x + 0 = x to rewrite
     * \x. x + 0 to \x.x.
     *)
    let val itevs = filter (not_same_term bvar) itevs in
    let val (b_thms_rec, no_ityvs_body, no_itevs_body) =
            subterm_eqs invalid_tyrs invalid_ters body l rw_thm ityvs ityvs_rw itevs itevs_rw in
    let val b_thms = map (fn (thm, tyis, rw_tyis, teis, utyvs, utevs) =>
                             (ABS (subst teis (inst tyis bvar)) thm, tyis, rw_tyis, teis, utyvs, utevs)) b_thms_rec in
      (b_thms, no_ityvs_abstraction bvar no_ityvs_body, no_itevs_abstraction itevs bvar no_itevs_body)
    end end end end

  (* Case on variable and constant, application or abstraction.
   *
   * Algorithm for finding instantiable type variables not occurring in the
   * current subterm t:
   * *Base case (variables and constants): All instantiable variables except
   *  those occurring in variable/constant.
   *
   * Algorithm for finding instantiable term variables not occurring in the
   * current subterm t:
   * *Base case:
   *  -variable:
   *   #If not instantiable variable: All instantiable variables
   *   #If     instantiable variable: All instantiable variables except the
   *   current node variable.
   * -constant: All instantiable variables.
   *)
  fun subterm_eqs_case subterm_eqs invalid_tyrs invalid_ters t l rw_thm ityvs ityvs_rw itevs itevs_rw =
    if is_var t orelse is_const t then
      ([], no_ityvs_variable ityvs t, no_itevs_variable t itevs)
    else if is_const t then
      ([], no_ityvs_constant ityvs t, no_itevs_constant itevs)
    else if is_comb t then
      subterm_eqs_app subterm_eqs invalid_tyrs invalid_ters t l rw_thm ityvs ityvs_rw itevs itevs_rw
    else (* is_abs t *)
      subterm_eqs_abs subterm_eqs invalid_tyrs invalid_ters t l rw_thm ityvs ityvs_rw itevs itevs_rw

  (* Add only those not occurring instantiable type variables that are not
   * instantiated as uninstantiated instantiable type variables.
   *)
  fun not_occurring_uninstantiated_type_variables tyis [] = []
    | not_occurring_uninstantiated_type_variables tyis (no_ityv::no_ityvs)=
      let val ityvs_to_add = not_occurring_uninstantiated_type_variables tyis no_ityvs in
        if exists (fn {redex = tyv, residue = _} => same_type no_ityv tyv) tyis then
          ityvs_to_add
        else
          no_ityv::ityvs_to_add
      end

  (* Add only those not occurring instantiable term variables that are not
   * instantiated as uninstantiated instantiable term variables.
   *)
  fun not_occurring_uninstantiated_term_variables tyis teis [] = []
    | not_occurring_uninstantiated_term_variables tyis teis (no_itev::no_itevs) =
      let val itevs_to_add = not_occurring_uninstantiated_term_variables tyis teis no_itevs
          val itev = inst tyis no_itev in
        if exists (fn {redex = tev, residue = _} => same_term itev tev) teis then
          itevs_to_add
        else
          itev::itevs_to_add
      end

  (* Generates all possible subterm instantiations for rewriting the current
   * rewrite theorem with a rewrite equation.
   *
   * @te_r: Right handside of current rewrite theorem to be rewritten.
   * @te_l: Left handside of the rewrite theorem used to rewrite the right
   *  handside of the current rewrite theorem.
   * @ityvs_r: Instantiable type variables of te_r.
   * @ityvs_l: Instantiable term variables of te_l.
   * @itevs_r: Instantiable type variables of te_r.
   * @itevs_l: Instantiable term variables of te_l.
   *
   * Algorithm:
   * Traverse the right handside, ser (subterm equality right handside), to be
   * rewritten of the equality, and if there is possible to make ser and srl
   * (subterm rewrite left handside) equal:
   *
   * 1. Apply the instantiations (including the type instantiations) on ser and
   *    srl to obtain iser and isrl, and the uninstantiated variables of iser and
   *    isrl.
   *
   *    NOTE: Bound variables must not be instantiated nor occur in instantiation
   *    values (unless they are bounded by a binder in the instantiation value).
   *    This is prevented by having unique new variables that represent
   *    instantiable variables, and by find_term_instantiation_variable checking
   *    that the subterms do not contain bounded variables.
   *
   * 2. Find correspondence pairs of uninstantiated variables in iser and isrl.
   *    Traverse iser and isrl in parallel and for each pair of uninstantiated
   *    variables, return a substitution s from the isrl uninstantiated variable
   *    to the iser uninstantiated variable. Since iser and isrl only differ with
   *    respect to uninstantiated variables, iser = isrl[s], and due to the
   *    A |- srl = srr, the following theorem is obtained:
   *
   *    A |- srl[s] = srr[s].
   *
   *    The uninstantiated variables, uv, in A |- srl[s] = srr[s] are the
   *    uninstantiated variables in iser and the remaining uninstantiated
   *    variables of A |- srl = srr (after s).
   *
   *    A |- srl[s] = srr[s] and uv are returned.
   *
   * 3. When returning upwards trough the term tree of ser, The follwoing rules
   *    are applied on each return value (of lists) from the recursive call:
   *    -ABS: term -> thm -> thm
   *         A |- l = r
   *     ------------------ABS (bvar)
   *     A |- \b. l = \b. r
   *
   *    -AP_TERM: term -> thm -> thm, where A |- l = r is a returned value of
   *     the right subtree and f is the left subtree.
   *     A |- l = r
   *     --------------AP_TERM (f)
   *     A |- f l = f r
   *
   *    -AP_THM: thm -> term -> thm, where l = r is a returned value of the left
   *     subtree and a is the right subtree.
   *     A |- l = r
   *     -----------------AP_THM (a)
   *     A |- l a = r a
   *
   * The result is a list of all possible single rewrites of the given right hand
   * side of the equation to rewrite, by means of the given rewrite theorem
   * A |- srl = srr.
   *
   *
   *
   * NOTE:
   * Since find_equality_instantiations only returns uninstantiated type and term
   * variables that actually occur in the terms to be made equal, the
   * uninstantiated variables must be extended with those instantiable variables
   * not occurring in the subterms. Those additional variables not occurring in
   * the subterms are added to the invalid list used for
   * find_equality_instantiations applied on the current term. The type
   * instantiations must be applied on the added instantiable term variables.
   *
   * Algorithm for finding instantiable type variables not occurring in the
   * current subterm t:
   * *Base case (variables and constants): All instantiable variables except
   *  those occurring in variable/constant.
   * *Recursive cases:
   *  -Application: Intersection of recursive lists.
   *  -Abstraction: Remove type variables occurring in bounded variable from
   *   recursive list.
   *
   * Algorithm for finding instantiable term variables not occurring in the
   * current subterm t:
   * *Base case:
   *  -variable:
   *   #If not instantiable variable: All instantiable variables
   *   #If    instantiable variable: All instantiable variables except the
   *    current node variable.
   * -constant: All instantiable variables.
   * *Recursive case:
   *  -Application: Intersection of recursive lists.
   *  -Abstraction:
   *   #If bounded variable is instantiable (must be same type as subterm
   *    occurrences of the variable has same type as bounding variable):
   *    Add the bounded variable to the recursive list.
   *   #Otherwise: Recursive list.
   *)
  fun subterm_eqs invalid_tyrs invalid_ters t l rw_thm ityvs ityvs_rw itevs itevs_rw =
    let val (rw_eq_thms, no_ityvs_t, no_itevs_t) =
            subterm_eqs_case subterm_eqs invalid_tyrs invalid_ters t l rw_thm ityvs ityvs_rw itevs itevs_rw in
            (* Add instantiable variables not occurring in t as invalid
             * names of uninstantiated instantiable variables.
             *)
    let val invalid_tyrs = (map dest_vartype no_ityvs_t) @ invalid_tyrs
        val invalid_ters = (map term_to_string no_itevs_t) @ invalid_ters in
        let val equality_instantiations = find_equality_instantiations invalid_tyrs invalid_ters t l itevs itevs_rw ityvs ityvs_rw in
      if isSome equality_instantiations then
        let val (tyis, rw_tyis, teis, rw_teis, utyvs, utevs) = valOf equality_instantiations in
        let val tyi_rw_thm = INST_TYPE rw_tyis rw_thm in
        let val tei_tyi_rw_thm = INST rw_teis tyi_rw_thm
            val no_ityvs = not_occurring_uninstantiated_type_variables tyis no_ityvs_t
            val no_itevs = not_occurring_uninstantiated_term_variables tyis teis no_itevs_t in
                (* Disjoint lists of uninstantiated variables cause no duplicates. *)
        let val rw_eq_thm = (tei_tyi_rw_thm, tyis, rw_tyis, teis, utyvs @ no_ityvs, utevs @ no_itevs) in
          (rw_eq_thm::rw_eq_thms, no_ityvs_t, no_itevs_t)
        end end end end
      else
        (rw_eq_thms, no_ityvs_t, no_itevs_t)
    end end end









  fun find_vs is_same variables_of [] = []
    | find_vs is_same variables_of (term::terms) =
      let val tevs_rec = find_vs is_same variables_of terms in
      let val tevs = variables_of term in
        union_lists is_same tevs tevs_rec
      end end

  (* Returns the set of type variables occurring in a list of terms. *)
  fun find_tyvs terms = find_vs same_type type_vars_in_term terms

  (* Returns the set of free term variables occurring in a list of terms. *)
  fun find_tevs terms = free_varsl terms

  fun union_listss is_same [] = []
    | union_listss is_same (l::ls) =
      let val unioned_listss = union_listss is_same ls in
      let val unioned_lists = union_lists is_same l unioned_listss in
        unioned_lists
      end end

  fun split_variables thm =
    let val (hyps, t) = dest_thm thm in
    let val tevs1 = free_vars t
        val hyp_tevs1 = find_tevs hyps
        val tyvs1 = type_vars_in_term t
        val hyp_tyvs1 = find_tyvs hyps in
      (t, tevs1, hyp_tevs1, tyvs1, hyp_tyvs1)
    end end

  (* Instantiable term/type variables OCCURING in thm.
   *)
  fun occurring_ivs itevs ityvs tevs1 tyvs1 =
    let val itevs1 = filter (fn tev => exists (same_term tev) itevs) tevs1
        val ityvs1 = filter (fn tyv => exists (same_type tyv) ityvs) tyvs1 in
      (itevs1, ityvs1)
    end

  (* Uninstantiable term/type variables occurring in thm. same_term can be used
   * in contrast to string equality as variables originating from the same
   * theorem with same name has the same type.
   *)
  fun uninstantiable_variables_thm itevs tevs1 hyp_tevs1 ityvs tyvs1 hyp_tyvs1 =
    let val utevs1 = filter (fn tev => all (not_same_term tev) itevs) tevs1                                      (* TEB1. *)
        val utevs_hyp1 = filter (fn tev => all (not_same_term tev) itevs) hyp_tevs1
        val utyvs1 = filter (fn tyv => all (not_same_type tyv) ityvs) tyvs1                                      (* TYB1. *)
        val utyvs_hyp1 = filter (fn tyv => all (not_same_type tyv) ityvs) hyp_tyvs1 in                           (* TYA1. *)
      (utevs1, utevs_hyp1, utyvs1, utyvs_hyp1)
    end

  (* Given a theorem A |- r, thm, a rewrite theorem
   * B |- r[tyis,teis] = t[tyis,teis], rw_thm, and uninstantiated type and term
   * variables, utyvs and utevs, returns
   * (A u B)[tyis_eq,teis_eq] |- t[tyis_eq,teis_eq], and the remaining
   * uninstantiated type and term variables of that theorem.
   *
   * NOTE regarding uninstantiated variables:
   * -The uninstantiated variables in the conclusion of the theorem are retained
   *  as only they will occur in the theorem.
   * -The uninstantiated variables not occurring in the subterms, but do occur in
   *  the conclusion of the complete term, are added to the list of uninstantiated variables.
   *
   *  To avoid uninstantiable variables not occurring in the term, the given
   *  lists with instantiable variables should only contain variables occurring
   * in the terms.
   *)
  fun rewrite_thm thm ityvs_r_only2 itevs_r_only2 (tei_tyi_rw_thm, new_tyis, rw_tyis, new_teis, ityvs, itevs) =
    let val tyi_thm = INST_TYPE new_tyis thm 
        val itevs_r_only2 = map (inst rw_tyis) itevs_r_only2 in
    let val tei_tyi_thm = INST new_teis tyi_thm in
    let val thm = EQ_MP tei_tyi_rw_thm tei_tyi_thm in
    let val tyvs = (type_vars_in_term o concl) thm
        val tevs = (free_vars o concl) thm in

            (* Keep only instantiable variables occurring in the theorem, as some
             * variables may only occur in the left hand side of the rewrite
             * theorem. No duplicates: lists disjoint.
             *)
    let val ityvs = (filter (fn ityv => exists (same_type ityv) tyvs) ityvs) @ ityvs_r_only2
        val itevs = (filter (fn itev => exists (same_term itev) tevs) itevs) @ itevs_r_only2 in
      (thm, ityvs, itevs)
    end end end end end

  (* Rewrites the right handside of eq_thm with the right handside of rw_thm,
   * after performing suitable instantiations of instantiable type and term
   * variables of eq_thm and rw_thm.
   *
   * Inputs:
   * @invalid_tyrs, invalid_ters: Invalid type and term variable names of
   *  uninstantiated variables for the expanded thm resulting from using rw_thm
   *  to rewrite thm.
   * @thm: Unquantified theorem.
   * @itevs: Instantiable term variables in thm.
   * @ityvs: Instantiable type variables in thm.
   * @rw_thm: Unquantified equational theorem.
   * @invalid_tyvs2, @invalid_tevs2: Uninstantiated type and term variable names
   *  occurring free among the hypotheses and the conclusion of @rw_thm, and
   *  instantiable type and term variables occurring only on the right handside
   *  of the conclusion of @rw_thm.
   * @l_ityvs2, @l_itevs2: Instantiable type and term variables occurring in the
   *  left handside of the conclusion of @rw_thm.
   * @ityvs_r_only2, @itevs_r_only2: Instantiable type and term variables
   *  occurring only in the right handside of the conclusion of @rw_thm.
   *
   * Outputs:
   * -thm: @thm replaced by the right handside of rw_thm, after instantiating thm
   *  and rw_thm such that the instantiated thm and the left hand sides are equal.
   * -itevs: Instantiable term variables occurring in the output eq_thm.
   * -ityvs: Instantiable type variables occurring in the output eq_thm.
   *
   * NOTE:
   * Instantiable variables occurring only in the right handside of rw are
   * illegal names for uninstantiated variables to make the left handside equal
   * to the conclusion of thm, to avoid name clashing (which causes two different
   * instantiable variables to become the same, which in turn causes unnecessary
   * limitations). Therefore their names must be added to the given lists
   * invalid_tyrs and invalid_ters.
   *
   * Invalid names for uninstantiated term variables:
   * -TEA1, TEA2: Free variables of hypothesis of thm and rw_thm.
   * -TEB1, TEB2: Uninstantiable variables occuring in the conclusions of thm and
   *  rw_thm.
   * -TEC1, TEC2: Instantiable variables occuring only in the right handside of
   *  rw_thm.
   *
   * Invalid names for uninstantiated type variables:
   * -TYA1, TYA2: Uninstantiable variables occurring in the hypotheses of thm and
   *  rw_thm.
   * -TYB1, TYB2: Uninstantiable variables occurring in the conclusion of thm and
   *  rw_thm.
   * -TYC1, TYC2: Instantiable variables occuring only in the right handside of
   *  rw.
   *)
  fun rewrite_thms invalid_tyrs invalid_ters thm itevs ityvs
                   (rw_thm, invalid_tyvs2, invalid_tevs2, l_ityvs2, l_itevs2, ityvs_r_only2, itevs_r_only2) =
            (* Occurring variables. *)
    let val (t, tevs1, hyp_tevs1, tyvs1, hyp_tyvs1) = split_variables thm in

            (* Occurring instantiable variables in thm. *)
    let val (itevs1, ityvs1) = occurring_ivs itevs ityvs tevs1 tyvs1

            (* Uninstantiable variables. *)
        val (utevs1, utevs_hyp1, utyvs1, utyvs_hyp1) = uninstantiable_variables_thm itevs tevs1 hyp_tevs1 ityvs tyvs1 hyp_tyvs1 in

    let val invalid_tyvs1 = map dest_vartype (union_listss same_type [utyvs_hyp1, utyvs1])
        val invalid_tevs1 = union_listss equal (map (map term_to_string) [utevs_hyp1, utevs1]) in
    let val invalid_tyrs = union_listss equal [invalid_tyrs, invalid_tyvs1, invalid_tyvs2]
        val invalid_ters = union_listss equal [invalid_ters, invalid_tevs1, invalid_tevs2] in
    let val (ityvs_rw, itevs_rw) = (l_ityvs2, l_itevs2)
        val l = ((lhs o concl) rw_thm) in

    let val rw_thms = #1 (subterm_eqs invalid_tyrs invalid_ters t l rw_thm ityvs ityvs_rw itevs itevs_rw) in

    let val rewritten_thms = map (rewrite_thm thm ityvs_r_only2 itevs_r_only2) rw_thms in
      rewritten_thms
    end end end end end end end

(* Test cases
val invalid_tyrs = []
val invalid_ters = []
val thm = mk_thm ([], ``g (x1 : 'a) (x2 : 'b) : bool``)
val rw_thm = mk_thm ([], ``g (y1 : 'c) (y2 : 'd) : bool = h (y2 : 'd) (y3 : 'e)``)
val ityvs = [``: 'a``, ``: 'b``]
val rw_ityvs = [``: 'c``, ``: 'd``]
val itevs = [``x1 : 'a``, ``x2 : 'b``]
val rw_itevs = [``y1 : 'c``, ``y2 : 'd``, ``y3 : 'e``]
rewrite_thms invalid_tyrs invalid_ters thm rw_thm itevs rw_itevs ityvs rw_ityvs

val invalid_tyrs = []
val invalid_ters = []
val thm = mk_thm ([], ``j (g (x2 : 'b) (x3 : 'c) : 'a) : bool``)
val rw_thm = mk_thm ([], ``g (y2 : 'b) (y3 : 'c) : 'g = h (y3 : 'c) (y5 : 'a)``)
val ityvs = [``: 'a``, ``: 'b``, ``: 'c``]
val rw_ityvs = [``: 'b``, ``: 'c``, ``: 'g``]
val itevs = [``(x2 : 'b)``, ``(x3 : 'c)``]
val rw_itevs = [``(y2 : 'b)``, ``y3 : 'c``, ``(y5 : 'a)``]
rewrite_thms invalid_tyrs invalid_ters thm rw_thm itevs rw_itevs ityvs rw_ityvs

val invalid_tyrs = []
val invalid_ters = []
val thm = mk_thm ([], ``= j (x3 : 'c)``)
val rw_thm = mk_thm ([], ``y3 : 'c = h (y3 : 'c) (y5 : 'e)``)
val itevs = [``x3 : 'c``]
val rw_itevs = [``y3 : 'c``, ``y5 : 'e``]
val ityvs = [``: 'a``, ``: 'b``, ``: 'c``]
val rw_ityvs = [``: 'c``, ``: 'e``]
rewrite_thms invalid_tyrs invalid_ters thm rw_thm itevs rw_itevs ityvs rw_ityvs

val invalid_tyrs = []
val invalid_ters = []
val thm = mk_thm ([], ``j (x3 : 'c)``)
val rw_thm = mk_thm ([], ``y3 : 'h = h (y4 : 'h) (y5 : 'e)``)
val itevs = [``x3 : 'c``]
val rw_itevs = [``y3 : 'c``, ``y5 : 'e``]
val ityvs = [``: 'a``, ``: 'b``, ``: 'c``]
val rw_ityvs = [``: 'e``]
rewrite_thms invalid_tyrs invalid_ters thm rw_thm itevs rw_itevs ityvs rw_ityvs
 *)





  datatype target_theorem =
    (* Constructor saying that target is reached. *)
    TARGET_REACHED of Thm.thm *
                      {redex : Type.hol_type, residue : Type.hol_type} list *
                      {redex : Term.term, residue : Term.term} list *
                      Type.hol_type list *
                      Term.term list |
    (* Constructor saying that target is not reached with remaining theorems. *)
    THEOREMS of (Thm.thm * Type.hol_type list * Term.term list) list

  fun rewrite_thmss invalid_tyrs invalid_ters target_term target_ityvs target_itevs thm ityvs itevs [           ] = THEOREMS []
    | rewrite_thmss invalid_tyrs invalid_ters target_term target_ityvs target_itevs thm ityvs itevs (rw::rw_thms) =
      let val rewritten_thms = rewrite_thms invalid_tyrs invalid_ters thm itevs ityvs rw in
        case has_final_equalities invalid_tyrs invalid_ters target_term target_ityvs target_itevs rewritten_thms of
          NONE => (
          case rewrite_thmss invalid_tyrs invalid_ters target_term target_ityvs target_itevs thm ityvs itevs rw_thms of
            TARGET_REACHED (thm, target_tyis, target_teis, utyvs, utevs) =>
            TARGET_REACHED (thm, target_tyis, target_teis, utyvs, utevs)
          | THEOREMS rewritten_thmss =>
            THEOREMS (rewritten_thms @ rewritten_thmss))
        | SOME (thm, target_tyis, target_teis, utyvs, utevs) =>
          TARGET_REACHED (thm, target_tyis, target_teis, utyvs, utevs)
      end

  (* Returns expanded equality theorems if the target is not reached, or one
   * equality theorem if the target is reached.
   *
   * Algorithm: First expand and check termination condition. Checking the
   * termination condition immediately after rewrite minimizes redundant
   * computation.
   *)
  fun rewrite_thmsss invalid_tyrs invalid_ters target_term target_ityvs target_itevs [] rw_thms = THEOREMS []
    | rewrite_thmsss invalid_tyrs invalid_ters target_term target_ityvs target_itevs ((thm, ityvs, itevs)::thms) rw_thms =
      case rewrite_thmss invalid_tyrs invalid_ters target_term target_ityvs target_itevs thm ityvs itevs rw_thms of
        TARGET_REACHED (thm, target_tyis, target_teis, utyvs, utevs) =>
        TARGET_REACHED (thm, target_tyis, target_teis, utyvs, utevs)
      | THEOREMS rewritten_thmss =>
        case rewrite_thmsss invalid_tyrs invalid_ters target_term target_ityvs target_itevs thms rw_thms of
          TARGET_REACHED (thm, target_tyis, target_teis, utyvs, utevs) =>
          TARGET_REACHED (thm, target_tyis, target_teis, utyvs, utevs)
        | THEOREMS rewritten_thmsss =>
          THEOREMS (rewritten_thmss @ rewritten_thmsss)

  (* Breadth-first-search algorithm for finding a rewrite theorem of the form.
   *
   * @target_term: Target term.
   * @target_tyivs: Instantiable type variables of the target term.
   * @target_itevs: Instantiable term variables of the target term.
   * @rws: List of pairs of theorems and rewrite theorems, with instantiable type
   *  and term variables, where the rewrite theorems can be used to rewrite the
   *  conclusions of the theorems such that the conclusions of the theorems
   *  become the target term if the target term and the theorems are instantiated
   *  appropriately.
   *
   * NOTE: Having instantiable type and term variables that does not occur in
   * the terms has no effect, as they do not affect the instantiations, nor the
   * uninstantiated variables (including their names).
   *
   * Design:
   * If it is possible to rewrite F Y to T X by means of the equations, then it
   * is possible to rewrite F Y to intermediate formulas, step by step, applying
   * one equation at a time: F I Y' -> eqi Fi -> eqi+1 ... -> eqj Fj -> T J X'.
   *
   * Such a sequence of rewrites will be found by applying each equation on all
   * possible subterms of the current formula Fk, to generate all possible Fk+1.
   *
   * By having all formulas Fk on a queue with the rewritten results of each
   * appended to the tail, until a result of Fk = T J X' is encountered, a
   * breadth first search is made, which will reach the result if possible.
   *)
  fun search_thm invalid_tyrs invalid_ters target_term target_ityvs target_itevs [] = NONE
    | search_thm invalid_tyrs invalid_ters target_term target_ityvs target_itevs ((source_thms, rw_thms)::rws) =
      case rewrite_thmsss invalid_tyrs invalid_ters target_term target_ityvs target_itevs source_thms rw_thms of
        TARGET_REACHED (thm, target_tyis, target_teis, utyvs, utevs) =>
        SOME (thm, target_tyis, target_teis, utyvs, utevs)
      | THEOREMS rewritten_thmsss =>
        search_thm invalid_tyrs invalid_ters target_term target_ityvs target_itevs (rws @ [(rewritten_thmsss, rw_thms)])

  (* BFS to find target, implemented by means of a queue of "rewrite states"
   * (see @rws).
   *
   * Inputs:
   * @invalid_tyrs, invalid_ters: Two lists of invalid uninstantiated type and
   *  term variable names (strings; all type variables and free term variables
   *  among the assumptions and the conclusion of the goal).
   * @target_term: Target term.
   * @target_ityvs, target_itevs: Instantiable type and term variables of the
   *  target term.
   * @rw_combs: List of pairs
   *  [([(source_thm, ityvs, itevs)],
   *    [(rw_thm, properties of variables and invalid names...)]
   *   )
   *  ]:
   *  -List of source theorems whose conclusion shall be made equal to the target
   *   term, together with their instantiable type and term variables.
   *  -List of rewrite theorems with instantiable type and term variables that
   *   can be used to rewrite the conclusion of the source theorems and invalid
   *   names for uninstantiated variables.
   *
   * Outputs:
   * -thm: Theorem A |- target_term[target_tyis,target_teis].
   * -target_tyis, target_teis: Type and term instantiations to apply on
   *  target_term to make it the conclusion of the returned theorem.
   * -utyvs: Instantiable variables of thm.
   * -utevs: Instantiable variables of thm.
   *)
  fun find_target_thm invalid_tyrs invalid_ters target_term target_ityvs target_itevs rw_combs =
    case has_final_equalitiess invalid_tyrs invalid_ters target_term target_itevs target_ityvs rw_combs of
      SOME (thm, target_tyis, target_teis, utyvs, utevs) =>
      SOME (thm, target_tyis, target_teis, utyvs, utevs)
    | NONE =>
         case search_thm invalid_tyrs invalid_ters target_term target_ityvs target_itevs rw_combs of
          NONE => NONE
        | SOME (thm, target_tyis, target_teis, utyvs, utevs) =>
          SOME (thm, target_tyis, target_teis, utyvs, utevs)

(* Test case not requiring rewrite theorems:
val source_term = ``f (x : 'a) (y (z : 'b) : 'c) : bool``
val target_term = ``f (x : 'e) (y : 'f) : bool``
val source_ityvs = []
val target_ityvs = [``: 'e``, ``: 'f``]
val source_itevs = []
val target_itevs = [``y : 'f``]
val invalid_tyrs = []
val invalid_ters = []
val rw_thms = [((SPEC_ALL o ASSUME) ``!x : 'b -> 'c. x = a``, [] : hol_type list, [``x : 'b -> 'c``]),
               ((SPEC_ALL o ASSUME) ``!b : 'c. a (z : 'b) : 'c = b``, [], [``b : 'c``])]
val rws = [([(ASSUME source_term, [] : hol_type list, [] : term list)], rw_thms)]

val SOME (thm, target_tyis, target_teis, utyvs, utevs) = find_target_thm invalid_tyrs invalid_ters target_term target_ityvs target_itevs rws

Term.compare (concl thm, subst target_teis (inst target_tyis target_term))
*)

(* Test case requiring rewrite theorems:
val source_term = ``f (x : 'a) (y (z : 'b) : 'c) : bool``
val target_term = ``f (x : 'e) (y : 'f) : bool``
val source_ityvs = [] : hol_type list
val target_ityvs = [``: 'e``, ``: 'f``]
val source_itevs = [``y : 'b -> 'c``]
val target_itevs = []
val invalid_tyrs = []
val invalid_ters = []
val rw_thms = [((SPEC_ALL o ASSUME) ``!x : 'b -> 'c. x = a``, [] : hol_type list, [``x : 'b -> 'c``]),
               ((SPEC_ALL o ASSUME) ``!b : 'c. a (z : 'b) : 'c = b``, [], [``b : 'c``])]
val rws = [([(ASSUME source_term, source_ityvs, source_itevs)], rw_thms)]

val SOME (thm, target_tyis, target_teis, utyvs, utevs) = find_target_thm invalid_tyrs invalid_ters target_term target_ityvs target_itevs rws

Term.compare (concl thm, subst target_teis (inst target_tyis target_term))
*)





  (* NOTE: Type variables of assumptions of a goal are not instantiable.
   * Therefore the middle component is the empty list.
   *)
  fun extract_asm_ivs [] = []
    | extract_asm_ivs (asm::asms) =
      let val extracted_asms_ivs = extract_asm_ivs asms
          val itevs = (#1 o strip_forall) asm in
      let val thm = (SPEC_ALL o ASSUME) asm in
        (thm, [], itevs)::extracted_asms_ivs
      end end

  fun split_eq_variables rw_thm =
    let val (hyps, con) = dest_thm rw_thm in
    let val (l, r) = dest_eq con in
    let val l_tevs2 = free_vars l
        val r_tevs2 = free_vars r
        val hyp_tevs2 = find_tevs hyps (* TEA1/TEA2. *)
        val l_tyvs2 = type_vars_in_term l
        val r_tyvs2 = type_vars_in_term r
        val hyp_tyvs2 = find_tyvs hyps in
      (l_tevs2, r_tevs2, hyp_tevs2, l_tyvs2, r_tyvs2, hyp_tyvs2)
    end end end

  (* Instantiable term/type variables OCCURING in the left/right handsides of
   * rw_thm.
   *)
  fun occurring_ivs_l_r rw_itevs rw_ityvs l_tyvs2 r_tyvs2 l_tevs2 r_tevs2 =
    let val l_ityvs2 = filter (fn tyv => exists (same_type tyv) rw_ityvs) l_tyvs2
        val r_ityvs2 = filter (fn tyv => exists (same_type tyv) rw_ityvs) r_tyvs2
        val l_itevs2 = filter (fn tev => exists (same_term tev) rw_itevs) l_tevs2
        val r_itevs2 = filter (fn tev => exists (same_term tev) rw_itevs) r_tevs2 in
      (l_ityvs2, r_ityvs2, l_itevs2, r_itevs2)
    end

  (* Instantiable term/type variables of rw_thm that occur only in the left/right
   * handsides of rw_thm.
   *)
  fun ivs_only_l_r l_ityvs2 r_ityvs2 l_tyvs2 r_tyvs2 rw_ityvs l_itevs2 r_itevs2 l_tevs2 r_tevs2 rw_itevs =
    let val ityvs_l_only2 = filter (fn tyv => all (not_same_type tyv) r_ityvs2 andalso exists (same_type tyv) l_tyvs2) rw_ityvs
        val ityvs_r_only2 = filter (fn tyv => all (not_same_type tyv) l_ityvs2 andalso exists (same_type tyv) r_tyvs2) rw_ityvs
        val itevs_l_only2 = filter (fn tev => all (not_same_term tev) r_itevs2 andalso exists (same_term tev) l_tevs2) rw_itevs
        val itevs_r_only2 = filter (fn tev => all (not_same_term tev) l_itevs2 andalso exists (same_term tev) r_tevs2) rw_itevs in
      (ityvs_l_only2, ityvs_r_only2, itevs_l_only2, itevs_r_only2)
    end

  (* Uninstantiable term/type variables occurring in rw_thm. same_term can be
   * used in contrast to string equality as variables originating from the
   * same theorem with the same name has the same type.
   *)
  fun uninstantiable_variables_rw_thm rw_itevs l_tevs2 r_tevs2 hyp_tevs2 rw_ityvs l_tyvs2 r_tyvs2 hyp_tyvs2 =
    let val utevs2 = filter (fn tev => all (not_same_term tev) rw_itevs) (union_lists same_term l_tevs2 r_tevs2) (* TEB2. *)
        val utevs_hyp2 = filter (fn tev => all (not_same_term tev) rw_itevs) hyp_tevs2
        val utyvs2 = filter (fn tyv => all (not_same_type tyv) rw_ityvs) (union_lists same_type l_tyvs2 r_tyvs2) (* TYB2. *)
        val utyvs_hyp2 = filter (fn tyv => all (not_same_type tyv) rw_ityvs) hyp_tyvs2 in                        (* TYA2. *)
      (utevs2, utevs_hyp2, utyvs2, utyvs_hyp2)
    end

  (* Computes:
   * -rw_thm: Rewrite theorem whose conclusion is an unquantified equality.
   * -l_ityvs2, r_ityvs2, l_itevs2, r_itevs2: Instantiable type and term
   *  variables OCCURRING in the left and right handsides in the conclusion of
   *  the equality of rw_thm.
   * -ityvs_l_only2, ityvs_r_only2, itevs_l_only2, itevs_r_only2: Instantiable
   *  type and term variables occurring ONLY in the left/right handsides of the
   *  equality in the conclusion of rw_thm.
   * -invalid_tyvs2, invalid_tevs2:
   *)
  fun extract_rw_thm_properties rw_thm rw_ityvs rw_itevs =
         (* Occurring variables. *)
    let val (l_tevs2, r_tevs2, hyp_tevs2, l_tyvs2, r_tyvs2, hyp_tyvs2) = split_eq_variables rw_thm in
         (* Occurring instantiable variables in thm and in the left handside of rw_thm. *)
    let val (l_ityvs2, r_ityvs2, l_itevs2, r_itevs2) = occurring_ivs_l_r rw_itevs rw_ityvs l_tyvs2 r_tyvs2 l_tevs2 r_tevs2 in
         (* Instantiable variables occurring only in the right handside of rw_thm. *)
    let val (ityvs_l_only2, ityvs_r_only2, itevs_l_only2, itevs_r_only2) =
            ivs_only_l_r l_ityvs2 r_ityvs2 l_tyvs2 r_tyvs2 rw_ityvs l_itevs2 r_itevs2 l_tevs2 r_tevs2 rw_itevs
          (* Uninstantiable variables. *)
        val (utevs2, utevs_hyp2, utyvs2, utyvs_hyp2) =
            uninstantiable_variables_rw_thm rw_itevs l_tevs2 r_tevs2 hyp_tevs2 rw_ityvs l_tyvs2 r_tyvs2 hyp_tyvs2 in

    let val invalid_tyvs_hyp2 = map dest_vartype (union_listss same_type [utyvs_hyp2, utyvs2])
        val invalid_tevs_hyp2 = union_listss equal (map (map term_to_string) [utevs_hyp2, utevs2]) in

        (* ityvs/itevs can be appended without creating duplicates since
         * (instantiable) ityvs/itevs and (uninstantiable) utyvs/utevs are
         * disjoint.
         *)
    let val invalid_tyvs2      = invalid_tyvs_hyp2 @ (map dest_vartype ityvs_r_only2)
        val invalid_tevs2      = invalid_tevs_hyp2 @ (map term_to_string itevs_r_only2)
        val invalid_tyvs_refl2 = invalid_tyvs_hyp2 @ (map dest_vartype ityvs_l_only2)
        val invalid_tevs_refl2 = invalid_tevs_hyp2 @ (map term_to_string itevs_l_only2) in
      (rw_thm, l_ityvs2, r_ityvs2, ityvs_l_only2, ityvs_r_only2,
               l_itevs2, r_itevs2, itevs_l_only2, itevs_r_only2,
       invalid_tyvs2, invalid_tevs2, invalid_tyvs_refl2, invalid_tevs_refl2)
    end end end end end

  fun extract_rw_thm_propertiess [] = []
    | extract_rw_thm_propertiess ((rw_thm, rw_ityvs, rw_itevs)::rw_thm_ivss) =
      let val extracted_rw_thm_propertiess = extract_rw_thm_propertiess rw_thm_ivss in
        if (is_eq o concl) rw_thm then (* ONLY EQUATIONS CAN BE USED FOR REWRITING. *)
          (extract_rw_thm_properties rw_thm rw_ityvs rw_itevs)::extracted_rw_thm_propertiess
        else
          extracted_rw_thm_propertiess
      end

  fun add_rw_thms source_thm source_ityvs source_itevs
                  (rw_thm, l_ityvs2, r_ityvs2, ityvs_l_only2, ityvs_r_only2,
                           l_itevs2, r_itevs2, itevs_l_only2, itevs_r_only2,
                   invalid_tyvs2, invalid_tevs2, invalid_tyvs_refl2, invalid_tevs_refl2) =
    (* source_thm and rw_thm are both generated from assumptions and therefore
     * are of the form !X. Ai |- Ai, and are identical if the conclusions are
     * identical. Do not use source/start theorems as rewrites as such rewrite
     * theorems do not contribute.
     *)
    if same_term (concl source_thm) (concl rw_thm) then
      []
    else
      let val      thm = (    rw_thm, invalid_tyvs2     , invalid_tevs2     , l_ityvs2, l_itevs2, ityvs_r_only2, itevs_r_only2)
          val refl_thm = (SYM rw_thm, invalid_tyvs_refl2, invalid_tevs_refl2, r_ityvs2, r_itevs2, ityvs_l_only2, itevs_l_only2) in
        [thm, refl_thm]
      end

  fun source_rw_thms source_thm source_ityvs source_itevs [] = []
    | source_rw_thms source_thm source_ityvs source_itevs (rw_thm_properties::rw_thm_propertiess) =
      let val rw_thms_rec = source_rw_thms source_thm source_ityvs source_itevs rw_thm_propertiess
          val rw_thms_current = add_rw_thms source_thm source_ityvs source_itevs rw_thm_properties in
            rw_thms_current @ rw_thms_rec
      end

  fun combine_source_rw_thms rw_thm_properties [] = []
    | combine_source_rw_thms rw_thm_properties ((source_thm, source_ityvs, source_itevs)::following_thms) =
      let val source_rw_thmss = combine_source_rw_thms rw_thm_properties following_thms
          val rw_thms = source_rw_thms source_thm source_ityvs source_itevs rw_thm_properties in
        ([(source_thm, source_ityvs, source_itevs)], rw_thms)::source_rw_thmss
      end

  (* Initial work on assumptions:
   *
   * 1. Given an assumption list [!X. A1 X, ..., !X. An X].
   * 2. For each '!X. Ai X':
   *    a) Compute !X. Ai X |- !X. Ai X
   *    b) Find instantiable variables Ai, and remove them: (!X. Ai X |- Ai, X).
   * 3. For each (!Xi. Ai Xi |- Ai, Xi):
   *    Form the set of rewrite theorems, including the reflexive version of each
   *    equation, that can be used to potentially find a rewrite Ai to Cj X':
   *    !Xj. Aj Xj |- Aj Xj, for j <> i and where Aj is an equation
   *    Aj Xj <=> lj Xj = rj Xj:
   *    (!Xi. Ai Xi |- Ai Xi, Xi,
   *     [(!Xj. Aj Xj |- lj Xj = rj Xj, Xj), (!Xj. Aj Xj |- rj Xj = lj Xj, Xj)])
   *)
  fun generate_rw_thm_combinations assumptions =
    let val thm_ivs = extract_asm_ivs assumptions in                              (* 2. *)
         (* Information regarding occurrences of variables and invalid names of
          * uninstantiated variables.
          *)
    let val rw_thm_propertiess = extract_rw_thm_propertiess thm_ivs in
         (* Pairs each assumption (source/start theorem) with all other equations
          * (excluding itself) to be used for rewriting the source to reach the
          * target.
          *)
    let val source_rw_thms = combine_source_rw_thms rw_thm_propertiess thm_ivs in (* 3. *)
      source_rw_thms
    end end end

  fun generate_term_variable invalid_names preferred_v =
    let val preferred_v_string = term_to_string preferred_v in
    let fun generate_v_string v =
      if exists (fn invalid_name => v = invalid_name) invalid_names then
        generate_v_string (concat [v, "'"])
      else
        let val renamed_v = mk_var (v, type_of preferred_v) in
          (renamed_v, v::invalid_names)
         end in
      generate_v_string preferred_v_string
    end end

  fun rename_tevs invalid_names [] = ([], invalid_names)
    | rename_tevs invalid_names (tev::tevs) =
      let val (renamed_tevs, invalid_names) = rename_tevs invalid_names tevs
          val (renamed_tev, invalid_names) = generate_term_variable invalid_names tev in
        (renamed_tev::renamed_tevs, invalid_names)
      end

  (* If the quantified implication is of the form
   * {..., A x1...x...xn, ...} |- !x X. P x X (the quantified variable is free
   * among the assumptions, then it needs to be renamed to avoid name clashing
   * when removing the quantified variables, which is what this function does.
   *)
  fun uniquify_qimp_qvs invalid_ters qimp_thm =
    let val (assumptions, conclusion) = dest_thm qimp_thm in
    let val tevs = free_varsl (conclusion::assumptions) in
    let val invalid_names = union_lists equal invalid_ters (map term_to_string tevs)
        val itevs = (#1 o strip_forall) conclusion in
    let val itevs = #1 (rename_tevs invalid_names itevs) in
    let val imp_thm = SPECL itevs qimp_thm in
      (imp_thm, itevs)
    end end end end end

  (* Initial work on quantified implication:
   * 4. Given a potentially quantified implication qimp = A |- !X. C1 X /\ ... /\ Cn X ==> C X.
   * 5. Rename quantified variables of qimp, to avoid name clashing when
   *    specializaing to remove the quantified variables, and obtaining the
   *    quantified variables in the next step.
   * 6. Obtain the quantified instantiable variables of qimp and specialize qimp to
   *    remove unquantified variables. This gives
   *    -qimp = A |- C1 X' /\ ... /\ Cn X' ==> C X'
   *   -qitevs = X'
   *   -qityvs = All type variables occurring in qimp
   *
   * @invalid_ters: Used to prevent the names of the instantiable variables of
   *  the unquantified theorem to clash with the free variables in the goal
   *  (hypotheses and the conclusion).
   *)
  fun initialize_qimp invalid_ters qimp_thm =
    let val (imp_thm, imp_itevs) = uniquify_qimp_qvs invalid_ters qimp_thm in
    let val imp_ityvs = (type_vars_in_term o concl) imp_thm in
      (imp_thm, imp_ityvs, imp_itevs)
    end end

  (* Uninstantiated type variables:
   * a) Remove instantiated type variables, including renaming of uninstantiated
   *    type variables.
   * b) Add uninstantiated type variables, avoiding duplicates in case
   *    uninstantiated type variables have not been renamed.
   *
   * Uninstantiated term variables:
   * a) Type instantiate instantiable term variables.
   * b) Remove instantiated term variables, including renaming of uninstantiated
   *    term variables.
   * c) Add uninstantiated term variables, avoiding duplicates in case
   *    uninstantiated term variables have not been renamed.
   *)
  fun update_imp_ivs imp_ityvs imp_itevs ityvs_c1 itevs_c1 tyis_c1 teis_c1 =
    let val imp_ityvs_without_is = remove_instantiated_variables same_type tyis_c1 imp_ityvs in
    let val imp_ityvs = union_lists same_type imp_ityvs_without_is ityvs_c1
        val imp_itevs_without_is = remove_instantiated_variables same_term teis_c1 (map (inst tyis_c1) imp_itevs) in
    let val imp_itevs = union_lists same_term imp_itevs_without_is itevs_c1 in
      (imp_ityvs, imp_itevs)
    end end end

  fun CONJ_ANT_TO_HYP imp_thm =
    let fun conj_tm_to_hyp_conj_thm tm =
      if not (is_conj tm) then
        ASSUME tm
      else
        let val (cl, cr) = dest_conj tm in
        let val hl = conj_tm_to_hyp_conj_thm cl in
        let val hr = conj_tm_to_hyp_conj_thm cr in
        CONJ hl hr end end end in
    let val (ant, suc) = dest_imp (concl imp_thm) in
    let val hyps_ant_thm = conj_tm_to_hyp_conj_thm ant in
    MP imp_thm hyps_ant_thm 
    end end end;

  (* Inputs:
   * -Term Ai
   * -Theorem {A1, ..., An} |- A ==> t, or {A1, ..., An} |- t.
   *
   * Output: Theorem {A1, ..., An} - {Ai} |- A /\ Ai ==> t, or  {A1, ..., An} - {Ai} |- Ai ==> t, or 
   *
   * Algorithm:
   * ------------------ASSUME
   * Ai /\ A |- Ai /\ A                 Input
   * ------------------CONJUNCT1    -------------             ------------------ASSUME
   *   Ai /\ A |- Ai                Ai |- A ==> t             Ai /\ A |- Ai /\ A
   * --------------------------------------------PROVE_HYP    ------------------CONJUNCT2
   *               Ai /\ A |- A ==> t                            Ai /\ A |- A
   * ------------------------------------------------------------------------MP
   *                    Ai /\ A |- t
   *                  ----------------DISCH 'Ai /\ A'
   *                  |- Ai /\ A ==> t
   *)
  fun HYP_IMP_TO_CONJ_IMP_RULE Ai Ai__A_imp_t_thm =
    if (not o is_imp o concl) Ai__A_imp_t_thm then
      DISCH Ai Ai__A_imp_t_thm
    else
      let val A = (#1 o dest_imp o concl) Ai__A_imp_t_thm in
      let val Ai_and_A = mk_conj (Ai, A) in
      let val Ai_and_A__Ai_and_A_thm = ASSUME Ai_and_A in
      let val Ai_and_A__Ai_thm = CONJUNCT1 Ai_and_A__Ai_and_A_thm
          val Ai_and_A__A_thm = CONJUNCT2 Ai_and_A__Ai_and_A_thm in
      let val Ai_and_A__A_imp_t_thm = PROVE_HYP Ai_and_A__Ai_thm Ai__A_imp_t_thm in
      let val Ai_and_A__t_thm = MP Ai_and_A__A_imp_t_thm Ai_and_A__A_thm in
      let val Ai_and_A_imp_t_thm = DISCH Ai_and_A Ai_and_A__t_thm in
        Ai_and_A_imp_t_thm
      end end end end end end end

  (*
   *      A0 u {Ai} u {A1, ..., Ai-1, Ai+1, ..., An} |- A
   * ---------------------------------------------------------HYPS_IMP_TO_CONJS_IMP_RULE [A1, ..., Ai-1, Ai+1, ..., An]
   *           A0 u {Ai} |- A1 /\ ... /\ Ai-1 /\ Ai+1 /\ ... /\ An ==> A
   *)
  fun HYPS_IMP_TO_CONJS_IMP_RULE thm Ajs = foldr (fn (Aj, thm) => HYP_IMP_TO_CONJ_IMP_RULE Aj thm) thm Ajs

  (* Performs steps 10, 11, 12 and 13.
   *
   * @first_conj_thm: A |- c1
   * @imp_thm: B |- c1 /\ ... /\ cn ==> c
   *
   * output: A u B |- c2 /\ ... /\ cn ==> c
   *)
  fun REMOVE_FIRST_ANT_CONJ_RULE first_conj_thm iimp_thm =
    let val c2_ns = (tl o strip_conj o #1 o dest_imp o concl) iimp_thm              (* 10. *)
        val hyp_suc_thm = CONJ_ANT_TO_HYP iimp_thm in                               (* 11. *)
    let val first_conj_hyp_thm = HYPS_IMP_TO_CONJS_IMP_RULE hyp_suc_thm c2_ns in    (* 12. *)
    let val without_first_conj_thm = PROVE_HYP first_conj_thm first_conj_hyp_thm in (* 13. *)
      without_first_conj_thm
    end end end

  (* Remove the first conjunct of the quantified implication:
   * 7. Extract the first conjunct of qimp and associated instantiable variables:
   *    (C1 X1', X1', T1'), where X1' are the term variables in X' occurring in C1 and
   *    T1' are the type variables occurring in C1 X1'.
   * 8. Apply BFS on (!Xi. Ai Xi |- Ai Xi, Xi, [(!Xj. Aj Xj |- lj Xj = rj Xj, Xj)]) to
   *    find 
   *    ([!Xk. Ak Xk]_k |- C1 cteis1 Z1, cteis1, ctyis1, utyvs, utevsm)
   *    of Ai Xi to C1 X1'.
   * 9. Instantiate qimp with cteis1 and ctyis1 to obtain
   *    iqimp = (A |- C1 cteis1 Z1 /\ ... /\ Cn cteis1 Z ==> C cteis1 Z)[ctyis1],
   *    where Z includes Z1.
   * 10.Find all Ck of qimp, k > 1: {C2 cteis1 Z1, ..., Cn cteis1 Z}.
   * 11.Apply CONJ_ANT_TO_HYP on qimp
   * 12.Apply HYPS_IMP_TO_CONJS_IMP_RULE on
   *    A |- C1 cteis1 Z1 /\ ... /\ Cn cteis1 Z ==> C cteis1 Z and
   *    {C2 cteis1 Z1, ..., Cn cteis1 Z}
   *    to obtain:
   *    A u {C1 cteis1 Z1} |- C2 cteis1 Z /\ ... /\ Cn cteis1 Z ==> C cteis1 Z
   * 13.Apply PROVE_HYP on
   *    [!Xk. Ak Xk]_k |- C1 cteis1 Z1 and
   *    A u {C1 cteis1 Z1} |- C2 cteis1 Z /\ ... /\ Cn cteis1 Z ==> C cteis1 Z
   *    to obtain:
   *    [!Xk. Ak Xk]_k u A |- C2 cteis1 Z /\ ... /\ Cn cteis1 Z ==> C cteis1 Z
   *)
  fun remove_first_imp_conjunct invalid_tyrs invalid_ters imp_thm imp_ityvs imp_itevs rw_combs =
    let val c1 = (hd o strip_conj o #1 o dest_imp o concl) imp_thm in                                                (* 7. *)
    let val tyvs = type_vars_in_term c1
        val tevs = free_vars c1 in
    let val ityvs_c1 = filter (fn ityv => exists (same_type ityv) tyvs) imp_ityvs
        val itevs_c1 = filter (fn itev => exists (same_term itev) tevs) imp_itevs in
    let val target_term = c1
        val target_ityvs = ityvs_c1
        val target_itevs = itevs_c1 in
    let val thm_is_ivs = find_target_thm invalid_tyrs invalid_ters target_term target_ityvs target_itevs rw_combs in (* 8. *)
      if isSome thm_is_ivs then
        let val (first_conj_thm, tyis_c1, teis_c1, ityvs_c1, itevs_c1) = valOf thm_is_ivs in
        let val iimp_thm = INST teis_c1 (INST_TYPE tyis_c1 imp_thm) in                                               (* 9. *)
        let val without_first_conj_thm = REMOVE_FIRST_ANT_CONJ_RULE first_conj_thm iimp_thm                          (* 10 - 13. *)
            val (imp_ityvs, imp_itevs) = update_imp_ivs imp_ityvs imp_itevs ityvs_c1 itevs_c1 tyis_c1 teis_c1 in
          (without_first_conj_thm, imp_ityvs, imp_itevs)
        end end end 
      else
        raise (mk_HOL_ERR "ltac" "remove_first_qimp_conjunct" "Could not derive conjunct of lemma from assumptions.")
    end end end end end

  (* 7 to 14.
   *
   * Inputs:
   * -rw_combs: [(Aj |- Aj, [(Ai |- li = ri)])]
   * -imp_thm: A |- C1 /\ ... /\ Cn ==> C
   *
   * Output: A u {Ai}_i|- C with instantiable type and term variables of C, if
   * C1, ..., Cn can be derived from Aj and rewrites li = ri. Otherwise an
   * exception is generated.
   *)
  fun reduce_antecedent invalid_tyrs invalid_ters imp_thm imp_ityvs imp_itevs rw_combs =
    if (is_imp o concl) imp_thm then
      let val (imp_thm, imp_ityvs, imp_itevs) =
              remove_first_imp_conjunct invalid_tyrs invalid_ters imp_thm imp_ityvs imp_itevs rw_combs in
        reduce_antecedent invalid_tyrs invalid_ters imp_thm imp_ityvs imp_itevs rw_combs
      end
    else
      (imp_thm, imp_ityvs, imp_itevs)

  (* 1 to 14.
   *
   * Algorithm:
   * 1-3, Initial work on assumptions:###########################################
   *
   * 1. Given an assumption list [!X. A1 X, ..., !X. An X].
   * 2. For each '!X. Ai X':
   *    a) Compute !X. Ai X |- !X. Ai X
   *    b) Find instantiable variables Ai, and remove them: (!X. Ai X |- Ai, X).
   * 3. For each (!Xi. Ai Xi |- Ai, Xi):
   *    Form the set of rewrite theorems, including the reflexive version of each
   *    equation, that can be used to potentially find a rewrite Ai to Cj X':
   *    !Xj. Aj Xj |- Aj Xj, for j <> i and where Aj is an equation
   *    Aj Xj <=> lj Xj = rj Xj:
   *    (!Xi. Ai Xi |- Ai Xi, Xi,
   *     [(!Xj. Aj Xj |- lj Xj = rj Xj, Xj), (!Xj. Aj Xj |- rj Xj = lj Xj, Xj)])
   *
   * 4-6, Initial work on quantified implication:################################
   *
   * 4. Given a potentially quantified implication qimp =
   *    A |- !X. C1 X /\ ... /\ Cn X ==> C X.
   * 5. Rename quantified variables of qimp, to avoid name clashing when
   *    specializaing to remove the quantified variables, and obtaining the
   *    quantified variables in the next step.
   * 6. Obtain the quantified instantiable variables of qimp and specialize qimp
   *    to remove unquantified variables. This gives
   *    -qimp = A |- C1 X' /\ ... /\ Cn X' ==> C X'
   *    -qitevs = X'
   *    -qityvs = All type variables occurring in qimp
   *
   * 7-13, Remove the first conjunct of the quantified implication:
   *
   * 7. Extract the first conjunct of qimp and associated instantiable variables:
   *    (C1 X1', X1', T1'), where X1' are the term variables in X' occurring in
   *    C1 and T1' are the type variables occurring in C1 X1'.
   * 8. Apply BFS on
   *    (!Xi. Ai Xi |- Ai Xi, Xi, [(!Xj. Aj Xj |- lj Xj = rj Xj, Xj)]) to find
   *    ([!Xk. Ak Xk]_k |- C1 cteis1 Z1, cteis1, ctyis1, utyvs, utevsm) of
   *    Ai Xi to C1 X1'.
   * 9. Instantiate qimp with cteis1 and ctyis1 to obtain
   *    iqimp = (A |- C1 cteis1 Z1 /\ ... /\ Cn cteis1 Z ==> C cteis1 Z)[ctyis1],
   *    where Z includes Z1.
   * 10.Find all Ck of qimp, k > 1: {C2 cteis1 Z1, ..., Cn cteis1 Z}.
   * 11.Apply CONJ_ANT_TO_HYP on qimp
   * 12.Apply HYPS_IMP_TO_CONJS_IMP_RULE on
   *    A |- C1 cteis1 Z1 /\ ... /\ Cn cteis1 Z ==> C cteis1 Z and
   *    {C2 cteis1 Z1, ..., Cn cteis1 Z}
   *    to obtain:
   *    A u {C1 cteis1 Z1} |- C2 cteis1 Z /\ ... /\ Cn cteis1 Z ==> C cteis1 Z
   * 13.Apply PROVE_HYP on
   *    [!Xk. Ak Xk]_k |- C1 cteis1 Z1 and
   *    A u {C1 cteis1 Z1} |- C2 cteis1 Z /\ ... /\ Cn cteis1 Z ==> C cteis1 Z
   *    to obtain:
   *    [!Xk. Ak Xk]_k u A |- C2 cteis1 Z /\ ... /\ Cn cteis1 Z ==> C cteis1 Z
   *
   * 14, Inspect result:#########################################################
   *
   * 14.If the result of step 13 is no implication, then the result is
   *    [!Xk. Ak Xk]_k u A |- C cteis1 Z, and go to step 15.
   *    Otherwise go to step 7 with:
   *    -qimp =
   *     [!Xk. Ak Xk]_k u A |- C2 cteis1 Z /\ ... /\ Cn cteis1 Z ==> C cteis1 Z
   *    -qitevs = qitevs \ cteis1
   *    -qityvs = qityvs \ ctyvs1
   *
   *
   *
   * Inputs:
   * @invalid_tyrs, @invalid_ters: Invalid uninstantiated type and term variable
   *  names (strings) when generating new uninstantiated instantiable variables
   *  in the derivation. Should be all type variables and free term variables
   *  among the assumptions and the conclusion of the goal.
   * @assumptions: A list of terms [Ai].
   * @qimp_thm: A potentially quantified implication theorem
   *  A |- !X. C1 X /\ ... /\ Cn X ==> C X.
   *
   * Outputs: The conclusion of @qimp_thm instantiated to such that the
   * antecedent conjuncts of @qimp_thm can be derived from @assumptions, with
   * uninstantiated variables quantified, if possible:
   * {Ai}_i u A |- !X'. C I X'
   *
   * Otherwise an exception is thrown.
   *)
  fun reduce_implication invalid_tyrs invalid_ters assumptions qimp_thm =
    let val rw_combs = generate_rw_thm_combinations assumptions                                                       (* 1, 2, 3. *)
        val (imp_thm, imp_ityvs, imp_itevs) = initialize_qimp invalid_ters qimp_thm in                                (* 4, 5, 6. *)
    let val (thm, ityvs, itevs) = reduce_antecedent invalid_tyrs invalid_ters imp_thm imp_ityvs imp_itevs rw_combs in (* 7 to 14. *)
    let val qthm = GENL itevs thm in
      qthm
    end end end

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
  fun LTAC qimp_thm (assumptions, t) =
         (* Invalid uninstantiated type and term variable names (strings), of all
          * type variables and free term variables among the assumptions and the
          * conclusion of the goal.
          *)
    let val invalid_tyrs = map dest_vartype (find_tyvs (t::assumptions))
        val invalid_ters = map term_to_string (find_tevs (t::assumptions)) in
    let val qthm = reduce_implication invalid_tyrs invalid_ters assumptions qimp_thm in
      ASSUME_TAC qthm (assumptions, t)
    end end

(* Test case.
Theorem x:
(!x : 'd. P x) ==>
(!x : 'd. x = c) ==>
P (c : 'd) : bool = Q (d : 'e) ==>
conclusion
Proof
REPEAT DISCH_TAC
LTAC qimp_thm
QED

val qimp_thm = mk_thm ([], ``!(x1 : 'a) (x2 : 'b). P x1 /\ Q x2 ==> R x1 x2``)
val a1 = ``!x : 'd. P x``
val a2 = ``!x : 'd. x = c``
val a3 = ``P (c : 'd) : bool = Q (d : 'e)``
val assumptions = [a1, a2, a3]
val t = ``conclusion : bool``
val invalid_tyrs = map dest_vartype (find_tyvs (t::assumptions))
val invalid_ters = map term_to_string (find_tevs (t::assumptions))
reduce_implication invalid_tyrs invalid_ters assumptions qimp_thm
*)
    

(*
Ideer:
Kan använda denna taktik för att erhålla slutsatserna av implikationer som är antaganden:
-typvariabler är oinstantierade för implikationen.
-Det kan finnas flera implikationer: Sätt gräns för hur länge ett försök ska göras med en implikation, och därefter testa nästa. Men då är det bäst att beräkna source_rw_thm kombinationer endast en gång, och sedan ta bort de kombinationer där källan är aktuell implikation.
*)

end

