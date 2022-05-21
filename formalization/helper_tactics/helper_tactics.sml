structure helper_tactics :> helper_tactics =
struct

  open HolKernel Parse boolLib bossLib ltac;

  (****************************************************************************)
  (*General functions**********************************************************)
  (****************************************************************************)

(* Debugging functions.
let val cputimer = Timer.startCPUTimer () in
let val check = Timer.checkCPUTimer cputimer in
let val _ = (print o concat) [Time.toString (#usr check), "\n"] in


val cputimer = Timer.startCPUTimer ()
val check = Timer.checkCPUTimer cputimer
val _ = (print o concat) [Time.toString (#usr check), "\n"]


 *)
fun occurrences A a = foldl (fn (other, acc) => if Term.compare (a, other) = EQUAL then acc + 1 else acc ) 0 A
fun is_duplicate A = let val a_occs = map (fn a => (a, occurrences A a)) A in exists (fn (a, occs) => occs >= 2) a_occs end
fun duplicate_warning m A = if is_duplicate A then let val _ = print m val _ = map print_term A in raise (mk_HOL_ERR "" "" "") end else ()
fun duplicate m A = if is_duplicate A then let val _ = print m val _ = map print_term A in () end else ()


  fun print_list_rec print_function [] = ()
    | print_list_rec print_function (x::xs) =
      let val _ = print_function x
          val _ = print "\n" in
        print_list_rec print_function xs
      end

  fun print_list start_text print_function l =
    let val _ = print start_text in
      print_list_rec print_function l
    end

  (* true if and only if terms t1 and t2 denote the same term, including their
   * type variables.
   *)
  fun same_term t1 t2 = Term.compare (t1, t2) = EQUAL

  (* true if and only if terms t1 and t2 do not denote the same terms, including
   * their type variables.
   *)
  fun not_same_term t1 t2 = Term.compare (t1, t2) <> EQUAL

  (* true if and only if term is in the list terms.
   *)
  fun is_in terms term = exists (same_term term) terms

  (* true if and only if term is NOT in the list terms.
   *)
  fun not_in terms term = not (is_in terms term)

  (* true if and only if each term in sublist is in in the list list.
   *)
  fun is_sublist sublist list = all (is_in list) sublist

  (* true if and only if l1 and l2 contain a common term.
   *)
  fun common_term l1 l2 = exists (is_in l1) l2

  (* true if and only if l1 and l2 have no common term.
   *)
  fun disjoint_terms l1 l2 = not (common_term l1 l2)

  (* Generates a variable that does not occur in terms_with_invalid_mark_variables.
   *)
  fun generate_mark term_to_substitute terms_with_invalid_mark_variables =
    gen_variant is_constname "" (free_varsl terms_with_invalid_mark_variables) (mk_var ("mark", type_of term_to_substitute))

  (* Generates a fresh variable not used in the HOL session so far of the same
   * type as the given term.
   *)
  fun genvar_term term = (genvar o type_of) term

  (* Given [v0, ..., ti, ..., vn-1]
   * returns ([v0, ..., vi-1], ti, [vi+1, ..., vn-1]), where the ti is the first
   * element not being a variable.
   *)
  fun take_first predicate [] = raise (mk_HOL_ERR "helper_tactics" "take_first" "Empty list.\n")
    | take_first predicate (h::t) =
      if predicate h then
        ([], h, t)
      else
        let val (prefix, taken_element, suffix) = take_first predicate t in
          (h::prefix, taken_element, suffix)
        end

  fun not_var_nor_const t = not (is_var t orelse is_const t)

  (* Input:
   * -A term.
   *
   * Output:
   * -False: There is no subterm in term of the form 'let x = e in body'.
   * -True: There is a subterm in term of the form 'let x = e in body'.
   *)
  fun is_let_scalar term = if is_let term then (is_abs o hd o #2 o strip_comb) term else false

  (* Input:
   * -A term.
   *
   * Output:
   * -False: The given term is not of the form 'let (p1, p2) = (a1, a2) in e'.
   * -True: The term is of the form 'let (p1, p2) = (a1, a2) in e'.
   *)
  fun is_let_pair term = if is_let term then (is_comb o hd o #2 o strip_comb) term else false

  (* Inputs:
   * -An existential term xterm, ?x.s.
   * -A list of invalid variable names invalid_variable_names (formed from e.g.
   *  an assumption list and a conclusion).
   *
   * Output:
   * -NONE if xterm is not of the form ?x.s.
   * -SOME (v, x, inst_body), where v is a variable not occurring in terms, x
   *  being x in ?x.s, and inst_body = s[v/x], if xterm is of the form ?x.s.
   *)
  fun instantiate_exist xterm invalid_variable_names =
    if is_exists xterm then
      let val (x, xbody) = dest_exists xterm in
      let val v = gen_variant is_constname "" ((free_vars xterm) @ invalid_variable_names) x in
      let val inst_body = subst [x |-> v] xbody in
        SOME (v, x, inst_body)
      end end end
    else
      NONE

  (* Inputs:
   * -An existential term xterm, ?x.s.
   * -A term instantiation specifying the desired instantiation of x in s.
   * -A list of terms terms (e.g. an assumption list and a conclusion).
   *
   * Output:
   * -NONE if xterm is not of the form ?x.s.
   * -SOME (v, x, inst_body), where v is a variable not occurring in terms, x
   *  being x in ?x.s, and inst_body = s[v/x], if xterm is of the form ?x.s. If
   *  instantiation does not occur in xterm nor terms, then v is instantiation.
   *  Otherwise, v is instantiation with a prime.
   *)
  fun instantiate_specified_exist xterm instantiation terms =
    if is_exists xterm then
      let val (x, xbody) = dest_exists xterm in
      let val v = gen_variant is_constname "" (free_varsl (xterm::terms)) instantiation in
      let val inst_body = subst [x |-> v] xbody in
        SOME (v, x, inst_body)
      end end end
    else
      NONE

  (* Inputs:
   * -Boolean function property on terms.
   * -Term term.
   *
   * Outputs:
   * -NONE: If there is no subterm of term satisfying property.
   * -SOME (mark, template, subterm): If subterm is a subterm of term satisfying
   *  property and template[subterm/mark] = term.
   *)
  fun has_subterm_property property term =
    let fun subterm_property subterm =
      if property subterm then
        let val mark = (genvar o type_of) subterm in
          SOME (mark, mark, subterm)
        end
      else if is_var subterm orelse is_const subterm then
        NONE
      else if is_comb subterm then
        let val (function, argument) = dest_comb subterm in
          case subterm_property function of
            NONE => (
            case subterm_property argument of
              NONE => NONE
            | SOME (mark, argument_template, subterm_with_property) =>
              SOME (mark, mk_comb (function, argument_template), subterm_with_property))
          | SOME (mark, function_template, subterm_with_property) =>
            SOME (mark, mk_comb (function_template, argument), subterm_with_property)
        end
      else if is_abs subterm then
        let val (bvar, body) = dest_abs subterm in
          case subterm_property body of
            NONE => NONE
          | SOME (mark, template, subterm_with_property) =>
             (* A subterm satisfying the subterm property is considered to not
              * satisfy the subterm property if the subterm contains free
              * variables that are bound in term.
              * The reason is that free variables in a subterm are considered to
              * represent specific objects/elements/terms, which is false if the
              * free variable in the subterm is bound in term.
              *)
            if free_in bvar subterm_with_property then
              NONE
            else
              SOME (mark, mk_abs (bvar, template), subterm_with_property)
        end
      else
        NONE
    in
      subterm_property term
    end

  (* Inputs:
   * -Boolean function property on terms.
   * -Term term.
   *
   * Outputs:
   * -NONE: If there is no subterm of term satisfying property.
   * -SOME (mark, template, subterm): If subterm is a subterm of term satisfying
   *  property and template[subterm/mark] = term.
   *)
  fun some_subterm_property (some_property : Term.term -> 'a option) (term : Term.term) =
    let fun subterm_property (subterm : Term.term) =
      case some_property subterm of
        NONE => (
        if is_var subterm orelse is_const subterm then
          NONE
        else if is_comb subterm then
          let val (function, argument) = dest_comb subterm in
            case subterm_property function of
              NONE => (
              case subterm_property argument of
                NONE => NONE
              | SOME (mark, argument_template                    , subterm_with_property, property) =>
                SOME (mark, mk_comb (function, argument_template), subterm_with_property, property))
            |   SOME (mark, function_template                    , subterm_with_property, property) =>
                SOME (mark, mk_comb (function_template, argument), subterm_with_property, property)
          end
        else if is_abs subterm then
          let val (bvar, body) = dest_abs subterm in
            case subterm_property body of
              NONE => NONE
            | SOME (mark, template, subterm_with_property, property) =>
              if free_in bvar subterm_with_property then
                NONE
              else
                SOME (mark, mk_abs (bvar, template), subterm_with_property, property)
          end
        else
          NONE)
      | SOME property => (
        let val mark = (genvar o type_of) subterm in
          SOME (mark, mark, subterm, property)
        end)
    in
      subterm_property term
    end

  (* Inputs:
   * -Boolean function property on terms.
   * -Terms terms.
   *
   * Outputs:
   * -NONE: If there is no subterm of any term satisfying property.
   * -SOME subterm: If subterm is a subterm of a term satisfying property.
   *)
  fun has_terms_subterm_property subterm_property terms =
    let fun has_terms_subterm_property_rec [] = NONE
          | has_terms_subterm_property_rec (term::terms) =
            case has_subterm_property subterm_property term of
              NONE => has_terms_subterm_property_rec terms
            | SOME (mark, template, subterm_with_property) => SOME (mark, template, subterm_with_property, term)
    in
      has_terms_subterm_property_rec terms
    end

  (* subterm is a subterm of term if and only if a subterm of term is the same
   * term as subterm, and the free variables of subterm are free in term. This
   * means that free variables are considered to represent a specific object (a
   * constant).
   *)
  fun is_subterm subterm term =
    let val fv_subterm = free_vars subterm
        fun is_same t1 t2 = Term.compare (t1, t2) = EQUAL in
    let fun is_fv_subterm_in_fv_term fv_term = all (fn v => exists (is_same v) fv_term) fv_subterm in
    let fun is_subterm_recursive fv_term subterm term =
      if is_same subterm term andalso is_fv_subterm_in_fv_term fv_term then
        true
      else if is_var term orelse is_const term then
        false
      else if is_comb term then
        let val (function, argument) = dest_comb term in
          if is_subterm_recursive fv_term subterm argument then
            true
          else
            is_subterm_recursive fv_term subterm function
        end
      else (* is_abs term *)
        let val (bv, body) = dest_abs term in
        let val fv_term = filter (fn fv => not (is_same fv bv)) fv_term in
          is_subterm_recursive fv_term subterm ((#2 o dest_abs) term)
        end end in
      is_subterm_recursive (free_vars term) subterm term
    end end end

  (* SOME term if and only if subterm occurs in some term in terms. *)
  fun has_subterms subterm [] = NONE
    | has_subterms subterm (term::terms) =
        if is_subterm subterm term then
          SOME term
        else
          has_subterms subterm terms

  (* Given conv, property and term. If term = '...subterm...' where 'subterm'
   * satisfies property, and 'conv subterm' = '|- subterm = t', then returns
   * SOME |- 'term = ...t...'
   *)
  fun has_subterm_rw conv property term =
    let fun subterm_rw subterm =
      if property subterm then
          SOME (conv subterm)
      else if is_var subterm orelse is_const subterm then
        NONE
      else if is_comb subterm then
        let val (function, argument) = dest_comb subterm in
          case subterm_rw function of
            NONE => (
            case subterm_rw argument of
              NONE => NONE
            | SOME thm => SOME (AP_TERM function thm))
          | SOME thm => SOME (AP_THM thm argument)
        end
      else if is_abs subterm then
        let val (bvar, body) = dest_abs subterm in
          case subterm_rw body of
            NONE => NONE
          | SOME thm => SOME (ABS bvar thm)
        end
      else
        NONE
    in
      subterm_rw term
    end

  (* Given conv, property and term. If term = '...subterm...' where 'subterm'
   * satisfies property, and 'conv subterm' = '|- subterm = t', then returns
   * SOME |- 'term = ...t...'
   *)
  fun some_subterm_rw some_conv term =
    let fun subterm_rw subterm =
      case some_conv subterm of
        SOME thm => SOME thm
      | NONE =>
        if is_var subterm orelse is_const subterm then
          NONE
        else if is_comb subterm then
          let val (function, argument) = dest_comb subterm in
            case subterm_rw function of
              NONE => (
              case subterm_rw argument of
                NONE => NONE
              | SOME thm => SOME (AP_TERM function thm))
            | SOME thm => SOME (AP_THM thm argument)
          end
        else if is_abs subterm then
          let val (bvar, body) = dest_abs subterm in
            case subterm_rw body of
              NONE => NONE
            | SOME thm => SOME (ABS bvar thm)
          end
        else
          NONE
    in
      subterm_rw term
    end

  fun have_terms_subterm_rw conv property [] = NONE
    | have_terms_subterm_rw conv property (term::terms) =
      case has_subterm_rw conv property term of
        NONE => have_terms_subterm_rw conv property terms
      | SOME thm => SOME (term, thm)

  fun RW_TERM_TAC rw_term rw_thm (A, t) =
    let val (old, new) = (dest_eq o concl) rw_thm
        val mark = genvar bool in
    let val (A', t', template, DISCH_ASM, UNDISCH_ASM) =
      if same_term rw_term t then
        (A, new, mark, fn thm => thm, fn thm => thm)
      else
        let val A'_u = foldr (fn (a, (aa, u)) => if u andalso same_term rw_term a then (new::aa, false) else (a::aa, u)) ([], true) A in
          (#1 A'_u, t, mk_imp (mark, t), DISCH new, UNDISCH)
        end in
    let val v' = fn thms => (UNDISCH_ASM o (SUBST [mark |-> SYM rw_thm] template) o DISCH_ASM o hd) thms in
      ([(A', t')], v')
    end end end

  (* Inputs:
   * -A term term.
   * -A term old_term.
   * -A term new_term.
   *
   * Output:
   * -Replaces each occurence of old_term with new_term in term. That is:
   *  term[new_term/old_term].
   *)
  fun substitute_term term old_term new_term = subst [old_term |-> new_term] term

  (* Inputs:
   * -A list of terms.
   * -A term old_term.
   * -A term new_term.
   *
   * Output:
   * -A list of term for which each element is equal to the input list but with
   *  new_term substituting old_term. *)
  fun substitute_terms [] old_term new_term = []
    | substitute_terms (term::terms) old_term new_term =
        let val substituted_term = substitute_term term old_term new_term in
        let val substituted_terms = substitute_terms terms old_term new_term in
          substituted_term::substituted_terms
        end end

  fun merge_matchings compare matchings1 [] = SOME matchings1
    | merge_matchings compare matchings1 ({redex = from2, residue = to2}::matchings2) =
        case merge_matchings compare matchings1 matchings2 of
          NONE => NONE
        | SOME merged_matchings => (
            case List.find (fn {redex = from1, residue = _} => compare (from1, from2) = EQUAL) merged_matchings of
              NONE => SOME ({redex = from2, residue = to2}::merged_matchings)
            | SOME {redex = from1, residue = to1} => if compare (to1, to2) = EQUAL then SOME merged_matchings else NONE) (* Check consistent match. *)

  fun merge_type_matchings matchings1 matchings2 = merge_matchings Type.compare matchings1 matchings2
  fun merge_term_matchings matchings1 matchings2 = merge_matchings Term.compare matchings1 matchings2
  val merge_term_instantiations = merge_term_matchings
  val merge_type_instantiations = merge_type_matchings

  fun find_explicit_type_variable_instantiation_rec from to =
    if is_vartype from then    (* Can map from variable to anything. *)
      SOME [{redex = from, residue = to}]
    else if is_vartype to then (* Cannot map from non-variable to variable. *)
      NONE
    else  (* Can map if type operator is same and arguments are matchable, where different arguments have consistent matchings. *)
      let val (type_operator_from, type_arguments_from) = dest_type from
          val (type_operator_to, type_arguments_to) = dest_type to in
      let val type_operators_match = type_operator_from = type_operator_to in
        if type_operators_match then
          let val type_arguments = zip type_arguments_from type_arguments_to in
          let val type_argument_matchings = map (fn (from, to) => find_explicit_type_variable_instantiation_rec from to) type_arguments
              fun merge_type_argument_matchings [] = SOME []
                | merge_type_argument_matchings (NONE::_) = NONE
                | merge_type_argument_matchings ((SOME matching)::matchings) =
                  case merge_type_argument_matchings matchings of
                    NONE => NONE
                  | SOME merged_type_matching => merge_type_matchings matching merged_type_matching in
            merge_type_argument_matchings type_argument_matchings
          end end
        else
          NONE
      end end

  fun find_explicit_type_variable_instantiation from_term to_term =
    let val from = type_of from_term
        val to = type_of to_term in
      find_explicit_type_variable_instantiation_rec from to
    end

  (* Assumes that variable and instantiatable variables belong to the same term
   * and hence if variable is an instantiatable variable, then it exists in
   * instantiatable_variable with the same type.
   *)
  fun is_instantiatable_variable instantiatable_variables variable = exists (same_term variable) instantiatable_variables

  (* Input:
   * -Terms from and to.
   * -Terms instantiatable_variables which are term variables that may be
   *  instantiated to terms in from.
   *
   * Output:
   * -Some (term_variable_instantiation, type_variable_instantiation) if the
   *  free variables instantiatable_variables in from can be substituted for
   *  terms such that
   *  (inst type_variable_instantiation from)[terms/instantiatable_variables] = to.
   * -NONE otherwise.
   *)
  fun find_explicit_variable_instantiation instantiatable_variables from to =
    if is_var from then
      if is_instantiatable_variable instantiatable_variables from then
        case find_explicit_type_variable_instantiation from to of
          NONE => NONE
        | SOME type_matching => SOME ([{redex = inst type_matching from, residue = to}], type_matching)
      else if Term.compare (from, to) = EQUAL then (* from and to denote the same object and no instantiation is needed. *)
        SOME ([], [])
      else
        NONE
    else if is_const from andalso is_const to then
      if term_to_string from = term_to_string to then (* Do not compare types here. *)
        case find_explicit_type_variable_instantiation from to of (* Compare types here. *)
          NONE => NONE
        | SOME type_matching => SOME ([], type_matching)
      else
        NONE
    else if is_comb from andalso is_comb to then
      let val (fun_from, arg_from) = dest_comb from
          val (fun_to, arg_to) = dest_comb to in
        case (find_explicit_variable_instantiation instantiatable_variables fun_from fun_to, find_explicit_variable_instantiation instantiatable_variables arg_from arg_to) of
          (_, NONE) => NONE
        | (NONE, _) => NONE
        | (SOME (fun_term_matching, fun_type_matching), SOME (arg_term_matching, arg_type_matching)) =>
          case (merge_term_matchings fun_term_matching arg_term_matching, merge_type_matchings fun_type_matching arg_type_matching) of
            (NONE, _) => NONE
          | (_, NONE) => NONE
          | (SOME term_matching, SOME type_matching) => SOME (term_matching, type_matching)
      end
    else if is_abs from andalso is_abs to then
      let val (var_from, body_from) = dest_abs from
          val (var_to, body_to) = dest_abs to
          fun is_same term1 term2 = Term.compare (term1, term2) = EQUAL in
        case find_explicit_variable_instantiation (var_from::instantiatable_variables) body_from body_to of
          NONE => NONE
        | SOME (term_matching, type_matching) => (
            (* Types can be compared in Term.compare in is_same since the occurrence of the bound variable is checked. *)
            case filter (fn {redex = v1, residue = v2} => is_same v1 var_from orelse is_same v2 var_to) term_matching of
              [] => ( (* Neither bounded variable occurs in their respective bodies. *)
              (* Check and merge type matchings of bound variabless.*)
              case find_explicit_type_variable_instantiation var_from var_to of
                NONE => NONE
              | SOME from_to_type_matching =>
                case merge_type_matchings from_to_type_matching type_matching of
                  NONE => NONE
                | SOME merged_type_matching => SOME (term_matching, merged_type_matching))
            | bound_matching =>
                (* Types can be compared in Term.compare in is_same since the
                 * occurrences of the bound variables are checked.
                 *
                 * Check that bounded variables match in the sense that they
                 * occur at same positions in from and to.
                 *)
                if all (fn {redex = f, residue = t} => is_same f var_from andalso is_same t var_to) bound_matching then
                  (* Remove bounded variables from matching.
                   *)
                  let val updated_term_matching =
                     (* Types can be compared in Term.compare in is_same since the occurrences of the bound variables are checked. *)
                        filter (fn {redex = f, residue = t} => not (is_same f var_from) andalso not (is_same t var_to)) term_matching in
                    case find_explicit_type_variable_instantiation var_from var_to of
                      NONE => NONE
                    | SOME from_to_type_matching =>
                      case merge_type_matchings from_to_type_matching type_matching of
                        NONE => NONE
                      | SOME merged_type_matching => SOME (updated_term_matching, merged_type_matching)
                  end
                else
                  NONE)
      end
    else (* Structure not matching of from and to. *)
      NONE

  (* Inputs:
   * -A goal (A, t).
   * -A theorem B_thm, B |- s, achieving the subgoal (A, t)[new_term/old_term].
   * -A theorem of the form 'C |- new_term = old_term'
   *
   * Output:
   * -A theorem 'D |- r' achieving (A u C, t), obtained by
   *  replacing each occurrence of new_term in B with old_term, if that occurrence
   *  of new_term in (A, t)[new_term/old_term] was a result of the substitution
   *  [new_term/old_term] applied on (A, t).
   *
   * Algorithm:
   * 1. (Am, tm) := (A, t)[marker/old_term]
   * 2. (At, tt) := (A, t)[new_term/old_term]
   * 3. For each Bi i B find the corresponding Ati satisyfing Bi = Ati, record
   *    the pair (Ami, Bi). marker in Ami denotes the locations of new_term in Bi
   *    that shall be replaced by old_term.
   * 4. For each recorded pair (Ami, Bi), discharge the assumptions of B and the
   *    corresponding assumptions from Am:
   *      'Amn ==> ... ==> Am1 ==> tm'
   *      |-  Bn ==> ... ==> B1 ==> s
   * 5. Substitute old_term for new_term at the places indicated by the template
   *    Amn ==> ... Am1 ==> tm in |- Bn ==> ... ==> B1 ==> s by means of the
   *    theorem 'C |- new_term = old_term' to form the theorem
   *    '(C |- Bn ==> ... ==> B1 ==> s)[old_term/new_term], where old_term
   *    replaces new_term, if new_term was a result of replacing old_term in
   *    (A, t).
   * 6. Undischarge the assumption by forming:
   *    'C u {Bn, ..., B1}[old_term/new_term] |- s[old_term/new_term], where
   *    old_term replaces new_term if new_term was a result of replacing old_term
   *    in (A, t).
   *)
  fun reverse_substitute goal B_thm new_term_eq_old_term_thm =
    let val (A, t) = goal
        val (B, s) = dest_thm B_thm
        val (new_term, old_term) = (dest_eq o concl) new_term_eq_old_term_thm in
    (* New fresh marker variable used for reverse substitution without
     * substituting occurrences of new_term that already existed in (A, t) before
     * the substitution [new_term/old_term]. *)
    let val original_marker = mk_var ("mark", type_of old_term)
        val illegal_markers = A @ [t] @ B @ [s] @ [old_term] @ [new_term] in
    let val marker = gen_variant is_constname "" (free_varsl illegal_markers) original_marker in
    (* 3. *)
    let fun find_discharge_assumptions [] = []
          | find_discharge_assumptions (assumption::assumptions) =
              let val a_assumption_template = substitute_term assumption old_term marker (* 1. *)
                  val b_assumption = substitute_term assumption old_term new_term in     (* 2. At = B, tt = s *)
                if exists (fn b => Term.compare (b, b_assumption) = EQUAL) B then
                  (a_assumption_template, b_assumption)::(find_discharge_assumptions assumptions)
                else
                  find_discharge_assumptions assumptions
              end in
    (* 4. *)
    let val discharge_assumptions = find_discharge_assumptions A
        fun discharge [] template reverse_substitute_thm = (template, reverse_substitute_thm)
          | discharge ((a_assumption_template, b_assumption)::discharge_assumptions) template reverse_substituted_thm =
              let val template = mk_imp (a_assumption_template, template)
                  val reverse_substituted_thm = DISCH b_assumption reverse_substituted_thm in
                discharge discharge_assumptions template reverse_substituted_thm
              end
        val A_implication_template = substitute_term t old_term marker in
    let val (A_implication_template, reverse_substituted_implication_subgoal_thm) =
      discharge discharge_assumptions A_implication_template B_thm in
    (* 5. *)
    let val reverse_substituted_implication_goal_thm =
      SUBST [marker |-> new_term_eq_old_term_thm] A_implication_template reverse_substituted_implication_subgoal_thm

        fun undischargen n thm =
          if n = 0 then
              thm
            else
              undischargen (n - 1) (UNDISCH thm) in
    (* 6. *)
    let val goal_thm = undischargen (length discharge_assumptions) reverse_substituted_implication_goal_thm in
      goal_thm
    end end end end end end end end

  (* Inputs:
   * -Function conversion: term -> thm.
   * -Term of a form that conversion can produce a rewrite theorem for.
   * -Goal (A, t).
   *
   * Outputs:
   * -Subgoal (A, t)[rhs/lhs], where conversion term equals to 'B |- lhs = rhs'.
   * -Validation function mapping a theorem achieving (A, t)[rhs/lhs] to a
   *  theorem achieving (A, t).
   *)
  fun substitution_subgoal_validation conversion term (A, t) = 
    (* Subgoal generation. *)
    let val rewrite_thm = conversion term in
    let val (old_term, new_term) = (dest_eq o concl) rewrite_thm in
    let val A' = substitute_terms A old_term new_term
        val t' = substitute_term t old_term new_term in
    (* Validation function generation. *)
    let val validation_function = (fn thms =>
      let val original_goal = (A, t)
          val B_thm = hd thms (* One subgoal, gives one achieving theorem, which is obtained by means of hd. *)
          val new_term_eq_old_term_thm = SYM rewrite_thm in
      let val achieving_thm = reverse_substitute original_goal B_thm new_term_eq_old_term_thm in
        achieving_thm
      end end) in
      ([(A', t')], validation_function)
    end end end end

  (* Inputs:
   * -A term xterm of the form ?x1...xn.s.
   * -A list of terms (e.g. assumption list and conclusion of a goal).
   *
   * Outputs:
   * -A term s[v1/x1, ..., vn/xn].
   * -A list of pairs [(vn, xn), ..., (v1, x1)], where no vi occurs free in
   *  ?x1...xn.s, nor in terms, and each vi is distinct from any other vj.
   *)
  fun instantiate_exists xterm terms =
    let fun instantiate_exists_rec xterm invalid_variable_names mapping =
      case instantiate_exist xterm invalid_variable_names of
        NONE => (xterm, mapping)
      | SOME (vi, xi, inst_body) => instantiate_exists_rec inst_body (vi::invalid_variable_names) ((vi,xi)::mapping)
    in
      instantiate_exists_rec xterm (free_varsl terms) []
    end

  fun update_terms some_property [] = raise (mk_HOL_ERR "helper_tactics" "update_terms" "No terms to update.")
    | update_terms some_property (term::terms) =
      case some_property term of
        NONE =>
        let val (updated_terms, old_term) = update_terms some_property terms in
          (term::updated_terms, old_term)
        end
      | SOME new_terms => (new_terms @ terms, term)

  fun SPLIT_ASM_CONJ_TAC (A, t) =
    let fun some_property a = if is_conj a then let val (c1, c2) = dest_conj a in SOME [c1, c2] end else NONE in
    let val (A', conj) = update_terms some_property A in
    let val validation = fn thms =>
      (*                                      ----------------------ASSUME c1 /\ c2
       *                                      {c1 /\ c2} |- c1 /\ c2
       * ----------------------ASSUME         ----------------------CONJUNCT1      -----------------INPUT
       * {c1 /\ c2} |- c1 /\ c2                  {c1 /\ c2} |- c1                  A u {c1, c2} |- t
       * ----------------------CONJUNCT2         ---------------------------------------------------PROVE_HYP
       * {c1 /\ c2} |- c2                                     A u {c1 /\ c2, c2} |- t
       * ----------------------------------------------------------------------------PROVE_HYP
       *                              A u {c1 /\ c2} |- t
       *)
      let val thm = hd thms in
      let val c1_and_c2_thm = ASSUME conj in
      let val c1_thm = PROVE_HYP (CONJUNCT1 c1_and_c2_thm) thm in
      let val c1_c2_thm = PROVE_HYP (CONJUNCT2 c1_and_c2_thm) c1_thm in
          c1_c2_thm
      end end end end in
      ([(A', t)], validation)
   end end end

  val SPLIT_ASM_TAC = REPEAT SPLIT_ASM_CONJ_TAC;

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
   * A0 u {Ai} |- A1 /\ ... /\ Ai-1 /\ Ai+1 /\ ... /\ An ==> A
   *)
  fun HYPS_IMP_TO_CONJS_IMP_RULE thm Ajs = foldr (fn (Aj, thm) => HYP_IMP_TO_CONJ_IMP_RULE Aj thm) thm Ajs

  (* Inputs:
   * -Ai
   * -A0 |- A1 /\ ... /\ Ai /\ ... /\ An ==> A
   *
   * Output:
   * -A0 u {Ai} |- A1 /\ ... /\ Ai-1 /\ Ai+1 /\ ... /\ An ==> A
   *
   * -------------------------ASSUME Aj               ----------------------------------------
   * {A1} |- A1 ... {An} |- An                        A0 |- A1 /\ ... /\ Ai /\ ... /\ An ==> A           <---INPUT
   * --------------------------------LIST_CONJ        ----------------------------------------UNDISCH
   * {A1, ..., An} |- A1 /\ ... /\ An                 A0 u {A1 /\ ... /\ Ai /\ ... /\ An} |- A
   * -----------------------------------------------------------------------------------------PROVE_HYP
   *                            A0 u {A1, ..., An} |- A
   *                -----------------------------------------------Printing
   *                A0 u {Ai} u {A1, ..., Ai-1, Ai+1, ..., An} |- A
   *           ---------------------------------------------------------HYPS_IMP_TO_CONJS_IMP_RULE [A1, ..., Ai-1, Ai+1, ..., An]
   *           A0 u {Ai} |- A1 /\ ... /\ Ai-1 /\ Ai+1 /\ ... /\ An ==> A           <---OUTPUT
   *)
  fun ANT_CONJ_TO_HYP_RULE Ai thm =
    let val conjs = (strip_conj o #1 o dest_imp o concl) thm in
    let val As_hyp_As_conj = LIST_CONJ (map ASSUME conjs)
        val As_conj_thm = UNDISCH thm in
    let val As_hyp_thm = PROVE_HYP As_hyp_As_conj As_conj_thm
        val Ajs = filter (fn Aj => not (same_term Ai Aj)) conjs in
    let val Ai_hyp_thm = HYPS_IMP_TO_CONJS_IMP_RULE As_hyp_thm Ajs in
      Ai_hyp_thm
    end end end end

  (*
   * A |- Ai /\ x = x /\ Aj ==> B
   * -----------------------------ANT_CONJ_TO_HYP_RULE x = x
   * A u {x = x} |- Ai /\ Aj ==> B
   * -----------------------------PROVE_HYP boolTheory.EQ_REFL
   *     A |- Ai /\ Aj ==> B
   *)
  fun REMOVE_ID_EQS_RULE thm [] = thm
    | REMOVE_ID_EQS_RULE thm (eq::eqs) =
      let val l = lhs eq in
      let val thm1 = ISPEC l boolTheory.EQ_REFL
          val thm2 = ANT_CONJ_TO_HYP_RULE eq thm in
      let val thm = PROVE_HYP thm1 thm2 in
        REMOVE_ID_EQS_RULE thm eqs
      end end end

  (* True if and only if term is of the form 'x = x'.
   *)
  fun is_identity term =
    if is_eq term then
      (Term.compare o dest_eq) term = EQUAL
    else
      false

  (*
   * A |- Ai /\ x1 = x1 /\ ... /\ xn = xn /\ Aj ==> B
   * ------------------------------------------------REMOVE_ID_EQ_ANT_CONJS_RULE
   *               A |- Ai /\ Aj ==> B
   *)
  fun REMOVE_ID_EQ_ANT_CONJS_RULE thm =
    let val (hyps, conc) = (dest_imp o concl) thm in
    let val conjuncts = strip_conj hyps in
    let val id_eqs = filter is_identity conjuncts in
      REMOVE_ID_EQS_RULE thm id_eqs
    end end end




  (* Inputs:
   * -A string structure_name specifying the name of the structure in which the
   *  tactic is defined.
   * -A string tactic_name specifying the name of the tactic this function is
   *  used to define.
   * -A string failure_explanation indicating to the user why the tactic failed.
   * -A property function on terms returning NONE if no subterm in the goal has
   *  the property, and SOME substerm where subterm has the property and is to be
   *  rewritten.
   * -A conversion that given a term satisfying the property produces an equality
   *  theorem (of the form '|- t1 = t2', without assumptions) used to rewrite the
   *  goal (both assumptions and conclusion).
   *
   * Output:
   * -A tactic that performs successive rewrites until no subterm in the goal has
   *  the specified property. If the original goal does not have the property,
   *  the specified failure message will be printed.
   *)
  fun SPECIFIC_REWRITE_TACTIC_TEMPLATE structure_name tactic_name failure_explanation has_property conversion =
    let fun tactic (A, t) =
          case has_property (t::A) of
            NONE => raise (mk_HOL_ERR structure_name tactic_name failure_explanation)
          | SOME (mark, template, subterm_with_property, term) => substitution_subgoal_validation conversion subterm_with_property (A, t)
    in
      tactic THEN (REPEAT tactic) THEN SPLIT_ASM_TAC
    end

  (* split_list n [x1...xk] = ([x1...xn], [xn+1...xk])
   *)
  fun split_list n [] = ([], [])
    | split_list n (e::es) =
      if n = 0 then
        ([], e::es)
      else
        let val (p, s) = split_list (n - 1) es in
          (e::p, s)
        end

  (* Applies tactic on all subgoals, and composes their validation functions with
   * validation, and returns a list of subgoals paired with the term to rewrite
   * next for that subgoal.
   *
   * acmtstvs =
   * [([(a11, c11, mark11, template11, subterm11, term11), ..., (a1n, c1n, mark1n, template1n, subterm1n, term1n)], validation1)
   *  ,...,
   *  ([(am1, cm1, markm1, templatem1, subtermm1, termm1), ..., (amp, cmp, markmp, templatemp, subtermmp, termmp)], validationm)]
   *
   * validation [A1 |- c1, ..., An |- cn] = A |- t
   *
   * Output:
   * ([(A1', t1', subterm1', term1'), ..., (Am', tm', subtermm', termm')], composed_validation)
   * such that
   * composed_validation [A1' |- t1', ..., Am' |- tm'] = A |- t
   * where tactic (Ai, ti) = [(Ai1, ti1, subterm1, term1), ...] which is a subset of
   * {(Ai', ti', subtermi', termi'))}.
   *)
  fun COMPOSE_SUBGOALS_GOAL_TAC acmtstsvs validation =
    (* [(a11, c11, m11, template11, s11, t11), ..., (a1m, c1m, m1m, template1m, s1m, t1m),
     *  (a21, c21, m21, template21, s21, t21), ..., (a2q, c2q, m2q, template2q, s2q, t2q),
     *  ...,
     *  (an1, cn1, mn1, templaten1, sn1, tn1), ..., (anp, cnp, mnp, templatenp, snp, tnp)],
     * validation,
     * [m, q, ..., p]
     *)
    let val (acmtsts, validations, number_of_subsubgoals) = foldl
        (fn ((acmtsts, v), (acc_acmtsts, acc_vs, ns)) => (acc_acmtsts @ acmtsts, acc_vs @ [v], ns @ [length acmtsts]))
        ([], [], [])
        acmtstsvs in
    (*
     * composed_validation [A11 |- t11, ..., A1m |- t1m, A21 |- t21, ..., A2q |- t2q, ..., An1 |- tn1, ..., Anp |- tnp] = 
     * validation [v1 [A11 |- t11, ..., A1m |- t1m], v2 [A21 |- t21, ..., A2q |- t2q], ... vn [An1 |- tn1, ..., Anp |- tnp]] =
     * validation [A1 |- t1, A2 |- t2, ..., An |- tn] =
     * A |- t
     *)
    let val composed_validation =
        fn thms =>
        let fun group_subsubgoal_thms subsubgoal_thms [] = []
              | group_subsubgoal_thms subsubgoal_thms (n::ns) =
                let val (grouped_subgoal_thms, subsubgoal_thms_to_group) = split_list n subsubgoal_thms in
                let val grouped_subgoal_thmss = group_subsubgoal_thms subsubgoal_thms_to_group ns in
                  grouped_subgoal_thms::grouped_subgoal_thmss
                end end in
        let val grouped_subgoal_thms = group_subsubgoal_thms thms number_of_subsubgoals in
        let val validation_subgoal_thms = zip validations grouped_subgoal_thms in
        let val subgoal_thms = map (fn (v, sgs) => v sgs) validation_subgoal_thms in
        let val goal_thm = validation subgoal_thms in
          goal_thm
        end end end end end in
      (acmtsts, composed_validation)
    end end

  (* Applies tactic1 followed by tactic2 on every subgoal produced by tactic1.
   * tactic1 and tactic2 takes inputs and produces outputs of the following
   * form:
   * -Input: mark template subterm term (assumptions, conclusion).
   * -Ouput: [(assumptions, conclusion, mark, template, subterm, term)].
   *)
  fun COMPOSE_ACMTST_TAC tactic1 tactic2 mark template subterm term (A, t) =
    let val (acmtsts1, v1) = tactic1 mark template subterm term (A, t) in
    let val acmtstsvs2 = map (fn (a, c, m, tem, s, ter) => tactic2 m tem s ter (a, c)) acmtsts1 in
      COMPOSE_SUBGOALS_GOAL_TAC acmtstsvs2 v1
    end end

  (* Applies tactic1 followed by tactic2.
   * -tactic1 does not change/return the mark nor the template and produces a
   *  single subgoal.
   * -tactic2 takes input and produces output of the following form:
   *  *Input: mark template subterm term (assumptions, conclusion).
   *  *Output: (assumptions, conclusion, mark, template, subterm, term).
   *)
  fun COMPOSE_ACST_TAC tactic1 tactic2 mark template subterm term (A, t) =
    let val (A', t', v', subterm', term') = tactic1 mark template subterm term (A, t) in
    let val acmtstv = tactic2 mark template subterm' term' (A', t') in
      COMPOSE_SUBGOALS_GOAL_TAC [acmtstv] (v' o hd)
    end end

  (* Applies tactic1 followed by tactic2.
   * -tactic1 does not change/return the mark nor the template and produces a
   *  single subgoal.
   * -tactic2 takes inputs and produces outputs of the following
   *  form:
   *  *Input: mark template subterm term (assumptions, conclusion).
   *  *Output: [(assumptions, conclusion, mark, template, subterm, term)].
   *)
  fun COMPOSE_ACSTS_TAC tactic1 tactic2 mark template subterm term (A, t) =
    let val (A1, t1, v1, subterm1, term1) = tactic1 mark template subterm term (A, t) in
    let val (acmtsts2, v2) = tactic2 mark template subterm1 term1 (A1, t1) in
      (acmtsts2, v1 o v2)
    end end

  (* Applies tactic1 followed by tactic2.
   * -tactic1 does not change/return the mark nor the template but returns
   *  subgoals containing an option in addition to assumptions, conclusion,
   *  subterm, term: [(assumptions, conclusion, subterm term, option)].
   * -tactic2 takes as first argument f applied on the option and then the mark,
   *  template, subterm, and the pair (assumptions, conclusion), and returns a
   *  list of assumptions, conclusion, mark, template, subterm, and term.
   *)
  fun COMPOSE_ACSTO_TAC tactic1 tactic2 others mark template subterm term (A, t) =
    let val (acstos, v) = tactic1 mark template subterm term (A, t) in
    let val acmtstvs = map (fn (a, c, s, t, opt) => tactic2 (others opt) mark template s t (a, c)) acstos in
      COMPOSE_SUBGOALS_GOAL_TAC acmtstvs v
    end end

  (* Applices tactic1, then tactic2, then tactic3, ...
   * Each tactic takes as arguments:
   * mark template subterm term (A, t)
   * Each tactic produces output:
   * ([(a1, c1, m1, tem1, s1, ter1), ..., (an, cn, mn, temn, sn, tern)], v)
   *)
  fun COMPOSE_ACMTSTS_TAC []                mark template subterm term (A, t) = ([(A, t, mark, template, subterm, term)], hd)
    | COMPOSE_ACMTSTS_TAC (tactic::tactics) mark template subterm term (A, t) =
      let val (acmtsts, v) = tactic mark template subterm term (A, t) in
      let val acmtstsvs = map (fn (a, c, m, tem, s, ter) => COMPOSE_ACMTSTS_TAC tactics m tem s ter (a, c)) acmtsts in
        COMPOSE_SUBGOALS_GOAL_TAC acmtstsvs v
      end end

  (* Prints time it takes to execute a tactic.
   *)
  fun BENCH_TAC tactic (A, t) =
    let val cputimer = Timer.startCPUTimer () in
    let val (subgoals, v) = tactic (A, t) in
    let val check = Timer.checkCPUTimer cputimer in
    let val _ = (print o concat) [Time.toString (#usr check), "\n\n"] in
      (subgoals, v)
    end end end end

  (* A u {asm_to_remove} ?- t
   * ------------------------
   *         A ?- t
   *)
  fun REMOVE_ASM_TAC asm_to_remove (old_A, old_t) =
    let fun remove_first_occurrence [] = []
          | remove_first_occurrence (asm::asms) =
            if Term.compare (asm, asm_to_remove) = EQUAL then
              asms
            else
              asm::(remove_first_occurrence asms) in
    let val new_A = remove_first_occurrence old_A
        val new_t = old_t
        val validation = fn thms => hd thms in
      ([(new_A, new_t)], validation)
    end end

  (* asm_eq: l = r, is in A.
   * mark: Variable denoting occurrences of l in t that should be replaced by r.
   * con_template: t with occurrences of mark denoting places that should be r.
   *
   *            A u {l = r} ?- t
   * -----------------------------------
   * A u {l = r} ?- con_template[r/mark]
   *)
  fun SUBST_CON_TAC asm_eq mark con_template (A, t) =
    let val (l, r) = dest_eq asm_eq in
    let val A' = A
        val t' = subst [mark |-> r] con_template
        val v' = fn thms =>
          (* A u {l = r} |- con_template[r/mark]
           * -----------------------------------
           * A u {l = r} |- con_template[l/mark]
           *)
          let val subgoal_achieving_thm = hd thms in
          let val goal_achieving_thm = SUBST [mark |-> (SYM o ASSUME) asm_eq] con_template subgoal_achieving_thm in
            goal_achieving_thm
          end end in
      ([(A', t')], v')
    end end

  (* asm_eq: l = r, is in A.
   * mark: Variable denoting occurrences of l in t that should be replaced by r.
   * asm_template: asm_to_rewrite but with occurrences of mark denoting places that should be r.
   * asm_to_rewrite: Assumption in A to be rewritten.
   *
   *            A u {l = r, asm} ?- t
   * -----------------------------------
   * A u {l = r, asm_template[r/mark]} ?- t
   *)
  fun SUBST_ASM_TAC asm_eq mark asm_template asm_to_rewrite (A, t) =
    let val (l, r) = dest_eq asm_eq in
    let val a' = subst [mark |-> r] asm_template in
    let val A' = a'::(filter (fn a => Term.compare (a, asm_to_rewrite) <> EQUAL) A)
        val t' = t
        val v' = fn thms =>
          (* A u {l = r, asm_template[r/mark]} |- t
           * --------------------------------------
           * A u {l = r, asm_template[l/mark]} |- t
           *)
          let val subgoal_achieving_thm = hd thms in                                                 (* A u {l = r, asm_template[r/mark]} |- t *)
          let val imp_thm = DISCH a' subgoal_achieving_thm                                           (* A u {l = r} |- asm_template[r/mark] ==> t *)
              val imp_template = mk_imp (asm_template, t) in                                         (* asm_template ==> t *)
          let val imp_achieving_thm = SUBST [mark |-> (SYM o ASSUME) asm_eq] imp_template imp_thm in (* A u {l = r} |- asm_template[l/mark] ==> t *)
          let val goal_achieving_thm = UNDISCH imp_achieving_thm in                                  (* A u {l = r, asm_template[l/mark]} |- t *)
            goal_achieving_thm
          end end end end in
      ([(A', t')], v')
    end end end

  (*  A ?- t
   * --------asm_eq: 'l = r', in A
   * A' ?- t'
   *
   * A' and t' are rewritten such that r is substituted for l, according to the
   * occurrences of mark in term_to_rewrite_template, where term_to_rewrite is
   * the assumption or conclusion to rewrite.
   *)
  fun SUBST_ASM_OR_CON_TAC asm_eq mark template term (A, t) =
    if Term.compare (term, t) = EQUAL then
      SUBST_CON_TAC asm_eq mark template (A, t)
    else
      SUBST_ASM_TAC asm_eq mark template term (A, t)

  (*  A ?- t
   * --------
   * A' ?- t'
   *
   * -subterm_eq_thm: 'B |- subterml = subtermr', B subset of A
   * -template[subterml/mark] = term
   * -subterm: 'subterml'
   * -term = '...subterml...' in A or is t, is rewritten to
   *  rewritten_term = '...subtermr...' in A' or is t.
   * -rewritten_subterm = 'subtermr'.
   *)
  fun RW_SUBTERM_TAC subterm_eq_thm mark template term (A, t) =
    let val subterm_eq = concl subterm_eq_thm
        val (subgoals1, v1) = ASSUME_TAC subterm_eq_thm (A, t) in
    let val (subgoals2, v2) = SUBST_ASM_OR_CON_TAC subterm_eq mark template term (hd subgoals1) in
    let val (subgoals3, v3) = REMOVE_ASM_TAC subterm_eq (hd subgoals2) in
    let val (A3, t3) = hd subgoals3
    (* rewritten_term and subterm are used to identify whether conclusion or not,
     * and to enable rewrites via chained equalities of the rewritten subterm:
     * ...subterm1... = ...subterm2... = ...subterm3 = ... = ... subtermn ...
     *)
        val rewritten_subterm = boolSyntax.rhs subterm_eq in
    let val rewritten_term = subst [mark |-> rewritten_subterm] template in
      (A3, t3, fn thm => v1 [v2 [v3 [thm]]], rewritten_subterm, rewritten_term)
    end end end end end

  (*  A ?- t
   * --------
   * A' ?- t'
   *
   * -subterm_eq_thm: 'B |- subterml = subtermr', B subset of A
   * -template[subtermr/mark] = term
   * -subterm: 'subtermr'
   * -term = '...subtermr...' in A or is t, is rewritten to
   *  rewritten_term = '...subterml...' in A' or is t.
   * -rewritten_subterm = 'subterml'.
   *)
  fun RW_SUBTERM_REFL_TAC subterm_eq_thm mark template term (A, t) =
    RW_SUBTERM_TAC (SYM subterm_eq_thm) mark template term (A, t)

  (* A u {l = r, term(subterm(l))} ?- t
   * ----------------------------------
   * A u {l = r, term(subterm(r))} ?- t
   *
   * or
   *
   * A u {l = r} ?- term(subterm(l))
   * -------------------------------with priority given to rewriting the conclusion.
   * A u {l = r} ?- term(subterm(r))
   *
   * The occurrence of subterm in term is denoted by template.
   *)
  fun SUBST_SUBTERM_TAC asm_eq mark template subterm term (A, t) =
    let val (l, r) = dest_eq asm_eq in
    let val subterm_mark = genvar_term l in
    let val subterm_eq_template = mk_eq (subterm, subst [l |-> subterm_mark] subterm) in
    let val subterm_eq_thm = SUBST [subterm_mark |-> ASSUME asm_eq] subterm_eq_template (REFL subterm) in
      RW_SUBTERM_TAC subterm_eq_thm mark template term (A, t)
    end end end end

  (* A u {l = r, term(subterm(r))} ?- t
   * ----------------------------------
   * A u {l = r, term(subterm(l))} ?- t
   *
   * or
   *
   * A u {l = r} ?- term(subterm(r))
   * -------------------------------
   * A u {l = r} ?- term(subterm(l))
   *
   * with priority given to rewriting the conclusion.
   *
   * The occurrence of subterm in term is denoted by template.
   *)
  fun SUBST_SUBTERM_REFL_TAC l_eq_r_asm mark template subterm term (A, t) =
    let val (l, r) = dest_eq l_eq_r_asm
        val (subgoals1, v1) = ASSUME_TAC ((SYM o ASSUME) l_eq_r_asm) (A, t) in
    let val (A1, t1) = hd subgoals1
        val r_eq_l_asm = mk_eq (r, l) in
    let val (A2, t2, v2, subterm2, term2) = SUBST_SUBTERM_TAC r_eq_l_asm mark template subterm term (A1, t1) in
    let val (subgoals3, v3) = REMOVE_ASM_TAC r_eq_l_asm (A2, t2) in
    let val (A3, t3) = hd subgoals3
        val subterm3 = subterm2
        val term3 = term2 in
      (A3, t3, fn thm => v1 [(v2 o v3) [thm]], subterm3, term3)
    end end end end end

  (****************************************************************************)
  (*End of general functions***************************************************)
  (****************************************************************************)







  val INTRO_TAC = REPEAT GEN_TAC THEN DISCH_TAC THEN SPLIT_ASM_TAC;

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

  (* Input: Term of the form '!X. l = r'.
   * Output: Theorem of the form '|- (!X. r = l) <==> (!X. l = r)'.
   *)
  fun qeq_eq_rqeq_conv qeq =                                                 (* '!X. l = r'                     *)
    let val (q, eq) = strip_forall qeq in                                    (* 'X', 'l = r'                    *)
    let val (l, r) = dest_eq eq in                                           (* (l, r)                          *)
    let val req = mk_eq (r, l) in                                            (* 'r = l'                         *)
    let val rqeq = list_mk_forall (q, req)                                   (* !X. r = l                       *)

        val qeq_hyp_qeq_thm = ASSUME qeq in                                  (* {!X. l = r} |- !X. l = r        *)
    let val qeq_hyp_eq_thm = SPEC_ALL qeq_hyp_qeq_thm in                     (* {!X. l = r} |- l = r            *)
    let val qeq_hyp_req_thm = SYM qeq_hyp_eq_thm in                          (* {!X. l = r} |- r = l            *)
    let val qeq_hyp_rqeq_thm = GENL q qeq_hyp_req_thm in                     (* {!X. l = r} |- !X. r = l        *)
    let val qeq_imp_rqeq_thm = DISCH qeq qeq_hyp_rqeq_thm                    (* |- {!X. l = r} ==> !X. r = l    *)

        val rqeq_hyp_rqeq_thm = ASSUME rqeq in                               (* {!X. r = l} |- !X. r = l        *)
    let val rqeq_hyp_req_thm = SPEC_ALL rqeq_hyp_rqeq_thm in                 (* {!X. r = l} |-     r = l        *)
    let val rqeq_hyp_eq_thm = SYM rqeq_hyp_req_thm in                        (* {!X. r = l} |-     l = r        *)
    let val rqeq_hyp_qeq_thm = GENL q rqeq_hyp_eq_thm in                     (* {!X. r = l} |- !X. l = r        *)
    let val rqeq_imp_qeq_thm = DISCH rqeq rqeq_hyp_qeq_thm in                (* |- {!X. r = l} ==> !X. l = r    *)

    let val thm = IMP_ANTISYM_RULE qeq_imp_rqeq_thm rqeq_imp_qeq_thm in      (* |- (!X. l = r) <==> (!X. r = l) *)
      thm
    end end end end end end end end end end end end end

  fun remove_first_occurrence asm_to_remove [] = []
    | remove_first_occurrence asm_to_remove (asm::asms) =
      if same_term asm_to_remove asm then
        asms
      else
        asm::(remove_first_occurrence asm_to_remove asms)

  (* 'A u {!X. l = r} ?- t'
   * ----------------------'!X. l = r'
   * 'A u {!X. r = l} ?- t'
   *)
  fun REFL_ASM_TAC qeq (A, t) =
    let val A_one_less_qeq = remove_first_occurrence qeq A in
    let val rqeq = let val (q, eq) = strip_forall qeq in let val (l, r) = dest_eq eq in list_mk_forall (q, mk_eq (r, l)) end end in
    let val A' = rqeq::A_one_less_qeq in
    let val subgoals = [(A', t)]
        val validation = fn thms =>
          let val subgoal_achieving_thm = hd thms in                                          (* A u {!X. r = l} |- t            *)
          let val rqeq_imp_thm = DISCH rqeq subgoal_achieving_thm                             (* A |- (!X. r = l) ==> t          *)
              val rewrite_thm = qeq_eq_rqeq_conv rqeq                                         (* |- (!X. r = l) <==> (!X. l = r) *)
              val illegal_markers = free_vars t
              val original_marker = mk_var ("marker", bool) in
          let val marker = gen_variant is_constname "" illegal_markers original_marker in
          let val template = mk_imp (marker, t) in                                            (* marker ==> t                    *)
          let val qeq_imp_thm = SUBST [marker |-> rewrite_thm] template rqeq_imp_thm in       (* A |- (!X. l = r) ==> t          *)
          let val thm = UNDISCH qeq_imp_thm in                                                (* A u {!X. l = r} |- t            *)
            thm
          end end end end end end in
      (subgoals, validation)
    end end end end

  (* A u {l = r} ?- t
   * ----------------
   * A u {r = l} ?- t
   *)
  fun REFL_ASM_EQ_TAC (A, t) =
    case List.find is_eq A of
      NONE => raise (mk_HOL_ERR "helper_tactics" "REFL_EQ_TAC" "No equality in among the assumptions.")
    | SOME eq => REFL_ASM_TAC eq (A, t)

  (****************************************************************************)
  (*Start of tactics that use one assumption to rewrite another assumption.****)
  (****************************************************************************)

  (* Performs backwards substitution to rewrite an assumption with another
   * assumption. Useful to produce the validation function when a goal has been
   * transformed from
   * A u {lhs = rhs, ...lhs...} ?- t
   * to
   * A u {...rhs...} ?- t or
   * A u {...rhs...} u {lhs = rhs} ?- t
   *
   * Inputs:
   * -A term rw_asm 'lhs = rhs'
   * -A term asm_rewritten '...rhs...'
   * -A theorem 'A u {...rhs...} |- t'
   *
   * Output: A theorem 'A u {lhs = rhs, ...lhs...} |- t'
   *
   * 1. A u {...rhs...} |- t
   * 2. A |- ...rhs... ==> t
   * 3. A |- (...rhs... ==> t)[lhs/rhs], given 'lhs = rhs |- rhs = lhs'
   *    =
   *    A u {lhs = rhs} |- ...lhs... ==> t
   *
   *   SUBST
   *     [marker |-> 'lhs = rhs |- rhs = lhs']
   *     '...mar... ==> t'
   *     'A |- ...rhs... ==> t'
   *   = 
   *   'A u {lhs = rhs} |- ...lhs... ===> t'
   *
   * 4. 'A {lhs = rhs, ...lhs...} |- t'
   *
   * Initialization variables for debuggin:
   * val rw_asm = “lhs = (rhs : 'a)”
   * val asm_rewritten = “f (rhs : 'a) : bool”
   * val thm = mk_thm ([“a0 : bool”, “a1 : bool”, asm_rewritten], “t : bool”)
   *)
  fun REV_ASM_RW_ASM_RULE eq rewritten (reverse_substitution_template, marker) thm =
    let val discharged_thm = DISCH rewritten thm
        val eq_thm = (SYM o ASSUME) eq
        val conclusion = concl thm in
    let val template = mk_imp (reverse_substitution_template, conclusion) in
    let val substituted_discharged_thm = SUBST [marker |-> eq_thm] template discharged_thm in
    let val substituted_thm = UNDISCH substituted_discharged_thm in
      substituted_thm
    end end end end

  (* Inputs:
   * -A term l.
   * -A term old.
   * -A list of variables illegal_markers.
   *
   * Outputs:
   * -A term old[marker/l]
   * -A term marker, where marker does not occur in old nor illegal_markers,
   *  meaning that subst (old[marker/l])[l/marker] = old.
   *)
  fun substitution_template l old illegal_markers =
    let val original_marker = mk_var ("marker", type_of l) in
    let val marker = gen_variant is_constname "" ((free_vars old) @ illegal_markers) original_marker in
      (subst [l |-> marker] old, marker)
    end end

  (* Inputs:
   * -keep: boolean.
   * -eq_asm: Term of the form 'lhs = rhs'
   * -asm_to_rw: Term 'a'.
   * -(A u {lhs = rhs, a}, t): Goal.
   *
   * Outputs:
   * -(A u {lhs = rhs, a[lhs/rhs], t): New goal
   * -validation function: Maps 'A u {lhs = rhs, a[lhs/rhs] ?- t' to 'A u {lhs = rhs, a} ?- t'
   *)
  fun ASM_RW_ASM_TAC keep eq_asm asm_to_rw (A, t) =
    let fun is_same t1 t2 = Term.compare (t1, t2) = EQUAL
        val (l, r) = dest_eq eq_asm in
    let val A'_without_asm = filter (fn a => not (is_same a asm_to_rw) andalso if keep then true else not (is_same a eq_asm)) A
        val asm_rewritten = subst [l |-> r] asm_to_rw
        val reverse_substitution_template_marker = substitution_template l asm_to_rw (free_vars t) in
    let val A' = asm_rewritten::A'_without_asm
        val validation = fn thms => REV_ASM_RW_ASM_RULE eq_asm asm_rewritten reverse_substitution_template_marker (hd thms) in
      ([(A', t)], validation)
    end end end

  (* A u {lhs = rhs, ...lhs...} ?- t
   * -------------------------------
   * A u {...rhs...} ?- t
   *)
  fun RM_ASM_RW_ASM_TAC eq_asm asm_to_rw = ASM_RW_ASM_TAC false eq_asm asm_to_rw

  (* A u {lhs = rhs, ...lhs...} ?- t
   * -------------------------------
   * A u {lhs = rhs, ...rhs...} ?- t
   *)
  fun KEEP_ASM_RW_ASM_TAC eq_asm asm_to_rw = ASM_RW_ASM_TAC true eq_asm asm_to_rw

  (*   A u {old = new} ?- t
   * ------------------------
   * A[new/old] ?- t[new/old]
   *)
  fun ASM_RW_OTHERS_TAC keep asm_eq (A, t) =
    let val (old, new) = dest_eq asm_eq in
    let val asms_to_rewrite = filter (fn other => not_same_term asm_eq other andalso free_in old other) A in
    let fun RW_ASMS_TAC [] = if keep then ALL_TAC else REMOVE_ASM_TAC asm_eq
          | RW_ASMS_TAC (asm_to_rewrite::asms_to_rewrite) = KEEP_ASM_RW_ASM_TAC asm_eq asm_to_rewrite THEN RW_ASMS_TAC asms_to_rewrite
        val RW_CON_TAC = SUBST_TAC [ASSUME asm_eq] in
      (RW_ASMS_TAC asms_to_rewrite THEN RW_CON_TAC) (A, t)
    end end end

  (* A u {...l..., ..., ...l..., l = r} ?- t
   * ---------------------------------------t rewritten to t' if l occurs in t
   * A u {...r..., ..., ...r...} ?- t'
   *)
  fun LRTAC (A, t) =
    let val eqs = filter is_eq A in
      case List.find (fn eq => exists (fn a => not (same_term eq a) andalso free_in (boolSyntax.lhs eq) a) (t::A)) eqs of
        NONE => raise (mk_HOL_ERR "helper_tactics" "LRTAC" "No equality among assumptions with a left hand side occurring in another assumption.")
      | SOME asm_eq => ASM_RW_OTHERS_TAC false asm_eq (A, t)
    end

  (* Rewrites if right hand side is not a let. *)
  fun NLLRTAC (A, t) =
    let val eqs = filter (fn asm => if is_eq asm then let val r = rhs asm in (not o is_let_scalar) r andalso (not o is_let_pair) r end else false) A in
      case List.find (fn eq => exists (fn a => not (same_term eq a) andalso free_in (boolSyntax.lhs eq) a) (t::A)) eqs of
        NONE => raise (mk_HOL_ERR "helper_tactics" "LRTAC" "No equality among assumptions with a left hand side occurring in another assumption.")
      | SOME asm_eq => ASM_RW_OTHERS_TAC false asm_eq (A, t)
    end

  (*      [v1 = e1, ..., vn = en] @ A |- t
   * --------------------------------------------
   * A[e1/v1, ..., en/vn] |- t[e1/v1, ..., en/vn]
   *)
  fun NLRTAC n (A, t) =
    if n = 0 then
      ALL_TAC (A, t)
    else
      let val nasms = List.take (A, n) in
        if all is_eq nasms then
          let fun tactic [] = ALL_TAC
                | tactic (eq::eqs) = (ASM_RW_OTHERS_TAC false eq) THEN tactic eqs in
            tactic nasms (A, t)
          end
        else
          raise (mk_HOL_ERR "helper_tactics" "NLRTAC" (concat ["The first ", Int.toString n, " assumptions are not equalities."]))
      end

  (* A u {...l..., ..., ...l..., l = r} ?- t
   * ---------------------------------------t rewritten to t' if l occurs in t
   * A u {...r..., ..., ...r...} ?- t'
   *)
  fun ASM_LR_RW_OTHERS_KEEP_TAC (A, t) =
    let val eqs = filter is_eq A in
      case List.find (fn eq => exists (fn a => not (same_term eq a) andalso free_in (boolSyntax.lhs eq) a) (t::A)) eqs of
        NONE => raise (mk_HOL_ERR "helper_tactics" "ASM_LR_RW_OTHERS_KEEP_TAC" "No equality among assumptions with a left hand side occurring in another assumption.")
      | SOME asm_eq => ASM_RW_OTHERS_TAC true asm_eq (A, t)
    end

  val ALL_LRTAC = REPEAT LRTAC

  val ALL_ASM_LR_RW_OTHERS_KEEP_TAC = REPEAT ASM_LR_RW_OTHERS_KEEP_TAC

  (* A u {...r..., ..., ...r..., l = r} ?- t
   * ---------------------------------------t rewritten to t' if r occurs in t
   * A u {...l..., ..., ...l...} ?- t'
   *)
  fun RLTAC (A, t) =
    let val eqs = filter is_eq A in
      case List.find (fn eq => exists (fn a => not (same_term eq a) andalso free_in (boolSyntax.rhs eq) a) (t::A)) eqs of
        NONE => raise (mk_HOL_ERR "helper_tactics" "RLTAC" "No equality among assumptions with a right hand side occurring in another assumption.")
      | SOME asm_eq =>
        let val reflected_asm_eq = let val (l, r) = dest_eq asm_eq in mk_eq (r, l) end in
          (REFL_ASM_TAC asm_eq THEN ASM_RW_OTHERS_TAC false reflected_asm_eq) (A, t)
        end
    end

  (*      [e1 = v1, ..., en = vn] @ A |- t
   * --------------------------------------------
   * A[e1/v1, ..., en/vn] |- t[e1/v1, ..., en/vn]
   *)
  fun NRLTAC n (A, t) =
    if n = 0 then
      ALL_TAC (A, t)
    else
      let val nasms = List.take (A, n) in
        if all is_eq nasms then
          let fun tactic [] = ALL_TAC
                | tactic (eq::eqs) =
                  let val reflected_eq = let val (l, r) = dest_eq eq in mk_eq (r, l) end in
                    (REFL_ASM_TAC eq THEN ASM_RW_OTHERS_TAC false reflected_eq) THEN tactic eqs
                  end in
            tactic nasms (A, t)
          end
        else
          raise (mk_HOL_ERR "helper_tactics" "NRLTAC" (concat ["The first ", Int.toString n, " assumptions are not equalities."]))
      end

  fun ASM_RL_RW_OTHERS_KEEP_TAC (A, t) =
    let val eqs = filter is_eq A in
      case List.find (fn eq => exists (fn a => not (same_term eq a) andalso free_in (boolSyntax.rhs eq) a) (t::A)) eqs of
        NONE => raise (mk_HOL_ERR "helper_tactics" "ASM_RL_RW_OTHERS_KEEP_TAC" "No equality among assumptions with a right hand side occurring in another assumption.")
      | SOME asm_eq =>
        let val reflected_asm_eq = let val (l, r) = dest_eq asm_eq in mk_eq (r, l) end in
          (REFL_ASM_TAC asm_eq THEN ASM_RW_OTHERS_TAC true reflected_asm_eq THEN REFL_ASM_TAC reflected_asm_eq) (A, t)
        end
    end

  val ALL_RLTAC = REPEAT RLTAC

  val ALL_ASM_RL_RW_OTHERS_KEEP_TAC = REPEAT ASM_RL_RW_OTHERS_KEEP_TAC

  (* Inputs:
   * -keep: boolean.
   * -eq_asm: Term of the form 'lhs = rhs'
   * -asm_to_rw: Term 'a'.
   * -(A u {lhs = rhs, a}, t): Goal.
   *
   * Outputs:
   * -(A u {lhs = rhs, a[rhs/lhs], t): New goal
   * -validation function: Maps 'A u {lhs = rhs, a[rhs/lhs] ?- t' to 'A u {lhs = rhs, a} ?- t'
   *)
  fun ASM_RHS_RW_ASM_TAC keep eq_asm asm_to_rw (A, t) =
    let val (subgoals1, validation1) = REFL_ASM_TAC eq_asm (A, t)
        val reflected_eq_asm = mk_eq (boolSyntax.rhs eq_asm, boolSyntax.lhs eq_asm) in
    let val (subgoals2, validation2) = ASM_RW_ASM_TAC true reflected_eq_asm asm_to_rw (hd subgoals1) in
    let val (subgoals3, validation3) = REFL_ASM_TAC reflected_eq_asm (hd subgoals2) in
    let val (A', t') = hd subgoals3
        fun is_same t1 t2 = Term.compare (t1, t2) = EQUAL in
    let val A'_without_asm = filter (fn a => not (is_same a asm_to_rw) andalso if keep then true else not (is_same a eq_asm)) A' in
      ([(A'_without_asm, t')], fn thms => validation1 [validation2 [validation1 thms]])
    end end end end end

  (* A u {lhs = rhs, ...rhs...} ?- t
   * -------------------------------
   * A u {...lhs...} ?- t
   *)
  fun RM_RHS_ASM_RW_ASM_TAC eq_asm asm_to_rw = ASM_RHS_RW_ASM_TAC false eq_asm asm_to_rw

  (* A u {lhs = rhs, ...rhs...} ?- t
   * -------------------------------
   * A u {lhs = rhs, ...lhs...} ?- t
   *)
  fun KEEP_RHS_ASM_RW_ASM_TAC eq_asm asm_to_rw = ASM_RHS_RW_ASM_TAC true eq_asm asm_to_rw





  fun reverse_rewrite_hyps subgoal_thm [] _ = subgoal_thm
    | reverse_rewrite_hyps subgoal_thm _ [] = subgoal_thm
    | reverse_rewrite_hyps subgoal_thm (new_assumption::new_assumptions) (NONE::rev_rw_thms) =
      reverse_rewrite_hyps subgoal_thm new_assumptions rev_rw_thms
    | reverse_rewrite_hyps subgoal_thm (new_assumption::new_assumptions) ((SOME rev_rw_thm)::rev_rw_thms) =
      let val mark = genvar bool in
      let val imp_thm = DISCH new_assumption subgoal_thm
          val template = mk_imp (mark, concl subgoal_thm) in
      let val rw_imp_thm = SUBST [mark |-> rev_rw_thm] template imp_thm in
      let val subgoal_thm = UNDISCH rw_imp_thm in
        reverse_rewrite_hyps subgoal_thm new_assumptions rev_rw_thms
      end end end end

  fun rewrite_hyps_t to_left_or_right keep qeq_thm [] t = (
      let val t_rev_rw_thm = SYM (REWRITE_CONV [qeq_thm] t) in
      let val t' = (lhs o concl) t_rev_rw_thm in
        ([], [], t', SOME t_rev_rw_thm)
      end end
      handle _ => (* REWRITE_CONV generated NO CHANGE exception, meaning that t was not rewritten and is unchanged. *)
      ([], [], t, NONE))
    | rewrite_hyps_t to_left_or_right keep qeq_thm (assumption::assumptions) t =
      let val (new_assumptions, assumptions_rev_rw_thms, new_t, t_rev_rw_thm) = rewrite_hyps_t to_left_or_right keep qeq_thm assumptions t
          val rw_eq = if to_left_or_right then concl qeq_thm else (concl o GSYM) qeq_thm in
        if not_same_term rw_eq assumption then
          let val assumption_rev_rw_thm = SYM (REWRITE_CONV [qeq_thm] assumption) in
          let val new_assumption = (lhs o concl) assumption_rev_rw_thm in
            (new_assumption::new_assumptions, (SOME assumption_rev_rw_thm)::assumptions_rev_rw_thms, new_t, t_rev_rw_thm)
          end end
          handle _ => (* REWRITE_CONV generated NO CHANGE exception, meaning that assumption was not rewritten and is unchanged. *)
          (assumption::new_assumptions, NONE::assumptions_rev_rw_thms, new_t, t_rev_rw_thm)
        else if keep then
          (assumption::new_assumptions, NONE::assumptions_rev_rw_thms, new_t, t_rev_rw_thm)
        else
          (* Removes the term equation used for rewriting the other terms. *)
          (new_assumptions, assumptions_rev_rw_thms, new_t, t_rev_rw_thm)
      end

  fun find_rewrite_effect source_tactic to_left_or_right keep A t [] =
      raise (mk_HOL_ERR "helper_tactics" source_tactic "No equation among assumptions had rewrite effect.")
    | find_rewrite_effect source_tactic to_left_or_right keep A t (qeq::qeqs) =
      let val qeq_thm = if to_left_or_right then ASSUME qeq else (GSYM o ASSUME) qeq in
      let val (A', A_rev_rw_thms, t', t_rev_rw_thm) = rewrite_hyps_t to_left_or_right keep qeq_thm A t in
        if exists isSome A_rev_rw_thms orelse isSome t_rev_rw_thm then
          (A', A_rev_rw_thms, t', t_rev_rw_thm)
        else
          find_rewrite_effect source_tactic to_left_or_right keep A t qeqs
      end end

  fun reverse_rewrite_conclusion subgoal_thm NONE = subgoal_thm
    | reverse_rewrite_conclusion subgoal_thm (SOME rev_rw_thm) =
      let val mark = genvar bool in
      let val template = mark in
      let val goal_thm = SUBST [mark |-> rev_rw_thm] template subgoal_thm in
        goal_thm
      end end end

  fun QEQ_RW_ASM_TAC source_tactic to_left_or_right keep (A, t) =
    let val qeqs = filter (is_eq o #2 o strip_forall) A in
      if (not o null) qeqs then
        let val (A', A_rev_rw_thms, t', t_rev_rw_thm) = find_rewrite_effect source_tactic to_left_or_right keep A t qeqs in
        let val validation = fn subgoal_thms =>
              let val subgoal_thm = hd subgoal_thms in
              let val hyps_goal_thm = reverse_rewrite_hyps subgoal_thm A' A_rev_rw_thms in
              let val goal_thm = reverse_rewrite_conclusion hyps_goal_thm t_rev_rw_thm in
                goal_thm
              end end end in
          ([(A', t')], validation)
        end end
      else
        raise (mk_HOL_ERR "helper_tactics" source_tactic "No equation among assumptions.")
    end

  (* A u {...L X..., ...L Y...} u {!V. L V = R V} ?- ...L Z...
   * ---------------------------------------------------------
   * A u {...R X..., ...R Y...} ?- ...R Z...
   *)
  fun QLRTAC (A, t) =
    let val source_tactic = "QLRTAC"
        val to_left_or_right = true in
      QEQ_RW_ASM_TAC source_tactic to_left_or_right false (A, t)
    end

  (* A u {...R X..., ...R Y...} u {!V. L V = R V} ?- ...R Z...
   * ---------------------------------------------------------
   * A u {...L X..., ...L Y...} ?- ...L V...
   *)
  fun QRLTAC (A, t) =
    let val source_tactic = "QRLTAC"
        val to_left_or_right = false in
      QEQ_RW_ASM_TAC source_tactic to_left_or_right false (A, t)
    end



  (* A u {...L X..., ...L Y...} u {!V. L V = R V} ?- ...L Z...
   * ---------------------------------------------------------
   * A u {...R X..., ...R Y...} u {!V. L V = R V} ?- ...R Z...
   *)
  fun QEQ_RW_LHS_ASM_KEEP_TAC (A, t) =
    let val source_tactic = "QEQ_RW_LHS_ASM_KEEP_TAC"
        val to_left_or_right = true in
      QEQ_RW_ASM_TAC source_tactic to_left_or_right true (A, t)
    end

  (* A u {...R X..., ...R Y...} u {!V. L V = R V} ?- ...R Z...
   * ---------------------------------------------------------
   * A u {...L X..., ...L Y...} u {!V. L V = R V} ?- ...L V...
   *)
  fun QEQ_RW_RHS_ASM_KEEP_TAC (A, t) =
    let val source_tactic = "QEQ_RW_RHS_ASM_KEEP_TAC"
        val to_left_or_right = false in
      QEQ_RW_ASM_TAC source_tactic to_left_or_right true (A, t)
    end





  fun rw_hyp rw_thms refl_rw_thms hyp =
    let val (hyp, rev_eq_thm) =
      let val eq_thm = REWRITE_CONV rw_thms hyp in ((rhs o concl) eq_thm, SOME (SYM eq_thm)) end
      handle _ =>
      let val eq_thm = REWRITE_CONV refl_rw_thms hyp in ((rhs o concl) eq_thm, SOME (SYM eq_thm)) end
      handle _ =>
      (hyp, NONE) in
      (hyp, rev_eq_thm)
    end

  fun rw_hyps rw_thms refl_rw_thms [] = ([], [])
    | rw_hyps rw_thms refl_rw_thms (hyp::hyps) =
      let val (new_hyps, rev_eq_thms) = rw_hyps rw_thms refl_rw_thms hyps in
      let val (new_hyp, rev_eq_thm) = rw_hyp rw_thms refl_rw_thms hyp in
        (new_hyp::new_hyps, rev_eq_thm::rev_eq_thms)
      end end

  (* Rewrites hypothese with rw_thm, which can contain multiple rewrite theorems
   * in a conjunction. Can remove conjuncts if rewrites contain opposite boolean
   * value.
   *)
  fun RW_HYPS_NO_SPLIT_TAC rw_thm (A, t) =
    let val rw_thms = CONJUNCTS rw_thm in
    let val refl_rw_thms = map GSYM rw_thms in
    let val (A', rev_eq_thms) = rw_hyps rw_thms refl_rw_thms A in
    let val validation = fn subgoal_thms =>
            let val subgoal_thm = hd subgoal_thms in
            let val goal_thm = reverse_rewrite_hyps subgoal_thm A' rev_eq_thms in
              goal_thm
            end end in
      ([(A', t)], validation)
    end end end end

  fun RW_HYPS_TAC rw_thm = RW_HYPS_NO_SPLIT_TAC rw_thm THEN SPLIT_ASM_TAC

  (****************************************************************************)
  (*End of tactics that use one assumption to rewrite another assumption.******)
  (****************************************************************************)


  (* A u {P, P ==> Q} ?- t
   * ---------------------ADTAC if remove_asm = true
   *     A u {Q} ?- t
   *
   * A u {P, P ==> Q} ?- t
   * ---------------------ADTAC if remove_asm = false
   *   A u {P, Q} ?- t
   *)
  fun ADTAC remove_asm (A, t) =
    let val imp = List.find (fn imp => is_imp imp andalso exists ((same_term o #1 o dest_imp) imp) A) A in
      if isSome imp then
        let val imp = valOf imp in
        let val ant = (#1 o dest_imp) imp in
          (ASSUME_TAC ((UNDISCH o ASSUME) imp) THEN
           REMOVE_ASM_TAC imp THEN
           (if remove_asm then REMOVE_ASM_TAC ant else ALL_TAC)) (A, t)
        end end
      else
        raise (mk_HOL_ERR "helper_tactics" "ADTAC" "No implication with antecedent among assumptions.")
    end




  (* Finds matching from cs to A where only instantiatable variables may be
   * matched.
   *
   * Algorithm:
   * For each antecedent conjunct, check if it matches an assumption:
   * -If so merge the new matching with the current matching.
   * -If they cannot be merged, check if the current antecedent conjunct matches
   *  another assumption until the new matching is consistent with the current
   *  matching. If no matching works for the current conjunct, backtrack and try
   *  to match another assumption.
   *)
  fun find_matchings instantiatable_variables term_matching type_matching A [] = SOME (term_matching, type_matching)
    | find_matchings instantiatable_variables term_matching type_matching A (c::cs) =
      find_matching  instantiatable_variables term_matching type_matching A c cs A
  and find_matching  instantiatable_variables term_matching type_matching A c cs [] = NONE
    | find_matching  instantiatable_variables term_matching type_matching A c cs (asm::asms) =
      case find_explicit_variable_instantiation instantiatable_variables c asm of
        NONE =>                                                      (* No match with current asm: Try next asm. *)
        find_matching instantiatable_variables term_matching type_matching A c cs asms
      | SOME (term_m, type_m) =>
        case merge_term_matchings term_m term_matching of
          NONE =>                                                    (* Inconsistent with current match: Try next asm. *)
          find_matching instantiatable_variables term_matching type_matching A c cs asms
        | SOME merged_term_matching =>
          case merge_type_matchings type_m type_matching of
            NONE =>                                                  (* Inconsistent with current match: Try next asm. *)
            find_matching instantiatable_variables term_matching type_matching A c cs asms
          | SOME merged_type_matching =>
            (* Current conjunct matches current assumption, and consistent with current matchings: Continue with next conjunct. *)
            case find_matchings instantiatable_variables merged_term_matching merged_type_matching A cs of
              NONE =>                                                (* Later match failed: Back track and try next asm. *)
              find_matching instantiatable_variables term_matching type_matching A c cs asms
            | SOME (final_term_matching, final_type_matching) =>     (* Complete matching found: Return complete matching. *)
              SOME (final_term_matching, final_type_matching)

  (* Inputs:
   * -A: A list of terms.
   * -lemma: A theorem of the form 'B |- !X. C1 X /\ ... /\ Cn X ==> C X'
   *
   * Output:
   * -NONE: If X and type variables of lemma cannot be instantiated to X' such that each Ci X' is in A.
   * -SOME (X', T'): Each 'subst X' Ci' is in A with T' being a corresponding type instantiation.
   *)
  fun compute_lemma_instantiation A lemma =
    let val (qvars, imp) = (strip_forall o concl) lemma in
    let val conjs = (strip_conj o #1 o dest_imp) imp in
      find_matchings qvars [] [] A conjs
    end end

  (* Adds P v1...vn w1...wm to the assumption list given a lemma of the form
   * 'B |- !x1...xn. C1 x1..xn /\ ... /\ Cm x1..xn ==> P x1...xn w1...wm', and
   * where B and Ci v1...vn are assumptions in the assumption list.
   *)
  fun INST_IMP_TAC lemma =
    let fun tactic lemma (A, t) =
      case compute_lemma_instantiation A lemma of
        NONE => raise (mk_HOL_ERR "helper_tactics" "INST_IMP_TAC" "Could not instantiate lemma to match hypotheses.")
      | SOME term_type_matching =>
      let val instantiated_lemma = INST_TY_TERM term_type_matching (SPEC_ALL lemma) in
      let val lemma_thm = CONJ_ANT_TO_HYP instantiated_lemma in
        (ASSUME_TAC lemma_thm THEN SPLIT_ASM_TAC) (A, t)
      end end in
      tactic lemma ORELSE
      tactic (GSYM lemma)
    end

  fun INST_IMP_ASM_TAC (A, t) =
    case List.find (is_imp o #2 o strip_forall) A of
      NONE => raise (mk_HOL_ERR "helper_tactics" "INST_IMP_ASM_TAC" "No universally quantified implication nor unquantified implication among assumptions.\n")
    | SOME imp_asm =>
      let val (subgoals1, v1) = INST_IMP_TAC (ASSUME imp_asm) (A, t) in
      let val (A1, t1) = hd subgoals1 in
      let val A2 = filter (not_same_term imp_asm) A1 in
        ([(A2, t1)], v1)
      end end end

  (* Adds 'P v1...vn w1...wm' to the assumption list given a lemma of the form
   * '|- !x1...xn. C1 x1..xn /\ ... /\ Cm x1..xn ==> P x1...xn w1...wm', and
   * where there are assumptions in the assumption list satisfying some of
   * 'Ci v1...vn', and where the other 'Cj x1...xn' are instantiated such that
   * REWRITE_RULE [] can simplify them to true which is removed from the
   * conjuncts of the assumption of the resulting instantiated implication
   *)
  fun PART_INST_IMP_TAC lemma (asl, con) =
    let fun partial_match_lemma_to_assumptions asl [] = []
          | partial_match_lemma_to_assumptions asl (lemma_assumption::lemma_assumptions) =
          let val matches = map (fn assumption => SOME (match_term lemma_assumption assumption) handle _ => NONE) asl in
            case List.find (fn NONE => false | SOME match => true) matches of
              NONE => partial_match_lemma_to_assumptions asl lemma_assumptions
            | SOME NONE => partial_match_lemma_to_assumptions asl lemma_assumptions
            | SOME (SOME match) => match::(partial_match_lemma_to_assumptions asl lemma_assumptions)
          end
        val stripped_lemma = SPEC_ALL lemma in
    let val lemma_assumption_conjuncts = (strip_conj o #1 o dest_imp o concl) stripped_lemma in
    let val lemma_goal_match_term_types = partial_match_lemma_to_assumptions asl lemma_assumption_conjuncts in

    let val match_terms_types = unzip lemma_goal_match_term_types in
    let val (match_terms, match_types) =
      (fn (match_terms, match_types) => (flatten match_terms, flatten match_types)) match_terms_types in
    let val instantiated_lemma = INST_TY_TERM (match_terms, match_types) stripped_lemma in

    let val simplified_instantiated_lemma = REWRITE_RULE [] instantiated_lemma in
    let val lemma_thm = CONJ_ANT_TO_HYP simplified_instantiated_lemma in
      (ASSUME_TAC lemma_thm THEN SPLIT_ASM_TAC) (asl, con)
    end end end end end end end end

  (* Adds 't v1...vn' to the assumption list given a lemma of the form
   * '|- !x1...xn. t x1..xn', where instantiation_strings contains the string
   * names in order of v1...vn, with v1...vn type instantiated to match the
   * current assumption list and goal.
   *)
  fun ADD_INST_TAC lemma instantiation_strings (asl, con) =
    let fun is_equal_string string term = term_to_string term = string in
    let fun has_equal_string terms string = has_terms_subterm_property (is_equal_string string) terms in
    let val instantiation_term_options =
      map (fn instantiation_string => has_equal_string (con::asl) instantiation_string) instantiation_strings in
    let val instantiation_terms =
      map (fn NONE => raise (mk_HOL_ERR "helper_tactics" "ADD_INST_TAC" "No term with given name.")
            | SOME (mark, template, subterm_with_property, term) => subterm_with_property) instantiation_term_options
        val quantification_variables = (#1 o strip_forall o concl) lemma in
    let val quantification_instantiations = zip quantification_variables instantiation_terms in
    let val match_term_types = map (fn (var, ins) => match_term var ins) quantification_instantiations in
    let val match_terms_types = unzip match_term_types in
    let val (match_terms, match_types) =
      (fn (match_terms, match_types) => (flatten match_terms, flatten match_types)) match_terms_types in
    let val instantiated_lemma = INST_TY_TERM (match_terms, match_types) (SPEC_ALL lemma) in
      (ASSUME_TAC instantiated_lemma) (asl, con)
    end end end end end end end end end

  fun MATCH_MP_ASM_TAC term = PAT_X_ASSUM term (fn thm => MATCH_MP_TAC thm)

  fun SPEC_ASM_TAC term (asl, con) =
    let fun find_for_all [] = NONE
        |   find_for_all (term::terms) = if is_forall term then SOME term else find_for_all terms
        fun quantified_type for_all_term = (type_of o #1 o dest_forall) for_all_term in
    let val spec_term = find_for_all asl in
      case spec_term of
        NONE => FAIL_TAC "No universally quantified formula!\n" (asl, con)
      | SOME for_all_term =>
        let val quantification_type = quantified_type for_all_term
            val type_term = type_of term in
        let val type_inst_term = Term.inst [type_term |-> quantification_type] term
            val for_all_thm = ASSUME for_all_term in
        let val spec_thm = Drule.ISPEC type_inst_term for_all_thm in
          PAT_X_ASSUM for_all_term (fn thm => ASSUME_TAC spec_thm) (asl, con)
        end end end
    end end

  fun INST_EXIST_ASM_TAC term =
    let fun tactic first_iteration xthm (asl, con) =
      let val nvar_inst_body = instantiate_exist ((#2 o dest_thm) xthm) (free_varsl (con::asl)) in
        case nvar_inst_body of
          NONE =>
          if first_iteration then
            (ASSUME_TAC xthm THEN FAIL_TAC "No existential assumption!\n") (asl, con) (*ASSUME_TAC puts back removed term*)
          else
            ASSUME_TAC xthm (asl, con) (* All existentials have been instantiated, terminate. *)
        | SOME (new_var, _, inst_body) =>
          let val new_goal = (inst_body::asl, con) in
          let val (gl, exists_eliminations) = PAT_X_ASSUM inst_body (fn thm => tactic false thm) new_goal
              val exists_elimination = (CHOOSE (new_var, xthm)) in
          let val proof = exists_elimination o exists_eliminations in
            (gl, proof)
          end end end
      end
    in
      PAT_X_ASSUM term (fn thm => tactic true thm)
    end

  val AXTAC = REPEAT (INST_EXIST_ASM_TAC “?x. P”) THEN SPLIT_ASM_TAC

  fun INST_EXISTS_TAC (asl, con) = 
    if (not o is_exists) con then
      fail (print "Not existential goal.\n")
    else
      let val quantified_variables = (#1 o strip_exists) con in
      let fun tactic [] = ALL_TAC
            | tactic (variable::variables) = EXISTS_TAC variable THEN tactic variables in
        tactic quantified_variables (asl, con)
      end end

  fun INST_EXISTS_NAMES_TAC names (asl, con) =
    if (not o is_exists) con then
      fail (print "The goal does not have an existential conclusion.\n")
    else
      let val variable_types = map type_of ((#1 o strip_exists) con) in
      let val name_types = zip names (List.take (variable_types, length names))
          fun tactic [] = ALL_TAC
            | tactic ((name_type)::name_types) = EXISTS_TAC (mk_var name_type) THEN tactic name_types in
        tactic name_types (asl, con)
      end end

  (* Transforms a goal of the form A |- ?x1...xn. t to A |- t such that x1...xn
   * are substituted with v1...vn and t[v1...vn/x1...xn] is in A.
   *)
  fun INST_EXISTS_WITH_ASM_TAC (asl, con) =
    if (not o is_exists) con then
      fail (print "The goal is not existentially quantified.\n")
    else
      let val (xvariables, formula) = strip_exists con in
      let fun match_formula [] = NONE
            | match_formula (assumption::assumptions) =
            SOME (match_term formula assumption) handle _ => match_formula assumptions in
      let val match_variables = case match_formula asl of
                NONE => fail (print "Could not match existential formula to an assumption.\n")
              | SOME (match_variables, _) => match_variables
          fun match_xvariable xvariable [] = xvariable (* Quantified variable does not need to be changed. *)
            | match_xvariable xvariable ({redex = variable, residue = xinstantiation}::matches) =
            if Term.compare (xvariable, variable) = EQUAL then
              xinstantiation
            else
              match_xvariable xvariable matches in
      let fun match_xvariables [] = []
            | match_xvariables (xvariable::xvariables) =
            (match_xvariable xvariable match_variables)::(match_xvariables xvariables) in
      let val xinstantiations = match_xvariables xvariables
          fun tactic [] = ALL_TAC
            | tactic (xinstantiation::xinstantiations) = (EXISTS_TAC xinstantiation) THEN (tactic xinstantiations) in
        tactic xinstantiations (asl, con)
      end end end end end

  (* 'A ?- ?x. x = y' or 'A ?- ?x. y = x'
   * ==>
   * 'A ?- y = y
   *)
  fun INST_SCALAR_EQ_EXISTS_TAC (A, t) =
    let val (xvar, xeq) = dest_exists t in
    let val (l, r) = dest_eq xeq in
      if Term.compare(l, xvar) = EQUAL then (* Left hand side contains the existentially quantified variable. *)
        EXISTS_TAC r (A, t)
      else (* Right hand side contains the existentially quantified variable. *)
        EXISTS_TAC l (A, t)
    end end

  val INST_VECTOR_EQ_EXISTS_TAC =
    let fun tactic (A, t) =
      if (not o is_exists) t then
        raise (mk_HOL_ERR "helper_tactics" "INST_VECTOR_EQ_EXISTS_TAC" "Conclusion is not an existentially quantified formula.\n")
      else
        let val (xvars, xeq) = strip_exists t in
        let val xvar = hd xvars
            val (l, r) = dest_eq xeq in
        let val lhs_xvars = pairSyntax.strip_pair l
            val rhs_ivars = pairSyntax.strip_pair r in
        let val eq_xvars = zip lhs_xvars rhs_ivars in
          if var_occurs xvar l then (* Left hand side contains existentially quantified variable. *)
            case List.find (fn (l, _) => Term.compare (l, xvar) = EQUAL) eq_xvars of
              NONE => raise (mk_HOL_ERR "helper_tactics" "INST_EQ_EXISTS" "Cannot happen.\n")
            | SOME (_, rv) => EXISTS_TAC rv (A, t)
          else (* Right hand side contains existentially quantified variable. *)
            case List.find (fn (_, r) => Term.compare (r, xvar) = EQUAL) eq_xvars of
              NONE => raise (mk_HOL_ERR "helper_tactics" "INST_EQ_EXISTS" "Cannot happen.\n")
            | SOME (lv, _) => EXISTS_TAC lv (A, t)
    end end end end in
      tactic THEN REPEAT tactic
    end

  (* 'A ?- ?XY. XY' = X'Y
   * --------------------
   * 'A ?- X'Y' = X'Y', where X, X', Y, X' are vectors of variables. Some
   * existentially quantified variables occur on the left hand side (X and other
   * on the right hand side (Y), and may be interleaved arbitrarily in the sense
   * that not all left hand side variables must occur first in the quantification
   * (X) and then all right hand side variables (Y).
   *)
  fun INST_EQ_EXISTS_TAC (A, t) =
    if (not o is_exists) t then
      raise (mk_HOL_ERR "helper_tactics" "INST_EQ_EXISTS" "Conclusion is not an existentially quantified formula.\n")
    else
      let val (xvars, xbody) = strip_exists t in
        if is_eq xbody then
          let val (l, r) = dest_eq xbody in
            if length xvars = 1 then
              INST_SCALAR_EQ_EXISTS_TAC (A, t)
            else
              INST_VECTOR_EQ_EXISTS_TAC (A, t)
          end
        else
          raise (mk_HOL_ERR "helper_tactics" "INST_EQ_EXISTS" "Conclusion is not an existentially quantified equality.\n")
      end

  (* A ?- ?x. t(x) = t(t1)    A ?- ?x. t(x) = t(t1)
   * --------------------- or ---------------------
   *         -                         -
   *)
  fun EXISTS_PAT_TAC (A, t) =
    let val (xvar, eq) = dest_exists t in
    let val (l, r) = dest_eq eq in
    let val matching = #1 (if is_in (free_vars r) xvar then match_term r l else match_term l r) in
    let val inst = case List.find (fn {redex = from, residue = to} => same_term from xvar) matching of
        NONE => raise (mk_HOL_ERR "helper_tactics" "EXISTS_PAT_TAC" "Conclusion not of the form ?x.t[x] = t[t1] or ?x.t[t1] = t[x].")
      | SOME {redex = from, residue = to} => to in
      (EXISTS_TAC inst THEN REWRITE_TAC []) (A, t)
    end end end end


  (* Given var, returns |- !P. ~?var. P var = !var. ~P var
   *)
  fun rename_not_exists_eq_forall_not var =
    let val type_variable = (hd o type_vars o type_of o #1 o dest_forall o concl) boolTheory.NOT_EXISTS_THM in
    let val thm = (INST_TY_TERM ([], [type_variable |-> type_of var]) boolTheory.NOT_EXISTS_THM) in
    let val (l, r) = (dest_eq o concl o SPEC_ALL) thm in
    let val body = (rator o #2 o dest_exists o dest_neg) l in
    let val renamed_body = mk_comb (body, var) in
    let val renamed_l = (mk_neg o mk_exists) (var, renamed_body)
        val renamed_r = mk_forall (var, (mk_neg renamed_body)) in
    let val renamed_term = mk_forall (body, mk_eq (renamed_l, renamed_r)) in
    let val renamed_thm = PROVE_HYP thm (ASSUME renamed_term) in
      renamed_thm
    end end end end end end end end

  (* A u {~?x. P x} ?- t
   * -------------------
   * A u {!x. ~P x} ?- t
   *)
  fun ASM_NOT_EXISTS_TO_FORALL_NOT_TAC (A, t) =
    let fun is_not_exists term = if is_neg term then (is_exists o dest_neg) term else false in
    let val not_exists_body =
      case List.find is_not_exists A of
        NONE => raise (mk_HOL_ERR "helper_tactics" "ASM_NOT_EXISTS_TO_FORALL_NOT_TAC" "No negated existentially quantified assumption.")
      | SOME not_exists_body => not_exists_body in
    let val (var, body) = (dest_exists o dest_neg) not_exists_body in
    let val abs_var_body = mk_abs (var, body) in
    let val abs_var_body_app_var = mk_comb (abs_var_body, var) in
    let val body_eq_app_abs_thm = SYM (BETA_CONV abs_var_body_app_var) in
    let val not_exists_abs_thm = ONCE_REWRITE_RULE [GEN_ALL body_eq_app_abs_thm] (ASSUME not_exists_body) in
    let val forall_not_abs_thm = REWRITE_RULE [rename_not_exists_eq_forall_not var] not_exists_abs_thm in
    let val forall_not_thm = ONCE_REWRITE_RULE [GEN_ALL (SYM body_eq_app_abs_thm)] forall_not_abs_thm in
    let val (subgoals1, v1) = ASSUME_TAC forall_not_thm (A, t) in
    let val (A1, t1) = hd subgoals1 in
    let val A1' = filter (not_same_term not_exists_body) A1 in
      ([(A1', t1)], v1)
    end end end end end end end end end end end end

  (* A u {~!x1 ... xn. s(x1, ..., xn)} ?- t
   * -------------------
   * A u {~s(y1, ..., yn)} ?- t
   *)
  val NEG_FORALL_TAC =
    let fun tactic (A, t) =
      case List.find (fn assumption => if is_neg assumption then (is_forall o dest_neg) assumption else false) A of
        NONE => raise (mk_HOL_ERR "helper_tactics" "NEG_FORALL_TAC" "No negated quantification among assumptions.")
      | SOME negq =>
        let val q = dest_neg negq in
        let val (qvar, body) = dest_forall q in
        let val abs = mk_abs (qvar, body) in
        let val app = mk_comb (abs, qvar) in
        let val qapp = mk_forall (qvar, app) in
        let val thm0 = ASSUME negq in
        let val thm1 = GSYM ((DEPTH_CONV BETA_CONV) qapp) in
        let val thm2 = REWRITE_RULE [thm1] thm0 in
        let val thm3 = BETA_RULE (REWRITE_RULE [boolTheory.NOT_FORALL_THM] thm2) in
        let val (subgoals1, v1) = ASSUME_TAC thm3 (A, t) in
        let val (A1, t1) = hd subgoals1 in
        let val A2 = remove_first_occurrence negq A1 in
        let val t2 = t1 in
        let val v2 = (fn x : thm => x) in
        let val (subgoals3, v3) = INST_EXIST_ASM_TAC (concl thm3) (A2, t2) in
        let val (A3, t3) = hd subgoals3 in
          ([(A3, t3)], fn thms => v1 [(v2 o v3) thms])
        end end end end end end end end end end end end end end end end
    in
      tactic THEN REPEAT tactic
    end





(* Old code that does not allow instantiations to different terms. New code takes first instantiation.
  fun merge_teis teis1 [] = teis1
    | merge_teis teis1 ({redex = variable1, residue = value1}::teis2) =
      let val merged_teis = merge_teis teis1 teis2 in
      let val overlapping_tei = List.find (fn {redex = variable2, residue = value2} => same_term variable1 variable2) merged_teis in
        if isSome overlapping_tei then
          let val {redex = _, residue = value2} = valOf overlapping_tei in
            if same_term value1 value2 then
              merged_teis
            else
              raise (mk_HOL_ERR "helper_tactics" "merge_teis" "Same variable instantiated to two different terms.")
          end
        else
          {redex = variable1, residue = value1}::merged_teis
      end end
*)
  fun merge_teis teis1 [] = teis1
    | merge_teis teis1 ({redex = variable1, residue = value1}::teis2) =
      let val merged_teis = merge_teis teis1 teis2 in
      let val overlapping_tei = List.find (fn {redex = variable2, residue = value2} => same_term variable1 variable2) merged_teis in
        if isSome overlapping_tei then
          merged_teis (* Keep first instantiation in case of overlapping instantiations *)
        else
          {redex = variable1, residue = value1}::merged_teis
      end end

  fun separate_uxvars ivar [] =
      raise (mk_HOL_ERR "helper_tactics" "separate_uxvars" "Instantiated variable is not existantially quantified.")
    | separate_uxvars ivar (xvar::xvars) =
      if Term.compare (ivar, xvar) = EQUAL then
        ([], xvars)
      else
        let val (uxvars_prefix, uxvars_suffix) = separate_uxvars ivar xvars in
          (xvar::uxvars_prefix, uxvars_suffix)
        end

  fun add_exists thm [] = thm                 (* A |- P *)
    | add_exists thm (xivar::xvars) =         (* x1, x2, x3 *)
      let val xjthm = add_exists thm xvars in (* A |- ?x2 x3. P *)
      let val xijthm = EXISTS (mk_exists (xivar, concl xjthm), xivar) xjthm in (* A |- ?x1 x2 x3. P *)
        xijthm
      end end

  fun remove_exists_hyp axthm xterm current_xthm [] = PROVE_HYP axthm current_xthm   (* A |- ?x1 x2 x3. P *)
    | remove_exists_hyp axthm xterm current_xthm (xv::xvs) =   (* xterm = P, current_xthm = P |- ?x1 x2 x3. P, xv::xvs = x2, x1, x3 *)
      let val xterm = mk_exists (xv, xterm) in                 (* ?x2. P *)
      let val xthm = ASSUME xterm in                           (* ?x2. P |- ?x2. P *)
      let val current_xthm = CHOOSE (xv, xthm) current_xthm in (* ?x2. P |- ?x1 x2 x3. P *)
        remove_exists_hyp axthm xterm current_xthm xvs
      end end end

  fun insert_exists xvar xvars axthm term =
    let val thm = ASSUME term in
    let val current_xthm = add_exists thm (xvars @ [xvar]) in
    let val inserted_xthm = remove_exists_hyp axthm term current_xthm ((rev xvars) @ [xvar]) in
      inserted_xthm
    end end end

  fun XI_TAC {redex = ivar, residue = ival} (A, t) =
    let val (xvars, xbody) = strip_exists t in
    let val (uxvars_prefix, uxvars_suffix) = separate_uxvars ivar xvars in
    let val uxvars = uxvars_prefix @ uxvars_suffix in
    let val uxbody = list_mk_exists (uxvars, xbody) in
    let val (A', t') = (A, subst [ivar |-> ival] uxbody)
        val validation = fn subgoal_thms =>
            let val subgoal_thm = hd subgoal_thms in
            let val xthm = EXISTS (mk_exists (ivar, uxbody), ival) subgoal_thm in
            let val goal_thm = insert_exists ivar uxvars_prefix xthm (list_mk_exists (uxvars_suffix, xbody)) in
              goal_thm
            end end end in
      ([(A', t')], validation)
    end end end end end

  fun find_xis bvars xvars t =
    if is_neg t then
      find_xis bvars xvars (dest_neg t)
    else if is_conj t then
      let val (c1, c2) = dest_conj t in
      let val xis = find_xis bvars xvars c1 in
        if null xis then
          find_xis bvars xvars c2
        else
          xis
      end end
    else if is_disj t then
      let val (d1, d2) = dest_disj t in
      let val xis = find_xis bvars xvars d1 in
        if null xis then
          find_xis bvars xvars d2
        else
          xis
      end end
    else if is_imp t then
      let val (a, s) = dest_imp t in
      let val xis = find_xis bvars xvars a in
        if null xis then
          find_xis bvars xvars s
        else
          xis
      end end
    else if is_exists t then
      let val (xvs, xb) = strip_exists t in
      let val bvars = bvars @ xvs in
      let val xvars = filter (fn xvar => all (fn xv => term_to_string xvar <> term_to_string xv) xvs) xvars in (* Keep unbounded variables which can be instantiated. *)
        find_xis bvars xvars xb
      end end end
    else if is_forall t then
      let val (qvs, q) = strip_forall t in
      let val bvars = bvars @ qvs in
      let val xvars = filter (fn xvar => all (fn qv => term_to_string xvar <> term_to_string qv) qvs) xvars in (* Keep unbounded variables which can be instantiated. *)
        find_xis bvars xvars q
      end end end
    else if is_eq t then
      let val itevs = xvars
          val (l, r) = dest_eq t in
      let val tevs_l = free_vars l
          val tevs_r = free_vars r in
      let val itevs_l = filter (is_in tevs_l) itevs
          val itevs_r = filter (is_in tevs_r) itevs
          val bvars_l = filter (is_in bvars) tevs_l
          val bvars_r = filter (is_in bvars) tevs_r in
        if (null itevs_l andalso null itevs_r) orelse (not o null) bvars_l orelse (not o null) bvars_r then
          []
        else
          let val instantiations = find_equality_instantiations [] [] l r itevs_l itevs_r [] [] in
            if isSome instantiations then
              let val (_, _, teis_l, teis_r, _, utevs) = valOf instantiations in (* Types are not instantiable. *)
              let val teis = merge_teis teis_l teis_r in
                   (* Instantiates uninstantiated xvars to themselves. *)
              let val uteis = map (fn utev => {redex = utev, residue = utev}) utevs in
                teis @ uteis
              end end end
            else
              []
          end
      end end end
    else
      []

  fun find_xis_eq bvars xvars t =
    if is_neg t then
      find_xis_eq bvars xvars (dest_neg t)
    else if is_conj t then
      let val (c1, c2) = dest_conj t in
      let val xis = find_xis_eq bvars xvars c1 in
        if null xis then
          find_xis_eq bvars xvars c2
        else
          xis
      end end
    else if is_disj t then
      let val (d1, d2) = dest_disj t in
      let val xis = find_xis_eq bvars xvars d1 in
        if null xis then
          find_xis_eq bvars xvars d2
        else
          xis
      end end
    else if is_imp t then
      let val (a, s) = dest_imp t in
      let val xis = find_xis_eq bvars xvars a in
        if null xis then
          find_xis_eq bvars xvars s
        else
          xis
      end end
    else if is_exists t then
      let val (xvs, xb) = strip_exists t in
      let val bvars = bvars @ xvs in
      let val xvars = filter (fn xvar => all (fn xv => term_to_string xvar <> term_to_string xv) xvs) xvars in (* Keep unbounded variables which can be instantiated. *)
        find_xis_eq bvars xvars xb
      end end end
    else if is_forall t then
      let val (qvs, q) = strip_forall t in
      let val bvars = bvars @ qvs in
      let val xvars = filter (fn xvar => all (fn qv => term_to_string xvar <> term_to_string qv) qvs) xvars in (* Keep unbounded variables which can be instantiated. *)
        find_xis_eq bvars xvars q
      end end end
    else if is_eq t then
      let val itevs = xvars
          val (l, r) = dest_eq t in
      let val tevs_l = free_vars l
          val tevs_r = free_vars r in
      let val itevs_l = filter (is_in tevs_l) itevs
          val itevs_r = filter (is_in tevs_r) itevs
          val bvars_l = filter (is_in bvars) tevs_l
          val bvars_r = filter (is_in bvars) tevs_r in
          if is_var l andalso is_var r andalso is_in itevs l andalso is_in itevs r then (* Equality with both sides instantiable variables. *)
            [{redex = l, residue = l}, {redex = r, residue = l}]
          else 
            []
      end end end
    else
      []

  fun EXISTS_CONNECTIVE_TAC (A, t) =
    if is_exists t then
      let val (xvars, xbody) = strip_exists t in
      let val bvars = [] in
      let val xis = find_xis bvars xvars xbody in
        if null xis then (* No instantiations possible, unless... *)
          let val xis = find_xis_eq bvars xvars xbody in
            if null xis then (* there are existential equalities. *)
              raise (mk_HOL_ERR "helper_tactics" "find_xis" "No equation with existantial variables that can be instantiated to make both sides of the equality identical.")
            else
              let fun EXIST_CONNECTIVE_TAC [] (A, t) = ([(A, t)], hd)
                    | EXIST_CONNECTIVE_TAC (xi::xis) (A, t) =
                      let val (subgoals1, validation1) = XI_TAC xi (A, t) in
                      let val (subgoals2, validation2) = EXIST_CONNECTIVE_TAC xis (hd subgoals1) in
                        (subgoals2, fn thms => validation1 [validation2 thms])
                      end end in
                EXIST_CONNECTIVE_TAC xis (A, t)
              end
          end
        else
          let fun EXIST_CONNECTIVE_TAC [] (A, t) = ([(A, t)], hd)
                | EXIST_CONNECTIVE_TAC (xi::xis) (A, t) =
                  let val (subgoals1, validation1) = XI_TAC xi (A, t) in
                  let val (subgoals2, validation2) = EXIST_CONNECTIVE_TAC xis (hd subgoals1) in
                    (subgoals2, fn thms => validation1 [validation2 thms])
                  end end in
            EXIST_CONNECTIVE_TAC xis (A, t)
          end
      end end end
    else
      raise (mk_HOL_ERR "helper_tactics" "EXISTS_CONNECTIVE_TAC" "The conclusion is not existantially quantified.")

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
  val EXISTS_EQ_TAC = REPEAT EXISTS_CONNECTIVE_TAC THEN REWRITE_TAC []













  fun SPLIT_ASM_DISJ_TAC (asl, con) =
    let val t1_or_t2 =
      case List.find is_disj asl of
        NONE => raise (mk_HOL_ERR "helper_tactics" "SPLIT_ASM_DISJ_TAC" "No disjunction in the assumption list.\n")
      | SOME disjunction => disjunction in
        let val (t1, t2) = dest_disj t1_or_t2
            val A = filter (fn assumption => Term.compare (assumption, t1_or_t2) <> EQUAL) asl in
        let val A_t1_t = (t1::A, con)
            val A_t2_t = (t2::A, con)
            fun validation [] = fail (print "SPLIT_ASM_DISJ_TAC: No theorems to subgoals.")
              | validation [thm] = fail (print "SPLIT_ASM_DISJ_TAC: Only one instead of two theorems to subgoals.")
              | validation (A_t1_t_thm::A_t2_t_thm::_) =
              let val A_t1_or_t2_thm = ASSUME t1_or_t2 in
                DISJ_CASES A_t1_or_t2_thm A_t1_t_thm A_t2_t_thm
              end in
          ([A_t1_t, A_t2_t], validation)
        end end
    end

  val SPLIT_ASM_DISJS_TAC =
    let fun tactic (A, t) =
      let val t1_or_t2 = case List.find is_disj A of
        NONE => raise (mk_HOL_ERR "helper_tactics" "SPLIT_ASM_DISJ_TAC" "No disjunction in the assumption list.\n")
      | SOME disjunction => disjunction in
      let val (t1, t2) = dest_disj t1_or_t2
          val A_without_t1_or_t2 = filter (fn assumption => Term.compare (assumption, t1_or_t2) <> EQUAL) A in
      let val A_t1_t = (t1::A_without_t1_or_t2, t)
          val A_t2_t = (t2::A_without_t1_or_t2, t)
          fun validation [] = fail (print "SPLIT_ASM_DISJ_TAC: No theorems to subgoals.")
            | validation [thm] = fail (print "SPLIT_ASM_DISJ_TAC: Only one instead of two theorems to subgoals.")
            | validation (A_t1_t_thm::A_t2_t_thm::_) =
            let val A_t1_or_t2_thm = ASSUME t1_or_t2 in
              DISJ_CASES A_t1_or_t2_thm A_t1_t_thm A_t2_t_thm
            end in
        ([A_t1_t, A_t2_t], validation)
      end end end in
      tactic THEN (REPEAT tactic) THEN SPLIT_ASM_TAC
    end


  (* '{A, ..., B} |- C'
   * ==>
   * '|- A /\ B ==> C'
   *)
  fun HYP_TO_CONJ_RULE thm =
    if (length o hyp) thm = 0 then
      thm
    else
      let val hypotheses = hyp thm in
      let val implication_thm = foldr (fn (ass, thm) => DISCH ass thm) thm hypotheses
          val conjunction = list_mk_conj hypotheses in
      let val conjunction_thm = ASSUME conjunction
          fun remove_antecedents implication_thm conjunction_thm =
            if (length o strip_conj o concl) conjunction_thm = 1 then
              MP implication_thm conjunction_thm
            else
              let val conjunct_thm = CONJUNCT1 conjunction_thm
                  val conjunction_thm = CONJUNCT2 conjunction_thm in
              let val implication_thm = MP implication_thm conjunct_thm in
                remove_antecedents implication_thm conjunction_thm
              end end in
      let val hyp_con_thm = remove_antecedents implication_thm conjunction_thm in
      let val ant_con_thm = DISCH_ALL hyp_con_thm in
        ant_con_thm
      end end end end end

  (* '|- !x1...xn. ...A /\ v = f x1...xn /\ B... ==> t'
   * ==>
   * '|- !x1...xn. ...A /\ B... ==> t[f x1...xn/v]',
   *
   * with lhs not occuring anywhere in else in the antecedent.
   *)
  fun RM_ANT_CONJ_SINGLE_LHS_EQS_ANT_RULE imp_conj_thm =
  let val conclusion = concl imp_conj_thm in
  let val imp = (#2 o strip_forall) conclusion in
  let val antecedent = (#1 o dest_imp) imp in
  let val conjunctions = strip_conj antecedent in
  let val eqs = filter is_eq conjunctions in
  let val eq_lhs_vars = filter (is_var o #1 o dest_eq) eqs in
  let val eq_other_asss = map (fn eq => (dest_eq eq, filter (fn a => Term.compare (a, eq) <> EQUAL) conjunctions)) eq_lhs_vars in
  let val redundant_eqs = filter (fn ((lhs, rhs), asss) => not (exists (var_occurs lhs) asss)) eq_other_asss
      fun find_lhs_matchings [] = []
        | find_lhs_matchings (((lhs, rhs), _)::redundant_eqs) =
            let val matching = #1 (match_term lhs rhs)
                val matchings = find_lhs_matchings redundant_eqs in
              matching @ matchings
            end in
  let val redundant_matchings = find_lhs_matchings redundant_eqs
      val unquantified_thm = SPEC_ALL imp_conj_thm in
  let val redundant_id_eqs_thm = INST_TY_TERM (redundant_matchings, []) unquantified_thm in
  let val simplified_thm = REWRITE_RULE [] redundant_id_eqs_thm in
  let val reduced_thm = GEN_ALL simplified_thm in
    reduced_thm
  end end end end end end end end end end end end

  (* '|- !x1...xn. A /\ ... /\  B /\ ... /\ C ==> D' +
   * '|- !x1...xn. A /\ ... /\ ~B /\ ... /\ C ==> D'
   * ==>
   * '|- !x1...xn. A /\ ... /\ C ==> D'
   *)
  fun MERGE_IMP_LEM_RULE imp1_thm imp2_thm =
    let val unquantified_imp1 = SPEC_ALL imp1_thm
        val unquantified_imp2 = SPEC_ALL imp2_thm in
    let val (imp1_ass, imp1_con) = (dest_imp o #2 o strip_forall o concl) unquantified_imp1
        val (imp2_ass, imp2_con) = (dest_imp o #2 o strip_forall o concl) unquantified_imp2 in
    let val imp1_ass_conj = strip_conj imp1_ass
        val imp2_ass_conj = strip_conj imp2_ass
        fun lem_match (t1, t2) = (is_neg t1 andalso (not o is_neg) t2) orelse (is_neg t2 andalso (not o is_neg) t1) in
    let val (lem1, lem2) =
      case List.find lem_match (zip imp1_ass_conj imp2_ass_conj) of
        NONE => fail (print "MERGE_IMP_LEM_RULE: No pair of assumption conjuncts with one being the negation of the other.\n")
      | SOME (ass1, ass2) => (ass1, ass2) in
    let val (t, t_imp, neg_t, neg_t_imp) =
      if is_neg lem1 then
        (lem2, unquantified_imp2, lem1, unquantified_imp1)
      else
        (lem1, unquantified_imp1, lem2, unquantified_imp2) in
    let val inst_lem_thm = ISPEC t boolTheory.EXCLUDED_MIDDLE
        val hyp_conclusion1_thm = CONJ_ANT_TO_HYP unquantified_imp1
        val hyp_conclusion2_thm = CONJ_ANT_TO_HYP unquantified_imp2 in
    let val hyp_thm = DISJ_CASES inst_lem_thm hyp_conclusion1_thm hyp_conclusion2_thm in
    let val conj_thm = HYP_TO_CONJ_RULE hyp_thm in
    (* Removal of B and ~B may cause other conjuncts to be redundant if they are
     * equalities with a left hand side variable not occurring in any other part
     * of the assumption of the implication.
     *)
    let val simplified_thm = RM_ANT_CONJ_SINGLE_LHS_EQS_ANT_RULE conj_thm in
    let val thm = GEN_ALL simplified_thm in
      thm
    end end end end end end end end end end

  (* '|- !x1...xn y. ...A /\ y = c1 /\ B... ==> C'
   * ...
   * '|- !x1...xn y. ...A /\ y = cm /\ B... ==> C'
   * ==>
   * '|- !x1...xn. ...A /\ B... ==> C'
   *
   * Where the possible values of f x1...xn are {c1...cm}, and n may be 0 and y
   * may or may not be quantified.
   *)
  fun MERGE_IMP_BOOL_CASE_RULE thms =
    let val conjunctss = map (strip_conj o #1 o dest_imp o #2 o strip_forall o concl) thms
        fun distinct_conjuncts conjunctss =
      if (null o flatten) conjunctss then
        []
      else
        let val same_position_conjuncts = map hd conjunctss in
          if Term.compare (hd same_position_conjuncts, (hd o tl) same_position_conjuncts) = EQUAL then
            distinct_conjuncts (map tl conjunctss)
          else
            same_position_conjuncts
        end in
    let val cases = distinct_conjuncts conjunctss in
    let val function_application_eq_value = map dest_eq cases in
    let val lhs = (#1 o hd) function_application_eq_value
        val value_type = (type_of o #2 o hd) function_application_eq_value in
    let val value_nchotomy_thm = TypeBase.nchotomy_of value_type in
    let val value_case_thm = ISPEC lhs value_nchotomy_thm
        val unquantified_thms = map SPEC_ALL thms in
    let val hyp_thms = map CONJ_ANT_TO_HYP unquantified_thms in
    let val hyp_thm = DISJ_CASESL value_case_thm hyp_thms in
    let val conj_thm = HYP_TO_CONJ_RULE hyp_thm
        val xvars = (#1 o strip_forall o concl o hd) thms in
    let val free_vars_conj_thm = (free_vars o concl) conj_thm in
    let val still_xvars = filter (fn xv => exists (fn fv => Term.compare (xv, fv) = EQUAL) free_vars_conj_thm) xvars in
    let val thm = GENL still_xvars conj_thm in
      thm
    end end end end end end end end end end end end

  (* '|- !X y. A /\ ... y = f X value1 ... /\ B ==> C'
   * ...
   * '|- !X y. A /\ ... y = f X valuen ... /\ B ==> C'
   * ==>
   * '|- !name_of_quantifier X y. A /\ ... y = f X name_of_quantifier ... /\ B ==> C'
   *
   * where value1...valuen are all possible values of the last argument to f.
   *)
  fun MERGE_IMP_FUN_ARG_CASE_RULE name_of_quantifier thms =
    let val conjuncts = map (strip_conj o #1 o dest_imp o concl o SPEC_ALL) thms
        fun find_different_corresponding_elements conjuncts =
      if (null o flatten) conjuncts then
        raise (mk_HOL_ERR "helper_tactics" "MERGE_IMP_FUN_ARG_CASE_RULE" "The antecedent conjuncts of all theorems are identical.")
      else
        let val corresponding_conjuncts = map hd conjuncts in
          if Term.compare (hd corresponding_conjuncts, (hd o tl) corresponding_conjuncts) <> EQUAL then
            corresponding_conjuncts
          else
            find_different_corresponding_elements (map tl conjuncts)
        end in
    let val eq_function_case_eqs = find_different_corresponding_elements conjuncts in
    let val function_cases = map (boolSyntax.rhs) eq_function_case_eqs in
    let val args = map (#2 o strip_comb) function_cases in
    let val values = find_different_corresponding_elements args in
    let val values_type = (type_of o hd) values in
    let val nchotomy_thm = TypeBase.nchotomy_of values_type
        val new_quantifier = mk_var (name_of_quantifier, values_type) in
    let val inst_case_thm = ISPEC new_quantifier nchotomy_thm
        val thm_values = zip thms values in
    let val thm_value_case_thms = map (fn (thm, value) => (thm, value, (SYM o ASSUME o mk_eq) (new_quantifier, value))) thm_values
        fun prove (thm, value, rw_thm) = SUBST [new_quantifier |-> rw_thm] (subst [value |-> new_quantifier] (concl thm)) thm in
    let val variable_thms = map prove thm_value_case_thms in
    let val variable_thm = DISJ_CASESL inst_case_thm variable_thms in
    let val thm = GEN new_quantifier variable_thm in
      thm
    end end end end end end end end end end end end

  (* '|- !x1...xn y. A /\ ... y = construct1 x1...xn ... /\ B ==> C'
   * ...
   * '|- !x1...xn y. A /\ ... y = constructm x1...xn ... /\ B ==> C'
   * ==>
   * '|- !X. A /\ ... /\ B ==> C',
   *
   * where the datatype constructi x1...xn have m forms, and X are x1...xn
   * without those variables only occurring in the constructors.
   *)
(* OLD CODE THAT DOES NOT ALLOW NESTED CONSTRUCTS.
  fun MERGE_IMP_EQ_CASES_RULE thms =
    let val conjuncts = map (strip_conj o #1 o dest_imp o concl o SPEC_ALL) thms
        fun find_different_corresponding_elements conjuncts =
          if (null o flatten) conjuncts then
            raise (mk_HOL_ERR "helper_tactics" "MERGE_IMP_EQ_CASES_RULE" "The antecedent conjuncts of all theorems are identical.")
          else
            let val corresponding_conjuncts = map hd conjuncts in
              if Term.compare (hd corresponding_conjuncts, (hd o tl) corresponding_conjuncts) <> EQUAL then
                corresponding_conjuncts
              else
                find_different_corresponding_elements (map tl conjuncts)
            end in
    let val case_eqs = find_different_corresponding_elements conjuncts in
    let val cases = map (boolSyntax.rhs) case_eqs in
    let val case_type = (type_of o hd) cases in
    let val case_type_name = (#1 o dest_type) case_type in
    let val nchotomy_thm = (TypeBase.nchotomy_of o type_of o hd) cases (*(#1 o #2 o hd o DB.find) (concat [case_type_name, "_nchotomy"])*)
        val instantiation_term = (boolSyntax.lhs o hd) case_eqs in
    let val inst_case_eq_thm = ISPEC instantiation_term nchotomy_thm in
    let val thm_case_eqs = (strip_disj o #2 o strip_forall o concl) inst_case_eq_thm in
    let val cases_order = map (boolSyntax.rhs o #2 o strip_exists) thm_case_eqs
        val pair_case_thms = zip cases thms
        fun find_case_thm case_eq_exists [] = raise (mk_HOL_ERR "helper_tactics" "find_case_thm" "")
          | find_case_thm case_eq_exists ((case_eq, thm)::case_eq_thms) =
              let val term_matching = #1 (match_term ((boolSyntax.rhs o #2 o strip_exists) case_eq_exists) case_eq)
                  val (xvars, xbody) = strip_exists case_eq_exists in
              let val mvars = map (subst term_matching) xvars
                  val mbody = subst term_matching xbody in
                (list_mk_exists (mvars, mbody), thm)
              end end
              handle _ => find_case_thm case_eq_exists case_eq_thms in
    let fun pair_case_thm_thms [] = []
          | pair_case_thm_thms (thm_case_eq::thms_case_eqs) =
              (find_case_thm thm_case_eq pair_case_thms)::(pair_case_thm_thms thms_case_eqs) in
    let val case_thms = pair_case_thm_thms thm_case_eqs
        fun REMOVE_ANT_CONJ_RULE (xhyp, thm) =
          if (not o is_exists) xhyp then
            ASM_REWRITE_RULE [] (ADD_ASSUM xhyp (SPECL ((#1 o strip_forall o concl) thm) thm))
          else
            let val inst_xhyp = (#2 o strip_exists) xhyp in
            let val inst_xhyp_thm = ADD_ASSUM inst_xhyp thm in
            let val unquantified_thm = SPECL ((#1 o strip_forall o concl) thm) inst_xhyp_thm in
            let val thm = ASM_REWRITE_RULE [] unquantified_thm in
            let fun inst_exists xhyp =
              if (not o is_exists) xhyp then
                thm
               else
                 let val thm1 = ASSUME xhyp
                     val (xvar, xbody) = dest_exists xhyp in
                 let val thm2 = inst_exists xbody in
                   CHOOSE (xvar, thm1) thm2
                 end end in
              inst_exists xhyp
            end end end end end in
    let val removed_ant_thms = map REMOVE_ANT_CONJ_RULE case_thms in
    let val unquantified_thm = DISJ_CASESL inst_case_eq_thm removed_ant_thms
        val removed_variables = free_varsl cases
        val quantified_variables = (#1 o strip_forall o concl o hd) thms in
    let val still_quantified_variables =
        filter (fn qv => not (exists (fn rv => Term.compare (qv, rv) = EQUAL) removed_variables)) quantified_variables in
    let val thm = GENL still_quantified_variables unquantified_thm in
      thm
    end end end end end end end end end end end end end end end
*)

  (* Algorithm:
   * We have a base theorem: l = ...pattern ivars... |- ?xvars. l = t xvars
   * we want to rename subpatterns of ivars
   *
   * At a step we are given renaming: vari |-> termi varsi
   * Look up nchotomy for type of termi: |- !xi. ?xvarsi. xi = term_patterni xvarsi
   * Instantiate nchotomy with vari: |- ?xvarsi. vari = term_patterni xvarsi
   * compute recursive renaming: term_pattermi xvarsi |-> termi varsi
   * Recursive call gives: A[termi varsi/term_patterni xvarsi] |- ?xvars. l = t xvars
   * A[vari/termi varsi/term_patterni xvarsi] |- ?xvars. l = t xvars
   *
   * The algorithm is illustrated by the following proof tree where the the
   * nested patterns are lists and pairs:
   *
   * --------------------------NCHOTOMY
   * |- !h ?c1 c2. h = (c1, c2)
   * --------------------------SPEC h
   *  |- ?c1 c2. h = (c1, c2) = inchotomy
   *                                                 ----------------------------ASSUME    --------------------ASSUME
   *                                                 h = (c1, c2) |- h = (c1, c2)          l = h::t |- l = h::t
   *                                                 ----------------------------------------------------------SUBST (h |-> thm1) thm2
   *                                                        l = h::t, h = (c1, c2) |- l = (c1, c2)::t
   * --------------------------------------ASSUME    -----------------------------------------------------EXISTS
   * ?c2. h = (c1, c2) |- ?c2. h = (c1, c2)          l = h::t, h = (c1, c2) |- ?l c1 c2 t. l = (c1, c2)::t
   * -----------------------------------------------------------------------------------------------------CHOOSE (c2, thm1)
   * |- ?c1 c2. h = (c1, c2) / inchotomy        ?c2. h = (c1, c2), l = h::t |- ?l c1 c2 t. l = (c1, c2)::t
   * -----------------------------------------------------------------------------------------------------CHOOSE (c1, thm1)
   *                               l = h::t |- ?l c1 c2 t. l = (c1, c2)::t
   *
   * Inputs:
   * -base_xthm: l = pattern xvs |- ?xvs. l = pattern xvs, with xvars not
   *  occurring in l.
   * -v |-> p, where v is a variable and p a variable or a pattern potentially
   *  containing variables.
   *
   * Output: l = (pattern xvs)[v/p] |- ?xvs. l = pattern xvs.
   *)
  fun expand_xthm base_xthm {redex = v, residue = p} =
    if is_var p then
      INST [p |-> v] base_xthm
    else
      let val nchotomy_thm = ISPEC v ((TypeBase.nchotomy_of o type_of) v) in             (* |- ?xvs. v = v_type_pattern xvs *)
      let val (xvs, v_eq_p) = (strip_exists o concl) nchotomy_thm in                     (* (xvs, v = v_type_pattern xvs  *)
      let val renaming_rec = #1 (match_term (rhs v_eq_p) p) in (*xvsi |-> v_type_subterm_patterni; drop types, correct due to ISPEC.*)
           (* l = pattern[xvsi/v_type_subterm_patterni] |- ?xvs. l = pattern xvs *)
      let val thm_rec = foldr (fn (renaming, xthm) => expand_xthm xthm renaming) base_xthm renaming_rec in
           (* |- l = pattern[xvsi/v_type_subterm_patterni] ==> ?xvs. l = pattern xvs *)
      let val imp_thm_rec = DISCH ((hd o hyp) thm_rec) thm_rec  
          val p_eq_v = (mk_eq (rhs v_eq_p, lhs v_eq_p)) in (* v_type_pattern xvs = v *)
      let val p_eq_v_thm = ASSUME p_eq_v                   (* v_type_pattern xvs = v |- v_type_pattern xvs = v *)
          val mark = genvar_term (rhs p_eq_v) in
           (* l = pattern[mark/p] ==> ?xvs. l = pattern xvs *)
      let val template = subst [lhs p_eq_v |-> mark] (concl imp_thm_rec) in
           (* |- l = pattern[v/p] ==> ?xvs. l = pattern xvs *)
      let val v_imp_thm_rec = SUBST [mark |-> p_eq_v_thm] template imp_thm_rec
          fun add_x (x, (xp_eq_v, thm)) = (mk_exists (x, xp_eq_v), CHOOSE (x, (ASSUME o mk_exists) (x, xp_eq_v)) thm) in
           (* ?xvs. v_type_pattern xvs = v |- l = pattern[v/p] ==> ?xvs. l = pattern xvs *)
      let val x_imp_thm_rec = #2 (foldr add_x (p_eq_v, v_imp_thm_rec) (tl xvs)) in
           (* |- l = pattern[v/p] ==> ?xvs. l = pattern xvs *)
      let val imp_thm = CHOOSE (hd xvs, GSYM nchotomy_thm) x_imp_thm_rec in
           (* l = pattern[v/p] |- ?xvs. l = pattern xvs *)
      let val thm = UNDISCH imp_thm in
        thm
      end end end end end end end end end end end

  (* Inputs:
   * @case_eq_exists: ?xvars. l = pattern xvars. Disjunct of nchotomy theorem of the type of l.
   * @case_eq: (pattern1 v11...v1n)...(patterni vi1...vim)....(patternm vm1...vmp)
   *  The right handside of the equation in which l appears in, and which may be nested patterns.
   *
   * Output:
   * ?xvars l = pattern xvars
   * |-
   * ?v11...vm1. (pattern1 v11...v1n)...(patterni vi1...vim)....(patternm vm1...vmp)
   *)
  fun expand_xthms case_eq_exists case_eq =
    let val (xvars, xbody) = strip_exists case_eq_exists in
      if null xvars then
        ASSUME xbody
      else
        let fun sort_renaming renaming [] = []
              | sort_renaming renaming (xvar::xvars) = 
                let val sorted_renaming = sort_renaming renaming xvars
                    val renaming = List.find (fn {redex = v, residue = p} => same_term xvar v) renaming in
                        if isSome renaming then
                          sorted_renaming @ [(valOf renaming)]
                        else
                          raise (mk_HOL_ERR "helper_tactics" "sort_renaming" "renamed variable not existantially quantified.")
                end
            val renamings = #1 (match_term ((boolSyntax.rhs o #2 o strip_exists) case_eq_exists) case_eq) in
        let val sorted_renamings = sort_renaming renamings xvars (* Renamings are processed in order of existantial variables. *)
            val mvars = foldl (fn ({redex = _, residue = i}, mvars) => union_lists same_term mvars (free_vars i)) [] renamings
            val mbody = subst renamings xbody in
        let val base_xthm = foldl (fn (xvar, xthm) => EXISTS (mk_exists (xvar, concl xthm), xvar) xthm) (ASSUME mbody) mvars in
        let val expanded_xthm = foldr (fn (renaming, xthm) => expand_xthm xthm renaming) base_xthm sorted_renamings
            fun add_x (x, (xterm, thm)) = (mk_exists (x, xterm), CHOOSE (x, (ASSUME o mk_exists) (x, xterm)) thm) in
        let val x_expanded_xthm = #2 (foldr add_x (xbody, expanded_xthm) (tl xvars)) in
        let val xthm = CHOOSE (hd xvars, ASSUME case_eq_exists) x_expanded_xthm in
          xthm
        end end end end end end
    end

  fun MERGE_IMP_EQ_CASES_RULE thms =
    let val conjuncts = map (strip_conj o #1 o dest_imp o concl o SPEC_ALL) thms
        fun find_different_corresponding_elements conjuncts = (* REQUIRES SOME ANTECEDENT CONJUNCTS TO OCCUR IN THE SAME ORDER! *)
          if (null o flatten) conjuncts then
            raise (mk_HOL_ERR "helper_tactics" "MERGE_IMP_EQ_CASES_RULE" "The antecedent conjuncts of all theorems are identical.")
          else
            let val corresponding_conjuncts = map hd conjuncts in
              if Term.compare (hd corresponding_conjuncts, (hd o tl) corresponding_conjuncts) <> EQUAL then
                corresponding_conjuncts
              else
                find_different_corresponding_elements (map tl conjuncts)
            end in
    let val case_eqs = find_different_corresponding_elements conjuncts in
    let val cases = map (boolSyntax.rhs) case_eqs in
    let val nchotomy_thm = (TypeBase.nchotomy_of o type_of o hd) cases
        val instantiation_term = (boolSyntax.lhs o hd) case_eqs in
    let val inst_case_eq_thm = ISPEC instantiation_term nchotomy_thm in
    let val thm_case_eqs = (strip_disj o #2 o strip_forall o concl) inst_case_eq_thm in
    let val cases_order = map (boolSyntax.rhs o #2 o strip_exists) thm_case_eqs
        val pair_case_thms = zip cases thms

        fun find_case_thm case_eq_exists [] =
            raise (mk_HOL_ERR "helper_tactics" "find_case_thm" "Could not match conjunct to nchotomy case.")
          | find_case_thm case_eq_exists ((case_eq, thm)::case_eq_thms) =
              let val xthm = expand_xthms case_eq_exists case_eq in
                (xthm, thm)
              end
              handle _ => find_case_thm case_eq_exists case_eq_thms in

    let fun pair_case_thm_thms [] = []
          | pair_case_thm_thms (case_eq_exists::thms_case_eqs) =
              (find_case_thm case_eq_exists pair_case_thms)::(pair_case_thm_thms thms_case_eqs) in

    let val case_thms = pair_case_thm_thms thm_case_eqs
        fun REMOVE_ANT_CONJ_RULE (xthm, thm) =
            let val xhyp = concl xthm in
            let val ihyp = (#2 o strip_exists) xhyp in
            let val ihyp_thm = ADD_ASSUM ihyp thm in
            let val unquantified_thm = SPECL ((#1 o strip_forall o concl) thm) ihyp_thm in
            let val other_ant_conjs = ((filter (not_same_term ihyp)) o strip_conj o #1 o dest_imp o concl) unquantified_thm
                val hyp_suc_thm = CONJ_ANT_TO_HYP unquantified_thm in
            let val first_conj_hyp_thm = HYPS_IMP_TO_CONJS_IMP_RULE hyp_suc_thm other_ant_conjs in
            let fun inst_exists xhyp =
                    if (not o is_exists) xhyp then
                      first_conj_hyp_thm
                    else
                      let val thm1 = ASSUME xhyp
                          val (xvar, xhyp) = dest_exists xhyp in
                      let val thm2 = inst_exists xhyp in
                        CHOOSE (xvar, thm1) thm2
                      end end in
              PROVE_HYP xthm (inst_exists xhyp)
            end end end end end end end in
    let val removed_ant_thms = map REMOVE_ANT_CONJ_RULE case_thms in
    let val unquantified_thm = DISJ_CASESL inst_case_eq_thm removed_ant_thms
        val removed_variables = free_varsl cases
        val quantified_variables = (#1 o strip_forall o concl o hd) thms in
    let val still_quantified_variables =
        filter (fn qv => not (exists (fn rv => Term.compare (qv, rv) = EQUAL) removed_variables)) quantified_variables in
    let val thm = GENL still_quantified_variables unquantified_thm in
      thm
    end end end end end end end end end end end end end

  (* '{a, ..., a} u ... u {b, ..., b} u A ?- t'
   * ==>
   * 'A ?- t'
   *)
  val REMOVE_DUPLICATE_ASMS_TAC =
    let fun tactic (A, t) =
      let fun has_duplicate [] = NONE
            | has_duplicate (term::terms) =
              if exists (fn other_term => Term.compare (other_term, term) = EQUAL) terms then
                SOME term
              else
                has_duplicate terms in
        case has_duplicate A of
          NONE => raise (mk_HOL_ERR "helper_tactics" "REMOVE_DUPLICATE_ASMS_TAC" "No duplicate assumptions.")
        | SOME duplicate =>
            let val A_without_duplicate = filter (fn a => Term.compare (a, duplicate) <> EQUAL) A in
            let val A' = duplicate::A_without_duplicate in
              ([(A', t)], (fn thms => hd thms))
            end end
      end in
      tactic THEN REPEAT tactic
    end

  (* 'A u {l1 = r1...ln = rn} ?- t'
   * ==>
   * 'A ?- t', where each li does not occur in any other assumption nor t. There
   * might be equations whose left hand side occurs in another assumption whose
   * left hand side does not occur in another assumption nor the conclusion, in
   * that case both these equations are removed.
   *
   * 1. Take all equations.
   * 2. Pair each equation with all other equations and the conclusion.
   * 3. Filter out the equations whose left hand side does not occur in the
   *    other assumptions nor the conclusion.
   * 4. Remove all such equations.
   * 5. Repeat steps 1-4, as long as there are equations with left hand sides
   *    not occuring anywhere else in the goal.
   *)
  val RM_SINGLE_LHS_ASMS_TAC =
    let fun tactic (A, t) =
      let val eqs = filter is_eq A
          fun is_same t1 t2 = Term.compare (t1, t2) = EQUAL in
      let fun other_assumptions_goal other = filter (fn a => not (is_same other a)) (t::A) in
      let fun eq_lhs_not_in_other_assumptions_goal eq = all (fn term => not (is_subterm (boolSyntax.lhs eq) term)) (other_assumptions_goal eq) in
      let val eqs_lhs_not_in_other_assumptions_goal = filter (fn eq => eq_lhs_not_in_other_assumptions_goal eq) eqs in
        if null eqs_lhs_not_in_other_assumptions_goal then
          raise (mk_HOL_ERR "helper_tactics" "RM_SINGLE_LHS_ASMS_TAC" "No assumption equality with left hand side not occuring anywhere else in the goal.\n")
        else
          let val A' = filter (fn a => all (fn eq => not (is_same eq a)) eqs_lhs_not_in_other_assumptions_goal) A in
            ([(A', t)], fn thms => hd thms)
          end
      end end end end in
      tactic THEN REPEAT tactic
    end

  (* '{var1 = t1, ..., tn = varn} u A ?- t'
   * ==>
   * 'A ?- t'
   *
   * where vi only ony occurs only among all assumptions and the conclusion t.
   *)
  val REMOVE_SINGLE_VAR_EQ_ASMS_TAC =
    let fun tactic (A, t) =
      let val eqs = filter is_eq A
          fun is_same t1 t2 = Term.compare (t1, t2) = EQUAL in
      let val var_eqs = filter (fn eq => (is_var o boolSyntax.lhs) eq orelse (is_var o boolSyntax.rhs) eq) eqs
          fun other_assumptions_goal other = filter (fn a => not (is_same other a)) (t::A)
          fun var_not_free var terms = not (exists (is_same var) (free_varsl terms)) in
      let fun var_not_in var terms = is_var var andalso var_not_free var terms
          val var_eqs_other_assumptions_goal = map (fn eq => (eq, other_assumptions_goal eq)) var_eqs in
      let fun var_lhs_or_rhs_not_in (eq, ts) = var_not_in (boolSyntax.lhs eq) ts orelse var_not_in (boolSyntax.rhs eq) ts in
      let val single_var_lhs_or_rhs_eq_other_assumptions_goal = filter var_lhs_or_rhs_not_in var_eqs_other_assumptions_goal in
      let val single_var_lhs_or_rhs_eqs = map #1 single_var_lhs_or_rhs_eq_other_assumptions_goal in
        if null single_var_lhs_or_rhs_eqs then
          raise (mk_HOL_ERR "helper_tactics" "REMOVE_SINGLE_VAR_EQ_ASMS_TAC" "No assumptions being equalities with a left or right hand side variable that does not occur in any other assumption or the conclusion of the goal.\n")
        else
          let fun is_single_var_lhs_or_rhs_eq a = exists (is_same a) single_var_lhs_or_rhs_eqs in
          let val A' = filter (fn a => not (is_single_var_lhs_or_rhs_eq a)) A in
            ([(A', t)], fn thms => hd thms)
          end end end end end end end end in
    tactic THEN REPEAT tactic
  end



  (* A u {t1 = t1, ..., tn = tn} ?- t
   * ==>
   * A ?- t
   *)
  fun RM_ASM_IDS_TAC (A, t) =
    let val eqs = filter is_eq A in
    let val identities = filter (fn eq => Term.compare (lhs eq, rhs eq) = EQUAL) eqs in
    let fun not_identity a = all (not_same_term a) identities in
    let val A_without_identities = filter not_identity A in
      ([(A_without_identities, t)], fn thms => hd thms)
    end end end end

  (* xeq = '?x1...xn. variable = pattern x1...xn'
   * A u {?x1...xn. variable = pattern x1...xn}  ?- t
   * ------------------------------------------------, where xi' do not exist in (A, t)
   *          A u {variable = pattern x1'...xn'} ?- t
   *)
  fun REMOVE_XEQ_TAC xeq additionally_invalid_instantiation_variables (A, t) =
    let val (ieq, instantiation) = instantiate_exists xeq (t::(A @ additionally_invalid_instantiation_variables)) in
    let val A' = ieq::(filter (not_same_term xeq) A)
        fun chooses thm iterm [] = thm
          | chooses thm iterm ((v, x)::vxs) =                       (* iterm = s[v/x] *)
            let val xterm = mk_exists (x, subst [v |-> x] iterm) in (* xterm = ?x. s, since v is fresh. *)
              chooses (CHOOSE (v, ASSUME xterm) thm) xterm vxs
            end in
    let val validation = fn subgoal_achieving_thm => chooses subgoal_achieving_thm ieq instantiation in
      (A', t, validation, ieq)
    end end end

  (* A ?- t
   * ------xeq: ?x1...xn. s = f x1...xn
   * (A ?- t)[f x1'...xn'/s]
   *)
  fun INST_XEQ_TAC xeq mark template subterm term (A, t) =
    let val (A1, t1, v1, asm_eq) = REMOVE_XEQ_TAC xeq [mark] (xeq::A, t) in
    let val (subgoals2, v2) = ASM_RW_OTHERS_TAC false asm_eq (A1, t1) in
    let val (A2, t2) = hd subgoals2
        val (old, new) = dest_eq asm_eq
        val mark2 = mark in
    let val template2 = subst [old |-> new] template in
    let val subterm2 = subst [old |-> new] subterm in
    let val term2 = subst [mark2 |-> subterm2] template2 in
      ((A2, t2, mark2, template2, subterm2, term2), v1 o v2)
    end end end end end end


  (****************************************************************************)
  (*Start of automatic lemma instantiation tactic******************************)
  (****************************************************************************)

  (* Input:
   * -A term subterm.
   * -A term superterm.
   *
   * Output:
   * -SOME ((term_matching from subterm to a subterm of term,
   *         type_matching from subterm to a subterm of term),
   *        the subterm of term that is matched to from term),
   *  if it is possible to match subterm to a subterm of term.
   * -NONE otherwise.
   *
   * A requirement of the matching is that the matched variables in the superterm
   * are free in the superterm. This is done as follows.
   * -If no matching exists: NONE is returned.
   * -If a matching exists: If the variables matched to in the superterm is not
   *  free, then the subterms of the superterm are checked form matchings.
   *  Otherwise the matching is returned.
   *
   * The variables that are mapped to in the superterm are identified as follows:
   * -Those that are explicitly mentioned in the matching.
   * -Those that are not explicitly mentioned in the matching, and therefore have
   *  the same name as the free variables of the subterm that are not mentioned
   *  in the matching.
   *)
  fun has_subterm_match subterm superterm =
    let val free_supervariable_names = map term_to_string (free_vars superterm) 
        val free_subvariable_names = map term_to_string (free_vars subterm)
        fun check_matching term =
          let val (term_matching, type_matching) = match_term subterm term in
          let val (explicit_from_map, explicit_to_map) = foldl
              (fn ({redex = from, residue = to}, (froms, tos)) => (term_to_string from::froms, term_to_string to::tos))
              ([], [])
              term_matching in
          let val implicit_to_map = filter
              (fn free_subvariable_name =>
               not (exists (fn mapped_from_variable_name =>
                            free_subvariable_name = mapped_from_variable_name) explicit_from_map))
                                                                               free_subvariable_names in
          let val explicit_maps_are_free = all (fn name => exists (fn free => name = free) free_supervariable_names) explicit_to_map
              val implicit_maps_are_free = all
                (fn name => exists (fn free => name = free) free_supervariable_names) implicit_to_map in
            if explicit_maps_are_free andalso implicit_maps_are_free then
              SOME (term_matching, type_matching, term)
            else
              check_subterms term
          end end end end
          handle _ => check_subterms term
        and check_subterms term =
          if is_var term orelse is_const term then
            NONE
          else if is_comb term then
            let val (function, argument) = dest_comb term in
              case check_matching function of
                NONE => check_matching argument
              | SOME term_match_type_match_term => SOME term_match_type_match_term
            end
          else (* abstraction *)
            let val body = (#2 o dest_abs) term in
              check_matching body
            end in
      check_matching superterm
    end

  (* Input:
   * -A predicate term conjunct of the form 'P x' or 'a = f b'
   * -A predicate term assumption of the form 'Q y' or 'x = g y'.
   *
   * Output: A term-type matching.
   * -([], [], []): conjunct does not match any subterm of assumption.
   * -([term_match], [type_match], []): 'P x' or 'a = f b' matches 'Q y' or
   *  'x = g y', respectively.
   * -([term_match], [type_match], [(a, |- ?x. x = subterm)]): 'f b' matches a
   *  subterm of 'Q y' or 'g y', where a is the left-hand side of 'a = f b', and
   *  subterm is the subterm of 'Q y' or 'g y' that 'f b' matches.
   *)
  fun find_match_assumption_substitution_conjunct_assumption conjunct assumption =
    if (not o is_eq) conjunct andalso (not o is_eq) assumption then (* conjunct: P x; assumption: Q y *)
      let val (term_match, type_match) = match_term conjunct assumption in
        (term_match, type_match, [])                                (* match P x to Q y *)
      end
      handle _ => ([], [], [])
    else if is_eq conjunct andalso is_eq assumption then            (* conjunct: a = f b; assumption: x = g y *)
      let val (term_match, type_match) = match_term conjunct assumption in
        (term_match, type_match, [])                                (* match a = f b to x = g y *)
      end
      handle _ =>
      let val (conjunct_lhs, conjunct_rhs) = dest_eq conjunct
          val (assumption_lhs, assumption_rhs) = dest_eq assumption in
        case has_subterm_match conjunct_rhs assumption_rhs of       (* match f b to a subterm of g y *)
          NONE => ([], [], [])
        | SOME (term_match, type_match, subterm) => (term_match, type_match, [(conjunct_lhs, ISPEC subterm EXISTS_REFL)])
      end
    else if is_eq conjunct andalso (not o is_eq) assumption then    (* conjunct: a = f b; assumption P x *)
      let val (lhs, rhs) = dest_eq conjunct in
        case has_subterm_match rhs assumption of                    (* match f b to a subterm of P x *)
          NONE => ([], [], [])
        | SOME (term_match, type_match, subterm) => (term_match, type_match, [(lhs, ISPEC subterm EXISTS_REFL)])
      end
    else (* Other cases not treated. *)
      ([], [], [])

  (* Input:
   * -A predicate term conjunct of the form 'P x' or 'a = f b'
   * -A list of predicate terms assumptions of the form 'Q y' or 'x = g y'.
   *
   * Output: A term-type matching, and an equality theorem associated with the
   * matched assumption.
   * -([term_match], [type_match], []): 'P x' or 'a = f b' matches 'Q y' or
   *  'x = g y' of some assumption, respectively.
   * -([term_match], [type_match], [(a, |- ?x. x = subterm)]): 'f b' matches a
   *  subterm of 'Q y' or 'g y', of some assumption, where a is the left-hand
   *  side of 'a = f b', and subterm is the subterm of 'Q y' or 'g y' that 'f b'
   *  matches.
   *
   * If no match is found, an exception is raised.
   *)
  fun find_match_assumption_substitution conjunct [] =
        fail ((print o concat) ["find_match_assumption_substitution: Could not match conjunct in assumption of lemma to an assumption in the goal: ", term_to_string conjunct, ".\n"])
    | find_match_assumption_substitution conjunct (assumption::assumptions) =
      case find_match_assumption_substitution_conjunct_assumption conjunct assumption of
        ([]          , []          , []        ) => find_match_assumption_substitution conjunct assumptions
      | (term_matches, type_matches, equalities) => (term_matches, type_matches, equalities)

  (* Input:
   * -A list of predicate terms conjuncts of the form 'P x' or 'a = f b'
   * -A list of predicate terms assumptions of the form 'Q y' or 'x = g y'.
   *
   * Output: Merged term matchings, and merged type matchings, involving all
   * matched conjuncts, and existential equality theorems for those conjuncts of
   * the form 'a = f b' with 'f b' matched. Fails if not all conjuncts match some
   * assumption: (term_matchings, type_matchings, existential_equality_theorems).
   * The existential equality theorems are of the form (a, |- ?x. x = g y), where
   * 'f b' matches 'g y', and 'a = f b'.
   *)
  fun find_match_assumptions_substitutions [] assumptions = ([], [], [])
    | find_match_assumptions_substitutions (conjunct::conjuncts) assumptions =
        let val (term_matchings, type_matchings, new_assumptions) = find_match_assumptions_substitutions conjuncts assumptions
            val (term_matching , type_matching , new_assumption ) = find_match_assumption_substitution   conjunct  assumptions in
          (term_matching @ term_matchings, type_matching @ type_matchings, new_assumption @ new_assumptions)
        end

  (* Input:
   * -Lemma of the form
   * '|- !vars.
   *     A1 vars (f1 vars)...(fm vars) /\ ... /\ Ak vars (f1 vars)...(fm vars) /\
   *     y1 = f1 vars /\ ... /\ yn = fn vars
   *     =>
   *     Q vars
   * -Goal of the form
   *   ([A1 values (f1 values)...(fm values), ..., Ak values (f1 values)...(fm values),
   *     B1 values (f1 values)...(fm values), ..., Bp values (f1 values)...(fm values)], (* Bi may be of the form x = g y *)
   *    C values (f1 values)...(fm values))                                              (* C denotes the goal conclusion *)
   *
   * Output: Produces a goal of the form, where y'i are fresh with respect to the goal and vars are appropriately instantiated:
   *   ([A1 values y'1...y'p, ..., Ak values y'1...y'm,
   *     B1 values y'1...y'p, ..., Bp values y'1...y'm,
   *     y'1 = f1 values, ..., y'n = fn values,
   *     Q values y'1...y'p],
   *    C values y'1...y'p)
   *
   * Algorithm:
   * 1. Remove the quantifiers from the lemma.
   * 2. Compute all conjuncts of the assumption of the uniquely specialized
   *    implication of the lemma.
   * 3. Compute the matchings from the conjuncts (equalities may be matched with
   *    respect to their right hand side only) of the lemma to the assumptions of
   *    the goal.
   *
   *    [Note: If there are equalities of the form var1 = var2, then var1 and
   *     var2 is used in some predicate or other equality with left hand sides
   *     being of the required form. Hence, these variable only equalities do not
   *     need to be considered, but the instantiated versions of the equalities
   *     must occur in the goal assumptions, otherwise it will not work.
   *     Equaltities of the form f x1...xn y1...yo = variable are not allowed and
   *     also do not need to be considered.]
   * 4. Instantiate the lemma with the computed matching.
   * 5. Compute the unmatched left-hand side variables to be used in the
   *    existentially quantified equality theorems.
   * 6. For each right hand side of an equality in the instantiated lemma,
   *    substitute its instantiated left hand side variable in the assumptions of
   *    the goal and the conclusion.
   * 7. Validation function. Given achieving theorem,
   *    A[ti/ui] u {C} u {t1 = u1, ..., tn = un} |- t[ti/ui],
   *    produces a theorem A |- t.
   *
   *    This is done as follows (where ti is yi and ui is fi values above):
   *
   *
   *     lemma_conjuncts |- Q     A |- t
   *   ----------------------------------  PROVE_HYP, lemma_conjuncts ⊆ A.
   *             A - {Q} |- t2
   *
   *    DISCHCARGE A[ti/ui]: {t1 = u1, ..., tn = un} |- (A ==> t)[ti/ui]
   *
   *
   *    t1 = u1 |- t1 = u1  ...  tn = un |- tn = un    {t1 = u1, ..., tn = un} |- (A ==> t)[ti/ui]
   *    ------------------------------------------------------------------------------------------SUBS[t1=u1|-t1=u1...tn=un|-tn=un]
   *    {t1 = u1} u ... u {tn = un} |- (A ==> t)[ti/ui][ui/ti], which is equivalent to:
   *    {t1 = u1} u ... u {tn = un} |- (A ==> t),
   *    since ti are unique as can bee seen in gen_variant in compute_lemma_instantiation_and_xthm_applications.
   *
   *
   *    |- ?tn. tn = un      {t1 = u1} u ... u {tn = un} |- A ==> t
   *    -------------------------------------------------------------  CHOOSE (tn, |- ?tn. tn = un)
   *            {t1 = u1} u ... u {tn-1 = un-1} |- A ==> t
   *
   *    ...CHOOSE applications...
   *
   *    |- ?t1. t1 = u1      {t1 = u1} |- A ==> t
   *    ------------------------------------------  CHOOSE (t1, |- ?t1. t1 = u1)
   *                 |- A ==> t
   *
   *
   *    |- A ==> t
   *    ------------UNDISCH
   *      A |- t
   *)
  fun INST_IMP_EQ_TAC lemma (A, t) =
    let val lemma_unquantified = SPEC_ALL lemma in (* 1. *)
    let val lemma_conjuncts = (strip_conj o #1 o dest_imp o concl) lemma_unquantified in (* 2. *)
    let val (term_matchings, type_matchings, xeq_thms) = find_match_assumptions_substitutions lemma_conjuncts A (* 3. *)
        val instantiated_lemma_except_eqs = INST_TY_TERM (term_matchings, type_matchings) lemma_unquantified (* 4. *)
        fun compute_lemma_instantiation_and_xthm_applications A t xthms =
          let fun process_xthms invalid_variable_names [] = ([], [], [], [])
                | process_xthms invalid_variable_names ((old_lhs, xthm)::lhs_xthms) =
                    let val (xvar, eq) = (dest_exists o concl) xthm in
                    let val rhs = (#2 o dest_eq) eq
                        val preferred_lhs = mk_var (term_to_string old_lhs, type_of xvar) in
                    let val new_lhs = gen_variant is_constname "" invalid_variable_names preferred_lhs in
                    let val new_assumption = mk_eq (new_lhs, rhs)
                        val lemma_match = {redex = preferred_lhs, residue = new_lhs}
                        val goal_match = {redex = rhs, residue = new_lhs}
                        val xthm_application = (new_lhs, xthm)
                        val (lemma_matches, goal_matches, new_assumptions, xthm_applications) =
                          process_xthms (new_lhs::invalid_variable_names) lhs_xthms in
                      (lemma_match::lemma_matches,
                       goal_match::goal_matches,
                       new_assumption::new_assumptions,
                       xthm_application::xthm_applications)
                    end end end end
              val goal_invalid_variable_names = free_varsl (t::A)
              val xthms_invalid_variable_names = free_varsl (map (fn (lhs, xthm) => concl xthm) xthms) in
          let val invalid_variable_names = goal_invalid_variable_names @ xthms_invalid_variable_names in
            process_xthms invalid_variable_names xthms
          end end in
    let val (lemma_matches, goal_matches, new_assumptions, xthm_applications) =
      compute_lemma_instantiation_and_xthm_applications A t xeq_thms
        val type_match = [] in
    let val instantiated_lemma = INST_TY_TERM (lemma_matches, type_match) instantiated_lemma_except_eqs in (* 5. *)
    let val instantiated_lemma_thm = CONJ_ANT_TO_HYP instantiated_lemma in
    let val instantiated_lemma_conclusion = concl instantiated_lemma_thm in
    let val A' = [instantiated_lemma_conclusion] @ new_assumptions @ (map (subst goal_matches) A)
        val t' = subst goal_matches t in (* 6. *)
    let val subgoal = [(A', t)]
        val validation_function = (* 7. *)
          (fn thms =>
           let val achieving_subgoal_thm = hd thms in (* One subgoal gives one achieving theorem which is the head. *)
           let val no_lemma_conclusion_thm = PROVE_HYP instantiated_lemma_thm achieving_subgoal_thm in
           let val assumptions_to_discharge = filter
             (fn assumption => not (exists (fn new_assumption => Term.compare (assumption, new_assumption) = EQUAL) new_assumptions))
             (hyp no_lemma_conclusion_thm) in
           let val discharged_thm = foldl
             (fn (assumption, thm) => DISCH assumption thm) no_lemma_conclusion_thm assumptions_to_discharge in
           let val subs_discharged_thm = SUBS (map ASSUME new_assumptions) discharged_thm in
           let val exists_application_thm = foldl
             (fn (xthm_application, thm) => CHOOSE xthm_application thm) subs_discharged_thm xthm_applications in
           let val achieving_goal_thm =
             let fun undischarge thm n = if n = 0 then thm else undischarge (UNDISCH thm) (n - 1) in
               undischarge exists_application_thm (length assumptions_to_discharge)
             end in
             achieving_goal_thm
           end end end end end end end) in
      (subgoal, validation_function)
    end end end end end end end end end

  (****************************************************************************)
  (*End of automatic lemma instantiation tactic********************************)
  (****************************************************************************)



  (****************************************************************************)
  (*Start of tactic appyling modus ponens on implication in assumptions and****)
  (*conclusion in goal, and instantiating as many existentially quantified*****)
  (*variables in the resulting goal as possible based on matching subterms of**)
  (*the goal to subterms in the assumptions.***********************************)
  (****************************************************************************)

  fun matching_to_instantiation [] relevant_variables matching = []
    | matching_to_instantiation (xvar::xvars) relevant_variables matching = 
        case List.find (fn {redex = from, residue = to} => same_term xvar from) matching of
          NONE =>
            if exists (same_term xvar) relevant_variables then
              (xvar, SOME xvar)::(matching_to_instantiation xvars relevant_variables matching)
            else
              (xvar, NONE     )::(matching_to_instantiation xvars relevant_variables matching)
        | SOME {redex = from, residue = to} => (xvar, SOME to)::(matching_to_instantiation xvars relevant_variables matching)

  (* To propritize matchings of large terms, the matchings of large terms should be the first argument. *)
  fun merge_instantiations [] [] = []
    | merge_instantiations [] (_::_) = fail (print "merge_instantiations: Cannot happen.\n")
    | merge_instantiations (_::_) [] = fail (print "merge_instantiations: Cannot happen.\n")
    (* from1 = from2 *)
    | merge_instantiations ((from1, NONE)::instantiation1)     ((from2, NONE)::instantiation2) =
        (from1, NONE)::(merge_instantiations instantiation1 instantiation2)
    | merge_instantiations ((from1, NONE)::instantiation1)     ((from2, SOME to2)::instantiation2) =
        (from2, SOME to2)::(merge_instantiations instantiation1 instantiation2)
    | merge_instantiations ((from1, SOME to1)::instantiation1) ((from2, NONE)::instantiation2) =
        (from1, SOME to1)::(merge_instantiations instantiation1 instantiation2)
    | merge_instantiations ((from1, SOME to1)::instantiation1) ((from2, SOME to2)::instantiation2) =
        (* to1 is chosen arbitrarily by assuming that terms occur once in assumption list. *)
        (from1, SOME to1)::(merge_instantiations instantiation1 instantiation2)

  (* If two terms match, and one variable is not mentioned in the instantiation,
   * then that variable is instantiated to a variable with the same name and
   * type.
   *)
  fun make_explicit_matching matching [] = matching
    | make_explicit_matching matching (fv::fvs) =
      let val explicit_matching = make_explicit_matching matching fvs in
        if all (fn {redex = from, residue = to} => not_same_term fv from) matching then (* Free variable not mentioned in instantiation. *)
          {redex = fv, residue = fv}::explicit_matching                                (* Add it. *)
        else
          explicit_matching
      end

  fun is_bound_matching bvars [] = []
    | is_bound_matching bvars ({redex = from, residue = to}::matching) =
      if exists (same_term to) bvars then
        raise (mk_HOL_ERR "helper_tactics" "is_bound_matching" "Instantiation to bound variable.")
      else
        {redex = from, residue = to}::(is_bound_matching bvars matching)

  fun instantiate_subterm xvars xsubterm_vars xsubterm subterm bvars =
    if term_size xsubterm > term_size subterm then (* Optimization: Cannot match a larger term to a smaller term. *)
        map (fn var => (var, NONE)) xvars
    else
      let val matching = #1 (match_term xsubterm subterm) in
      let val explicit_matching = make_explicit_matching matching (free_vars xsubterm) in (* Adds self-instantiations. *)
      let val filtered_matching = is_bound_matching bvars explicit_matching in            (* Instantiations to bounded variables not allowed. *)
          matching_to_instantiation xvars xsubterm_vars filtered_matching
      end end end
      handle _ =>
        if is_var subterm orelse is_const subterm then (* No instantiation exists. *)
          map (fn var => (var, NONE)) xvars
        else if is_comb subterm then
          let val (function, argument) = dest_comb subterm in
          let val function_matching = instantiate_subterm xvars xsubterm_vars xsubterm function bvars
              val argument_matching = instantiate_subterm xvars xsubterm_vars xsubterm argument bvars in
            merge_instantiations function_matching argument_matching
          end end
        else (* abstraction *)
          let val (bvar, body) = dest_abs subterm in
          let val bvars = bvar::bvars in
            instantiate_subterm xvars xsubterm_vars xsubterm body bvars
          end end

  fun is_instantiation_complete [] = true
    | is_instantiation_complete ((from, NONE   )::instantiation) = false
    | is_instantiation_complete ((from, SOME to)::instantiation) = is_instantiation_complete instantiation

  fun find_instantiation xvars xsubterm_vars xsubterm [] current_instantiation = current_instantiation (* Computed matching. *)
    | find_instantiation xvars xsubterm_vars xsubterm (assumption::assumptions) current_instantiation =
        if is_instantiation_complete current_instantiation then
          current_instantiation
        else
          let val additional_instantiation = instantiate_subterm xvars xsubterm_vars xsubterm assumption [] in
          let val current_instantiation = merge_instantiations current_instantiation additional_instantiation in (* old first arg *)
            find_instantiation xvars xsubterm_vars xsubterm assumptions current_instantiation
          end end

  (* xsubterm_vars is the set of free variables in xsubterm that occur in xvars. That is, the variables that may be matched in xsubterm. *)
(*
  fun instantiation_xsubterm xvars xsubterm_vars xsubterm assumptions current_instantiation =
    if is_instantiation_complete current_instantiation then
      current_instantiation (* Instantiation complete. *)
    else if is_var xsubterm orelse is_const xsubterm then
      current_instantiation (* Variables are not considered without context. Constants do not contribute. *)
    else
      let val current_instantiation = find_instantiation xvars xsubterm_vars xsubterm assumptions current_instantiation in
        if is_instantiation_complete current_instantiation then
          current_instantiation
        else if is_comb xsubterm then
          let val xfunction = (#1 o dest_comb) xsubterm in
          let val xfunction_vars = filter (fn xvar => var_occurs xvar xfunction) xvars in
          let val current_instantiation = instantiation_xsubterm xvars xfunction_vars xfunction assumptions current_instantiation in
            if is_instantiation_complete current_instantiation then
              current_instantiation
            else
              let val xargument = (#2 o dest_comb) xsubterm in
              let val xargument_vars = filter (fn xvar => var_occurs xvar xargument) xvars in
              let val current_instantiation =
                  instantiation_xsubterm xvars xargument_vars xargument assumptions current_instantiation in
                current_instantiation
              end end end
          end end end
        else (* is_abs xsubterm *)
          let val xbody = (#2 o dest_abs) xsubterm in
          let val xbody_vars = filter (fn xvar => var_occurs xvar xbody) xvars in
          let val current_instantiation = instantiation_xsubterm xvars xbody_vars xbody assumptions current_instantiation in
            current_instantiation
          end end end
      end
*)
  fun instantiation_xsubterm xvars xsubterm_vars xsubterm assumptions current_instantiation =
    if is_instantiation_complete current_instantiation then
      current_instantiation (* Instantiation complete. *)
    else if is_var xsubterm orelse is_const xsubterm then
      current_instantiation (* Variables are not considered without context. Constants do not contribute. *)
    else
      let val current_instantiation = find_instantiation xvars xsubterm_vars xsubterm assumptions current_instantiation in
        if is_instantiation_complete current_instantiation then
          current_instantiation
        else if is_comb xsubterm then
          let val xfunction = (#1 o dest_comb) xsubterm in
          let val xfunction_vars = filter (fn xvar => var_occurs xvar xfunction) xvars in
          let val current_instantiation = instantiation_xsubterm xvars xfunction_vars xfunction assumptions current_instantiation in
            if is_instantiation_complete current_instantiation then
              current_instantiation
            else
              let val xargument = (#2 o dest_comb) xsubterm in
              let val xargument_vars = filter (fn xvar => var_occurs xvar xargument) xvars in
              let val current_instantiation =
                  instantiation_xsubterm xvars xargument_vars xargument assumptions current_instantiation in
                current_instantiation
              end end end
          end end end
        else (* is_abs xsubterm *)
          let val xbody = (#2 o dest_abs) xsubterm in
          let val xbody_vars = filter (fn xvar => var_occurs xvar xbody) xvars in
          let val current_instantiation = instantiation_xsubterm xvars xbody_vars xbody assumptions current_instantiation in
            current_instantiation
          end end end
      end

  (* Computes the instantiation of xvars with respect to the existentially
   * quantified conclusion ?xvars. xbody and the assumptions of the goal.
   *
   * Problem: Given a goal with assumptions A and an existentially quantified
   * conclusion in the goal: ?x1...xn. t, find instantiations v1...vn of x1...xn
   * such that each v1...vn occurs in A, enabling, potentially via additional
   * reasoning, a derivation of t[v1...vn/x1...xn].
   *
   * Algorithm:
   * 0. Let s be xbody.
   * 1. Iterate through all assumptions and compute and merge instantiations
   *    matching s with assumptions.
   * 2. If a complete matching is found of all free variables, return and
   *    terminate.
   * 3. If no complete matching is found, extend the matching by go to 1. and set
   *    s to one child, and if necessary, repeat for the other child.
   *)
  fun find_instantiation_xbody xvars xbody assumptions =
    let val mapped_xvars = filter (fn xvar => var_occurs xvar xbody) xvars in
    let val current_instantiation = map (fn var => (var, NONE)) xvars in
      instantiation_xsubterm xvars mapped_xvars xbody assumptions current_instantiation
    end end

  (* Constructs the following proof tree (application of CHOOSE with a bound
   * variable works since the bound variable is thus not free):
   *
   *                                                              t |- t
   *                                           -----------------------------------EXISTS(?xn. t, xn)
   *                                                              t |- ?xn. t
   * 
   *                                                               ...
   * 
   *                                                              t |- ?x2...xn. t
   *                                      ----------------------------------------EXISTS(?x1. t, x1)
   *                                                              t |- ?x1...xn. t
   *                                      ?xn-1. t |- ?xn-1. t    t |- ?x1...xn. t
   *                                      ----------------------------------------CHOOSE (xn-1, ?xn-1. t |- ?xn-1. t)
   *                                               ?xn-1. t |- ?x1...xn. t
   * 
   *                                                       ...
   * 
   * ?xn x1..xn-1. t |- ?xn x1..xn-1. t       ?x1...xn-1. t |- ?x1...xn. t
   * ---------------------------------------------------------------------CHOOSE (xn, ?xn x1...xn-1. t |- ?xn x1...xn-1. t)
   *                               ?xn x1...xn-1. t |- ?x1...xn. t
   * A |- ?xn x1...xn-1. t         ?xn x1...xn-1. t |- ?x1...xn. t
   * -------------------------------------------------------------PROVE_HYP
   *                         A |- ?x1...xn. t
   *
   * Input:
   * -xterm: '?xn x1...xn-1.t'
   * -n
   *
   * Output: ?xn x1...xn-1. t |- t
   *)

   (* Input:
    * -t |- t
    * -[xn...x1]
    *
    * Output: t |- ?x1...xn. t
    *)
   fun apply_exists [] xthm = xthm
     | apply_exists (x::xs) xthm =                   (* xthm: t |- ?x(i-1)...xn. t *)
         let val xterm = concl xthm in               (* ?x(i-1)...xn. t            *)
         let val xterm = mk_exists (x, xterm) in     (* ?xi...xn. t                *)
         let val xthm = EXISTS (xterm, x) xthm in    (* t |- ?xi...xn. t           *)
           apply_exists xs xthm                      (* t |- ?x1...xn. t           *)
         end end end

   (* Input:
    * -[xn-1, xn-2, ..., x1, xn]
    * -t |- ?x1...xn. t
    *
    * Output: ?xn x1...xn-1. t |- ?x1...xn. t
    *)
   fun apply_choose [] xthm = xthm
     | apply_choose (x::xs) xthm =                  (* xthm: ?x(i-1)...x(n-1). t |- ?x1...xn. t *)
         let val a = (hd o hyp) xthm in             (* ?x(i-1)...x(n-1). t                      *)
         let val axterm = mk_exists (x, a) in       (* ?xi...xn-1. t                            *)
         let val axthm = ASSUME axterm in           (* ?xi...xn-1. t |- ?xi...xn-1. t           *)
         let val xthm = CHOOSE (x, axthm) xthm in   (* ?xi...xn-1. t |- ?x1...xn. t             *)
           apply_choose xs xthm
         end end end end

   (* Inputs:
    * -xterm: ?x1...xn. t
    * -n
    *
    * Outputs:
    * -[x1, ..., xn]
    * -t
    *)
   fun split_exists xterm n =
     if n = 0 then
       ([], xterm)
     else
       let val (x, xterm) = dest_exists xterm in
       let val (xs, xterm) = split_exists xterm (n - 1) in
         (x::xs, xterm)
       end end

   (* Input:
    * -subgoal_achieving_thm: A |- ?xn x1...x(n-1). t
    * -n
    *
    * Output: A |- ?x1...x(n-1) xn. t
    *)
   fun rotate_exists subgoal_achieving_thm n =                                   (* subgoal_achieving_thm: A |- ?xn x1...x(n-1). t *)
     let val (xvars, t) = split_exists (concl subgoal_achieving_thm) n in        (* ([xn, x1, x2, ..., x(n-1)], t)                 *)
     let val xvars_hd = hd xvars                                                 (* xn                                             *)
         val xvars_tl_rev = List.rev (tl xvars) in                               (* [x(n-1), ..., x1]                              *)
     let val exists_xvars = xvars_hd::xvars_tl_rev in                            (* [xn, x(n-1), ..., x2, x1]                      *)
     let val exists_thm = apply_exists exists_xvars (ASSUME t)                   (* t |- ?x1...xn. t                               *)
         val choose_xvars = xvars_tl_rev @ [xvars_hd] in                         (* [x(n-1), ..., x1, xn]                          *)
     let val choose_thm = apply_choose choose_xvars exists_thm in                (* ?xn x1...x(n-1). t |- ?x1...xn. t              *)
     let val achieving_goal_thm = PROVE_HYP subgoal_achieving_thm choose_thm in  (* A |- ?x1...xn. t                               *)
       achieving_goal_thm
     end end end end end end
(*
  (* Input: [(xvar1, inst1), ..., (xvarn, instn)]
   *
   * Output: (false, (* Has not seen any SOME inst *)
   *          [],
   *          [],
   *          [(xvarc, NONE), ..., (xvard, NONE])
   *
   * Output: (true,  (* Has seen SOME inst *)
   *          [(xvar1, NONE), ..., (xvari, SOME insti)],
   *          [[(xvara, NONE), ..., (xvarb, SOME instb)], ..., [(xvara, NONE), ..., (xvarb, SOME instb)]],
   *          [(xvarc, NONE), ..., (xvard, NONE])
   *)
  fun group_xvars [] = (false, [], [], [])
    | group_xvars ((from, NONE)::instantiations) = (
        case group_xvars instantiations of
          (false, _      , _             , trail) => (false, []                   , []                     , (from, NONE)::trail)
        | (true , current, instantiations, trail) => (true , (from, NONE)::current, instantiations         , trail              ))
    | group_xvars ((from, SOME to)::instantiations) = (
        case group_xvars instantiations of
          (false, _      , _             , trail) => (true , [(from, SOME to)]    , []                     , trail              )
        | (true , current, instantiations, trail) => (true , [(from, SOME to)]    , current::instantiations, trail              ))

  (* Input: [(xvar1, inst1), ..., (xvarn, instn)]
   *
   * Output: [[none11...none1m, Inst1], ..., [nonen1...nonenp, Instn]],  without trailing NONEs.
   *)
  fun group_rotate_exists instantiations =
    case group_xvars instantiations of
      (false, current, instantiations, trail) => []
    | (true , current, instantiations, trail) => current::instantiations
*)

  (* Inputs:
   * -?x1...xp. t
   * -[(from1, NONE), ..., (fromi, SOME toi), ...], or [(from1, NONE), (from2, NONE), ..., (fromi, NONE), ... (fromp, NONE)]
   *
   * Outputs:
   * -?xn x1...x(n-1) x(n+1)...xp. t, or ?x1...xp. t, depending on the second argument.
   * -[(fromn, SOME ton), (from1, NONE), ..., (from(n-1), NONE), (from(n+1), SOME ), ...], or [] depending on the second argument.
   * -n.
   *)
  fun rotate_exists_instantiations xterm instantiation =
    let fun rotate_xterm_instantiations xterm [] = (xterm, [], NONE, 0)
          | rotate_xterm_instantiations xterm ((from, NONE)::instantiations) =
              let val (xvar, xbody) = dest_exists xterm in
              let val (xbody_shift, following_instantiations, instantiation, n) = rotate_xterm_instantiations xbody instantiations in
              let val xterm_shift = mk_exists (xvar, xbody_shift) in
                (xterm_shift, (from, NONE)::following_instantiations, instantiation, n + 1)
              end end end
          | rotate_xterm_instantiations xterm ((from, SOME to)::following_instantiations) =
              let val (xvar, xbody) = dest_exists xterm in
                (xbody, following_instantiations, SOME (xvar, to), 1)
              end in
      case rotate_xterm_instantiations xterm instantiation of
        (xterm, following_instantiations, NONE, _) => (xterm, [], 0)
      | (xterm, following_instantiations, SOME (xn, to), n) => (mk_exists (xn, xterm), (xn, SOME to)::following_instantiations, n)
    end

  fun INSTS_EXISTS_TAC [] (A, t) = ALL_TAC (A, t)
    | INSTS_EXISTS_TAC ((from, NONE)::instantiations) (A, t) = (
        case rotate_exists_instantiations t ((from, NONE)::instantiations) of
          (_ , []                                       , _) => ALL_TAC (A, t) (* t' = t *)
        | (_ , (_   , NONE)   ::_                       , _) => fail (print "INSTS_EXISTS_TAC: Cannot happen.\n")
        | (t', (from, SOME to)::following_instantiations, n) =>
            let val (xsubgoal, xvalidation) = EXISTS_TAC to (A, t') in
            let val (subgoal, xsvalidation) = INSTS_EXISTS_TAC following_instantiations (hd xsubgoal) in
            let val validation = fn thms =>
              let val subgoal_achieving_thm = xvalidation [xsvalidation thms] in
              let val goal_achieving_thm = rotate_exists subgoal_achieving_thm n in
                goal_achieving_thm
              end end in
              (subgoal, validation)
            end end end
    )
    | INSTS_EXISTS_TAC ((from, SOME to)::following_instantiations) (A, t) =
        let val (xsubgoal, xvalidation) = EXISTS_TAC to (A, t) in
        let val (subgoal, xsvalidation) = INSTS_EXISTS_TAC following_instantiations (hd xsubgoal) in
        let val validation = fn thms =>
          let val goal_achieving_thm = xvalidation [xsvalidation thms] in
            goal_achieving_thm
          end in
          (subgoal, validation)
        end end end

  (* A |- ?X. t ==> A |- ?X'. t[V/(X\X')], where V, X, X' are vectors of terms
   * and variables, where V are identified via a matching of subterms of t with
   * subterms of A. X' is the existentially quantified variables of X for which
   * no matching was found.
   *)
  fun PAXTAC (A, t) =
    if is_exists t then
      let val (xvars, xbody) = strip_exists t in
      let val instantiation = find_instantiation_xbody xvars xbody A in
      let val (subgoal, validation) = INSTS_EXISTS_TAC instantiation (A, t) in
        (subgoal, validation)
      end end end
    else
      ALL_TAC (A, t)

  (* 'A u {!X. s ==> t} |- t'
   * ==>
   * 'A |- ?X'. s[V/(X\X')]'
   *
   * where V, X, X' are vectors of terms and variables, where V are identified
   * via a matching of subterms of t with subterms of A. X' is the existentially
   * quantified variables of X for which no matching was found.
   *)
  fun INST_IMP_ASM_GOAL_TAC (A, t) =
    let val qimps = filter (fn ass => is_imp ass orelse is_forall ass andalso (is_imp o #2 o strip_forall) ass) A in
    let fun tactic [] (A, t) = raise (mk_HOL_ERR
        "helper_tactics"
        "INST_IMP_GOAL_TAC"
        "No implication among the assumptions with a conclusion that matches the conclusion of the goal.\n")
          | tactic (qimp::qimps) (A, t) = ((MATCH_MP_ASM_TAC qimp THEN PAXTAC) ORELSE (tactic qimps)) (A, t) in (* tactic must take argument, otherwise tactic qimps can be evaluated and that will raise an exception. *)
      tactic qimps (A, t)
    end end



  (****************************************************************************)
  (*End of tactic appyling modus ponens on implication in assumptions and******)
  (*conclusion in goal, and instantiating as many existentially quantified*****)
  (*variables in the resulting goal as possible based on matching subterms of**)
  (*the goal to subterms in the assumptions.***********************************)
  (****************************************************************************)




  (* A u {A1, ..., An} ?- t
   * ----------------------!x1...xm. A1 x1...xm /\ ... /\ An x1...xm ==> t x1...xm
   * 
   *)
  fun IMP_LEMMA_SOLVE_GOAL_TAC lemma = MATCH_MP_TAC lemma THEN PAXTAC THEN ASM_REWRITE_TAC []









  (****************************************************************************)
  (*Start of equal pairs tactic************************************************)
  (****************************************************************************)

  (* Input:
   * -A term.
   *
   * Output:
   * -False: The given term is not of the form '(p1, p2) = (a1, a2)'.
   * -True: The term is of the form '(p1, p2) = (a1, a2)'.
   *)
  fun is_equality_pair term =
    if is_eq term then
      let val (lhs, rhs) = dest_eq term in
        pairSyntax.is_pair lhs andalso pairSyntax.is_pair rhs
      end
    else
      false

  (* Input:
   * -A list of terms.
   *
   * Output:
   * -NONE: There is no subterm in terms of the form '(p1, p2)'.
   * -SOME subterm: There is a subterm in terms of the form '(p1, p2)'.
   *)
  val has_equality_pair = has_terms_subterm_property is_equality_pair

  (* Input:
   * -A term pair_term of the form '(p1, p2)'.
   *
   * Output:
   * -A theorem of the form '|- (p1, p2) = (a1, a2) ⇔ p1 = a1 ∧ p2 = a2'.
   *)
  fun equality_pair_conv equality_pair_term =
    let val (lhs, rhs) = dest_eq equality_pair_term in
    let val (lp1, lp2) = pairSyntax.dest_pair lhs
        val (rp1, rp2) = pairSyntax.dest_pair rhs
        val thm = GEN_ALL pairTheory.PAIR_EQ in
    let val rewrite_thm = ISPECL [lp2, lp1, rp2, rp1] thm in
      rewrite_thm
    end end end

  (* 'A u {(l1, ..., ln) = (r1, ..., rn)} ?- t'
   * ==>
   * 'A u {l1 = r1, ..., ln = rn} ?- t'
   *)
  val EQ_PAIR_ASM_TAC =
    let fun tactic (A, t) =
          case has_equality_pair A of
            NONE => raise (mk_HOL_ERR "helper_tactics" "EQ_PAIR_ASM_TAC" "No paired equality among the assumptions in the goal.")
          | SOME (mark, template, subterm_with_property, term) =>
            ((substitution_subgoal_validation equality_pair_conv subterm_with_property) THEN SPLIT_ASM_TAC) (A, t) in
      tactic THEN (REPEAT tactic)
    end

  (* A ?- (l1, ..., ln) = (r1, ..., rn)
   * ----------------------------------
   *   A ?- l1 = r1 /\ ... /\ ln = rn
   *)
  val EQ_PAIR_TAC =
    let fun tactic (A, t) =
          case has_equality_pair [t] of
            NONE => raise (mk_HOL_ERR "helper_tactics" "EQ_PAIR_TAC" "No paired equality in the conclusion of the goal.")
          | SOME (mark, template, subterm_with_property, term) =>
            substitution_subgoal_validation equality_pair_conv subterm_with_property (A, t) in
      tactic THEN (REPEAT tactic)
    end

  (****************************************************************************)
  (*End of equal pairs tactic**************************************************)
  (****************************************************************************)



  (****************************************************************************)
  (*Start of tactic for simplifying negations, conjunctions, disjunctions and**)
  (*implications.**************************************************************)
  (****************************************************************************)

  fun is_neg_neg term = if is_neg term then is_neg (dest_neg term) else false

  (* Input: ~~A.
   * Output: |- ~~A = A.
   *)
  fun neg_neg_simp_conv neg_neg =
    let val rw_lemmas = (CONJUNCTS o SPEC_ALL) boolTheory.NOT_CLAUSES in
    let val neg_neg_lemma =
      case List.find (fn lemma => (is_neg o dest_neg o boolSyntax.lhs o #2 o strip_forall o concl) lemma) rw_lemmas of
        NONE => raise (mk_HOL_ERR "helper_tactics" "neg_neg_simp_conv" "boolTheory.NOT_CLAUSES does not contain ~~A <=> A")
      | SOME neg_neg_lemma => SPEC_ALL neg_neg_lemma in
    let val instantiation = match_term ((boolSyntax.lhs o concl) neg_neg_lemma) neg_neg in
      INST_TY_TERM instantiation neg_neg_lemma
    end end end

  fun is_neg_f term = if is_neg term then same_term F (dest_neg term) else false

  (* |- ~F = T.
   *)
  val neg_f_simp_conv =
    let val rw_lemmas = (CONJUNCTS o SPEC_ALL) boolTheory.NOT_CLAUSES in
      case List.find (fn lemma => same_term F ((dest_neg o boolSyntax.lhs o #2 o strip_forall o concl) lemma)) rw_lemmas of
        NONE => raise (mk_HOL_ERR "helper_tactics" "neg_f_simp_conv" "boolTheory.NOT_CLAUSES does not contain ~F = T.")
      | SOME neg_f_lemma => neg_f_lemma
    end

  fun is_neg_t term = if is_neg term then same_term T (dest_neg term) else false

  (* |- ~T = F.
   *)
  val neg_t_simp_conv =
    let val rw_lemmas = (CONJUNCTS o SPEC_ALL) boolTheory.NOT_CLAUSES in
      case List.find (fn lemma => same_term T ((dest_neg o boolSyntax.lhs o #2 o strip_forall o concl) lemma)) rw_lemmas of
        NONE => raise (mk_HOL_ERR "helper_tactics" "neg_t_simp_conv" "boolTheory.NOT_CLAUSES does not contain ~T = F.")
      | SOME neg_t_lemma => neg_t_lemma
    end



  fun is_t_conj term = if is_conj term then same_term T ((#1 o dest_conj) term) else false

  (* Input: T /\ A.
   * Output: |- T /\ A = A.
   *)
  fun t_conj_simp_conv t_conj =
    let val rw_lemmas = (CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES in
    let val t_conj_lemma =
      case List.find (fn lemma => same_term T ((#1 o dest_conj o boolSyntax.lhs o concl) lemma)) rw_lemmas of
        NONE => raise (mk_HOL_ERR "helper_tactics" "t_conj_simp_conv" "boolTheory.AND_CLAUSES does not contain T /\\ A <=> T")
      | SOME t_conj_lemma => t_conj_lemma in
    let val instantiation = match_term ((boolSyntax.lhs o concl o SPEC_ALL) t_conj_lemma) t_conj in
      INST_TY_TERM instantiation t_conj_lemma
    end end end

  fun is_conj_t term = if is_conj term then same_term T ((#2 o dest_conj) term) else false

  (* Input: A /\ T.
   * Output: |- A /\ T = T.
   *)
  fun conj_t_simp_conv conj_t =
    let val rw_lemmas = (CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES in
    let val conj_t_lemma =
      case List.find (fn lemma => same_term T ((#2 o dest_conj o boolSyntax.lhs o concl) lemma)) rw_lemmas of
        NONE => raise (mk_HOL_ERR "helper_tactics" "conj_t_simp_conv" "boolTheory.AND_CLAUSES does not contain A /\\ T <=> T")
      | SOME conj_t_lemma => conj_t_lemma in
    let val instantiation = match_term ((boolSyntax.lhs o concl o SPEC_ALL) conj_t_lemma) conj_t in
      INST_TY_TERM instantiation conj_t_lemma
    end end end

  fun is_f_conj term = if is_conj term then same_term F ((#1 o dest_conj) term) else false

  (* Input: F /\ A.
   * Output: |- F /\ A = A.
   *)
  fun f_conj_simp_conv f_conj =
    let val rw_lemmas = (CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES in
    let val f_conj_lemma =
      case List.find (fn lemma => same_term F ((#1 o dest_conj o boolSyntax.lhs o concl) lemma)) rw_lemmas of
        NONE => raise (mk_HOL_ERR "helper_tactics" "f_conj_simp_conv" "boolTheory.AND_CLAUSES does not contain F /\\ A <=> A")
      | SOME f_conj_lemma => f_conj_lemma in
    let val instantiation = match_term ((boolSyntax.lhs o concl o SPEC_ALL) f_conj_lemma) f_conj in
      INST_TY_TERM instantiation f_conj_lemma
    end end end

  fun is_conj_f term = if is_conj term then same_term F ((#2 o dest_conj) term) else false

  (* Input: A /\ F.
   * Output: |- A /\ F = A.
   *)
  fun conj_f_simp_conv conj_f =
    let val rw_lemmas = (CONJUNCTS o SPEC_ALL) boolTheory.AND_CLAUSES in
    let val conj_f_lemma =
      case List.find (fn lemma => same_term F ((#2 o dest_conj o boolSyntax.lhs o concl) lemma)) rw_lemmas of
        NONE => raise (mk_HOL_ERR "helper_tactics" "conj_f_simp_conv" "boolTheory.AND_CLAUSES does not contain A /\\ F <=> F")
      | SOME conj_f_lemma => conj_f_lemma in
    let val instantiation = match_term ((boolSyntax.lhs o concl o SPEC_ALL) conj_f_lemma) conj_f in
      INST_TY_TERM instantiation conj_f_lemma
    end end end



  fun is_t_disj term = if is_disj term then same_term T ((#1 o dest_disj) term) else false

  (* Input: T \/ A.
   * Output: |- T \/ A = T.
   *)
  fun t_disj_simp_conv t_disj =
    let val rw_lemmas = (CONJUNCTS o SPEC_ALL) boolTheory.OR_CLAUSES in
    let val t_disj_lemma =
      case List.find (fn lemma => same_term T ((#1 o dest_disj o boolSyntax.lhs o concl) lemma)) rw_lemmas of
        NONE => raise (mk_HOL_ERR "helper_tactics" "t_disj_simp_conv" "boolTheory.OR_CLAUSES does not contain T \\/ A <=> T")
      | SOME t_disj_lemma => t_disj_lemma in
    let val instantiation = match_term ((boolSyntax.lhs o concl o SPEC_ALL) t_disj_lemma) t_disj in
      INST_TY_TERM instantiation t_disj_lemma
    end end end

  fun is_disj_t term = if is_disj term then same_term T ((#2 o dest_disj) term) else false

  (* Input: A \/ T.
   * Output: |- A \/ T = T.
   *)
  fun disj_t_simp_conv disj_t =
    let val rw_lemmas = (CONJUNCTS o SPEC_ALL) boolTheory.OR_CLAUSES in
    let val disj_t_lemma =
      case List.find (fn lemma => same_term T ((#2 o dest_disj o boolSyntax.lhs o concl) lemma)) rw_lemmas of
        NONE => raise (mk_HOL_ERR "helper_tactics" "disj_t_simp_conv" "boolTheory.OR_CLAUSES does not contain A \\/ T <=> T")
      | SOME disj_t_lemma => disj_t_lemma in
    let val instantiation = match_term ((boolSyntax.lhs o concl o SPEC_ALL) disj_t_lemma) disj_t in
      INST_TY_TERM instantiation disj_t_lemma
    end end end

  fun is_f_disj term = if is_disj term then same_term F ((#1 o dest_disj) term) else false

  (* Input: F \/ A.
   * Output: |- F \/ A = A.
   *)
  fun f_disj_simp_conv f_disj =
    let val rw_lemmas = (CONJUNCTS o SPEC_ALL) boolTheory.OR_CLAUSES in
    let val f_disj_lemma =
      case List.find (fn lemma => same_term F ((#1 o dest_disj o boolSyntax.lhs o concl) lemma)) rw_lemmas of
        NONE => raise (mk_HOL_ERR "helper_tactics" "f_disj_simp_conv" "boolTheory.OR_CLAUSES does not contain F \\/ A <=> A")
      | SOME f_disj_lemma => f_disj_lemma in
    let val instantiation = match_term ((boolSyntax.lhs o concl o SPEC_ALL) f_disj_lemma) f_disj in
      INST_TY_TERM instantiation f_disj_lemma
    end end end

  fun is_disj_f term = if is_disj term then same_term F ((#2 o dest_disj) term) else false

  (* Input: A \/ F.
   * Output: |- A \/ F = A.
   *)
  fun disj_f_simp_conv disj_f =
    let val rw_lemmas = (CONJUNCTS o SPEC_ALL) boolTheory.OR_CLAUSES in
    let val disj_f_lemma =
      case List.find (fn lemma => same_term F ((#2 o dest_disj o boolSyntax.lhs o concl) lemma)) rw_lemmas of
        NONE => raise (mk_HOL_ERR "helper_tactics" "disj_f_simp_conv" "boolTheory.OR_CLAUSES does not contain A \\/ F <=> F")
      | SOME disj_f_lemma => disj_f_lemma in
    let val instantiation = match_term ((boolSyntax.lhs o concl o SPEC_ALL) disj_f_lemma) disj_f in
      INST_TY_TERM instantiation disj_f_lemma
    end end end



  fun is_t_imp term = if is_imp term then same_term T ((#1 o dest_imp) term) else false

  (* Input: T ==> A.
   * Output: |- T ==> A <=> A.
   *)
  fun t_imp_simp_conv t_imp =
    let val rw_lemmas = (CONJUNCTS o SPEC_ALL) boolTheory.IMP_CLAUSES in
    let val t_imp_lemma =
      case List.find (fn lemma => same_term T ((#1 o dest_imp o boolSyntax.lhs o concl) lemma)) rw_lemmas of
        NONE => raise (mk_HOL_ERR "helper_tactics" "t_imp_simp_conv" "boolTheory.IMP_CLAUSES does not contain T ==> A <=> A")
      | SOME t_imp_lemma => t_imp_lemma in
    let val instantiation = match_term ((boolSyntax.lhs o concl o SPEC_ALL) t_imp_lemma) t_imp in
      INST_TY_TERM instantiation t_imp_lemma
    end end end

  fun is_imp_t term = if is_imp term then same_term T ((#2 o dest_imp) term) else false

  (* Input: A ==> T.
   * Output: |- A ==> T <=> T.
   *)
  fun imp_t_simp_conv imp_t =
    let val rw_lemmas = (CONJUNCTS o SPEC_ALL) boolTheory.IMP_CLAUSES in
    let val imp_t_lemma =
      case List.find (fn lemma => same_term T ((#2 o dest_imp o boolSyntax.lhs o concl) lemma)) rw_lemmas of
        NONE => raise (mk_HOL_ERR "helper_tactics" "imp_t_simp_conv" "boolTheory.IMP_CLAUSES does not contain A ==> T <=> T")
      | SOME imp_t_lemma => imp_t_lemma in
    let val instantiation = match_term ((boolSyntax.lhs o concl o SPEC_ALL) imp_t_lemma) imp_t in
      INST_TY_TERM instantiation imp_t_lemma
    end end end

  fun is_f_imp term = if is_imp term then same_term F ((#1 o dest_imp) term) else false

  (* Input: F ==> A.
   * Output: |- F ==> A <=> T.
   *)
  fun f_imp_simp_conv f_imp =
    let val rw_lemmas = (CONJUNCTS o SPEC_ALL) boolTheory.IMP_CLAUSES in
    let val f_imp_lemma =
      case List.find (fn lemma => same_term F ((#1 o dest_imp o boolSyntax.lhs o concl) lemma)) rw_lemmas of
        NONE => raise (mk_HOL_ERR "helper_tactics" "f_imp_simp_conv" "boolTheory.IMP_CLAUSES does not contain F ==> A <=> T")
      | SOME f_imp_lemma => f_imp_lemma in
    let val instantiation = match_term ((boolSyntax.lhs o concl o SPEC_ALL) f_imp_lemma) f_imp in
      INST_TY_TERM instantiation f_imp_lemma
    end end end
(*
  fun is_imp_f term = if is_imp term then same_term F ((#2 o dest_imp) term) else false

  (* Input: A ==> F.
   * Output: |- A ==> F <=> ~A.
   *)
  fun imp_f_simp_conv imp_f =
    let val rw_lemmas = (CONJUNCTS o SPEC_ALL) boolTheory.IMP_CLAUSES in
    let val imp_f_lemma =
      case List.find (fn lemma => same_term F ((#2 o dest_imp o boolSyntax.lhs o concl) lemma)) rw_lemmas of
        NONE => raise (mk_HOL_ERR "helper_tactics" "imp_f_simp_conv" "boolTheory.IMP_CLAUSES does not contain A ==> F <=> ~F")
      | SOME imp_f_lemma => imp_f_lemma in
    let val instantiation = match_term ((boolSyntax.lhs o concl o SPEC_ALL) imp_f_lemma) imp_f in
      INST_TY_TERM instantiation imp_f_lemma
    end end end
*)

  (* Given a term of either form:
   * '~~A', '~F', '~T', returns
   * '|- ~~A <=> A', '|- ~F <=> T' '|- ~T <=> F'
   *
   * 'T /\ A', 'A /\ T', 'F /\ A', 'A /\ F', returns
   * '|- T /\ A <=> A', '|- A /\ T <=> A', '|- F /\ A <=> F', '|- A /\ F <=> F'
   *
   * 'T \/ A', 'A \/ T', 'F \/ A', 'A \/ F', returns
   * '|- T \/ A <=> T', '|- A \/ T <=> T', '|- F \/ A <=> A', '|- A \/ F <=> A'
   *
   * 'T ==> A', 'A ==> T', 'F ==> A', 'A ==> F', returns
   * '|- T ==> A <=> A', '|- A ==> T <=> T', '|- F ==> A <=> T', '|- A ==> F <=> ~A'
   *)
  fun neg_conj_disj_imp_simp_conv term =
    if is_neg_neg term then
      SOME (neg_neg_simp_conv term)
    else if is_neg_f term then
      SOME (neg_f_simp_conv)
    else if is_neg_t term then
      SOME (neg_t_simp_conv)
    else if is_t_conj term then
      SOME (t_conj_simp_conv term)
    else if is_conj_t term then
      SOME (conj_t_simp_conv term)
    else if is_f_conj term then
      SOME (f_conj_simp_conv term)
    else if is_conj_f term then
      SOME (conj_f_simp_conv term)
    else if is_t_disj term then
      SOME (t_disj_simp_conv term)
    else if is_disj_t term then
      SOME (disj_t_simp_conv term)
    else if is_f_disj term then
      SOME (f_disj_simp_conv term)
    else if is_disj_f term then
      SOME (disj_f_simp_conv term)
    else if is_t_imp term then
      SOME (t_imp_simp_conv term)
    else if is_imp_t term then
      SOME (imp_t_simp_conv term)
    else if is_f_imp term then
      SOME (f_imp_simp_conv term)
(*    else if is_imp_f term then (* Nothing to simplified. *)
      SOME (imp_f_simp_conv term)*)
    else
      NONE

  (* Given conv, property and term. If term = '...subterm...' where 'subterm'
   * satisfies property, and 'conv subterm' = '|- subterm = t', then returns
   * SOME |- 'term = ...t...'
   *)
  fun some_neg_conj_disj_imp_subterm_rw term =
    let fun subterm_rw subterm =
      case neg_conj_disj_imp_simp_conv subterm of
        SOME thm => SOME thm
      | NONE =>
        if is_var subterm orelse is_const subterm then
          NONE
        else if is_comb subterm then
          let val (function, argument) = dest_comb subterm in
            case subterm_rw function of
              NONE => (
              case subterm_rw argument of
                NONE => NONE
              | SOME thm => SOME (AP_TERM function thm))
            | SOME thm => SOME (AP_THM thm argument)
          end
        else if is_abs subterm then
          let val (bvar, body) = dest_abs subterm in
            case subterm_rw body of
              NONE => NONE
            | SOME thm => SOME (ABS bvar thm)
          end
        else
          NONE
    in
      subterm_rw term
    end

  fun have_neg_conj_disj_imp_simp [] = NONE
    | have_neg_conj_disj_imp_simp (term::terms) =
      case some_neg_conj_disj_imp_subterm_rw term of
        NONE => have_neg_conj_disj_imp_simp terms
      | SOME thm => SOME (term, thm)

  (* Simplifies all assumptions and the conclusion with respect to negation,
   * conjunction, disjunction and implication, where at least one operand is T or
   * F, except for double negation.
   *)
  fun NEG_CONJ_DISJ_IMP_SIMP_TAC (A, t) =
   case have_neg_conj_disj_imp_simp (t::A) of
     NONE => raise (mk_HOL_ERR "helper_tactics" "NEG_CONJ_DISJ_IMP_SIMP_TAC" "No negation, conjunction, disjunction or implication that is simplfifiable.")
   | SOME (rw_term, rw_thm) => RW_TERM_TAC rw_term rw_thm (A, t)

  (****************************************************************************)
  (*End of tactic for simplifying negations, conjunctions, disjunctions and****)
  (*implications.**************************************************************)
  (****************************************************************************)

  (****************************************************************************)
  (*Start of tactic that uses assumptions to simplify a universally quantified*)
  (*implication among the assumptions.*****************************************)
  (****************************************************************************)

  fun update_tyis ityvs tyis [] = SOME (tyis, ityvs)
    | update_tyis ityvs tyis ({redex = f, residue = t}::new_tyis) =
      if exists (same_type f) ityvs then
        (* f is in ityvs, and therefore not in tyis, and not in new_tyis either
         * since new_tyis does not contain duplicates.
         *)
        let val updated_tyis = update_tyis ityvs tyis new_tyis in
          if isSome updated_tyis then
            let val (tyis, ityvs) = valOf updated_tyis in
            let val tyis = tyis @ [{redex = f, residue = t}]  (* Add new instantiation. *)
                val ityvs = filter (not_same_type f) ityvs in (* Remove instantiated variable. *)
              SOME (tyis, ityvs)
            end end
          else
            NONE
        end
      else
        (* If not in ityvs, then either f has been instantiated, or f is not
         * instantiable and must be instantiated to itself.
         *)
        let val overlapping_instantiation = List.find (fn {redex = from, residue = to} => same_type f from) tyis in
          if isSome overlapping_instantiation then
            (* Already instantiated: Must be instantiated to same type, and not
             * added to the instantiation to avoid duplication.
             *)
            let val {redex = from, residue = to} = valOf overlapping_instantiation in
              if same_type f from then
                update_tyis ityvs tyis new_tyis
              else
                NONE
            end
          else if same_type f t then
            (* Not instantiable: Must be instantiated to itself, and not included
             * in the instantiation since f is not instantiable.
             *)
            update_tyis ityvs tyis new_tyis
          else
            NONE
        end

  fun type_instantiate tyis teis ityvs itevs from to =
    let val type_instantiation = find_explicit_type_variable_instantiation from to in
      if isSome type_instantiation then
        let val type_instantiation = valOf type_instantiation in
        let val updated_tyis = update_tyis ityvs tyis type_instantiation in
          if isSome updated_tyis then
            let val (tyis, ityvs) = valOf updated_tyis in
            let val teis = map (fn {redex = f, residue = t} => {redex = inst tyis f, residue = inst tyis t}) teis
                val itevs = map (inst tyis) itevs in
              SOME (tyis, teis, ityvs, itevs)
            end end
          else
            NONE
        end end
      else
        NONE
    end

  fun substitute_teis_to tei teis = map (fn {redex = f, residue = t} => {redex = f, residue = subst [tei] t}) teis

  fun update_teis tyis teis ityvs itevs [] = SOME (tyis, teis, ityvs, itevs)
    | update_teis tyis teis ityvs itevs ({redex = f, residue = t}::new_teis) =
      let val teis = update_teis tyis teis ityvs itevs new_teis in
        if isSome teis then
          let val (tyis, teis, ityvs, itevs) = valOf teis in
            if exists (same_term f) itevs then
              (* f is an instantiable variable, and can be instantiated to
               * anything.
               *)
(*              SOME (tyis, {redex = f, residue = t}::teis, ityvs, filter (not_same_term f) itevs)*)
              (* Must update uninstantiated variables in to-components in unupdated instantiations. *)
              SOME (tyis, {redex = f, residue = t}::(substitute_teis_to {redex = f, residue = t} teis), ityvs, filter (not_same_term f) itevs)
            else if same_term f t then
              (* f is not an instantiable variable, which means that it must be
               * instantiation instantiated to itelf.
               * teis and itevs do not change since a new instantiation has not
               * been made.
               *)
              SOME (tyis, teis, ityvs, itevs)
            else
              NONE
          end
        else
          NONE
      end

  (* Only instantiatable variables and consistent matchings are allowed. *)
  fun term_instantiate tyis teis ityvs itevs from l_or_r =
    let val instantiation = SOME (match_term from l_or_r) handle _ => NONE in
      if isSome instantiation then   (* Possible to match: 'from' type instantiated. *)
        let val (new_teis, new_tyis) = valOf instantiation in
        let val tyis = update_tyis ityvs tyis new_tyis in
          if isSome tyis then
            let val (tyis, ityvs) = valOf tyis in
            let val itevs = map (inst new_tyis) itevs in
              update_teis tyis teis ityvs itevs new_teis
            end end
          else
            NONE
        end end
      else
        NONE
    end

  fun expand_instantiation tyis teis ityvs itevs tyis_new teis_new ityvs_new itevs_new =
    let val tyis = update_tyis ityvs tyis tyis_new in
      if isSome tyis then
        let val (tyis, ityvs) = valOf tyis in
        let val itevs = map (inst tyis_new) itevs in
          update_teis tyis teis ityvs itevs teis_new
        end end
      else
        NONE
    end

  (* Rewriting right handside gives a left handside that can be matched to from
   * lemma conjunct.
   *
   * If to = r and from = l, then from = l = r = to.
   *)
  fun instantiable_r tyis teis ityvs itevs mark from to l r itevs_eq =
    if (not o null) itevs_eq then
      let val instantiationl = find_equality_instantiations [] [] from l itevs itevs_eq ityvs []
          val instantiationr = find_equality_instantiations [] [] to   r itevs itevs_eq ityvs [] in
        if isSome instantiationl andalso isSome instantiationr then
          let val (tyis_newl, _, teis_newl, teis_eql, ityvs_newl, itevs_newl) = valOf instantiationl
              val (tyis_newr, _, teis_newr, teis_eqr, ityvs_newr, itevs_newr) = valOf instantiationr in
          let val tyis_new = merge_type_instantiations tyis_newl tyis_newr
              val teis_new = merge_term_instantiations teis_newl teis_newr (* Type instantiations not necessary due to consistency *)
              val teis_eq = merge_term_instantiations teis_eql teis_eqr    (* checks below. *)
              val ityvs_new = filter (fn tyl => exists (same_type tyl) ityvs_newr) ityvs_newl
              val itevs_new = filter (is_in itevs_newr) itevs_newl in
            if (not o null) itevs_new orelse (not o isSome) tyis_new orelse (not o isSome) teis_new orelse (not o isSome) teis_eq then
              NONE
            else
              let val tyis_new = valOf tyis_new
                  val teis_new = valOf teis_new
                  val teis_eq = valOf teis_eq in
              let val instantiation = expand_instantiation tyis teis ityvs itevs tyis_new teis_new ityvs_new itevs_new in
                if isSome instantiation then
                  let val (tyis, teis, ityvs, itevs) = valOf instantiation in
                  let val qeq = list_mk_forall (itevs_eq, mk_eq (l, r)) in
                  let val asm_rw_is = (mark, {redex = to, residue = subst teis_eq l}, qeq, teis_eq, true) in
                    SOME (tyis, teis, ityvs, itevs, asm_rw_is)
                  end end end
                else
                  NONE
              end end
          end end
        else
          NONE
      end
    else if same_term to r then
      let val instantiation = term_instantiate tyis teis ityvs itevs from l in
        if isSome instantiation then
          let val (tyis, teis, ityvs, itevs) = valOf instantiation in
            (* Rewrite 'to' to 'from' via 'l = r', mark associated with the
             * position to rewrite in the assumption, and where 'l = r' must be
             * reflected.
             *)
            SOME (tyis, teis, ityvs, itevs, (mark, {redex = to, residue = l}, mk_eq (l, r), [], true))
          end
        else
          NONE
      end
    else
      NONE

  (* Rewriting left handside gives a right handside that can be matched to from
   * lemma conjunct.
   *
   * Try matching right handside first, and if it does not work, try the left
   * handside.
   *
   * to is wanted, and from is what is there now. But if to is instantiable, then
   * a matching equation is found if the instantiable variables of to from the
   * lemma are instantiated to match the appropriate side of the equation l = r.
   *
   * If to = l, and from = r, then from = r = l = to.
   *)
  fun instantiable_l tyis teis ityvs itevs mark from to l r itevs_eq =
    if (not o null) itevs_eq then (* Universally quantified equation. *)
      let val instantiationl = find_equality_instantiations [] [] to   l []    itevs_eq ityvs []
          val instantiationr = find_equality_instantiations [] [] from r itevs itevs_eq ityvs [] in (*itevs = [] for assumption to. *)
        if isSome instantiationl andalso isSome instantiationr then
          let val (tyis_newl, _, teis_newl, teis_eql, ityvs_newl, itevs_newl) = valOf instantiationl
              val (tyis_newr, _, teis_newr, teis_eqr, ityvs_newr, itevs_newr) = valOf instantiationr in
          let val tyis_new = merge_type_instantiations tyis_newl tyis_newr
              val teis_new = merge_term_instantiations teis_newl teis_newr (* Type instantiations not necessary due to consistency *)
              val teis_eq = merge_term_instantiations teis_eql teis_eqr    (* checks below. *)
              val ityvs_new = filter (fn tyl => exists (same_type tyl) ityvs_newr) ityvs_newl
              val itevs_new = filter (is_in itevs_newr) itevs_newl in
            if (not o null) itevs_new orelse (not o isSome) tyis_new orelse (not o isSome) teis_new orelse (not o isSome) teis_eq then
              (* Quantified variables of the equation must be instantiated,
               * therefore, current instantiation is not sufficient and the case
               * from = l = r = to is checked,
               *
               * and the type and term instantiations of the equation's left and right hand
               * sides must be consistent with each other.
               *)
              instantiable_r tyis teis ityvs itevs mark from to l r itevs_eq
            else
              let val tyis_new = valOf tyis_new
                  val teis_new = valOf teis_new
                  val teis_eq = valOf teis_eq in
              let val instantiation = expand_instantiation tyis teis ityvs itevs tyis_new teis_new ityvs_new itevs_new in
                if isSome instantiation then
                  let val (tyis, teis, ityvs, itevs) = valOf instantiation in
                  let val qeq = list_mk_forall (itevs_eq, mk_eq (l, r)) in
                  let val asm_rw_is = (mark, {redex = to, residue = subst teis_eq r}, qeq, teis_eq, false) in
                    SOME (tyis, teis, ityvs, itevs, asm_rw_is)
                  end end end
                else
                  instantiable_r tyis teis ityvs itevs mark from to l r itevs_eq
              end end
          end end
        else
          instantiable_r tyis teis ityvs itevs mark from to l r itevs_eq
      end
    else if same_term to l then
      let val instantiation = term_instantiate tyis teis ityvs itevs from r in (* Check if from and r can become identical. *)
        if isSome instantiation then
          let val (tyis, teis, ityvs, itevs) = valOf instantiation in
            (* Rewrite 'to' (which is 'l') to 'r' via 'l = r', where 'from' is
             * instantiated to become 'r', mark associated with the position to
             * rewrite in the assumption, and where 'l = r' does not need to be
             * reflected.
             *)
            SOME (tyis, teis, ityvs, itevs, (mark, {redex = to, residue = r}, mk_eq (l, r), [], false))
          end
        else
          instantiable_r tyis teis ityvs itevs mark from to l r itevs_eq
      end
    else
      instantiable_r tyis teis ityvs itevs mark from to l r itevs_eq

(*
val from = con
val to = asm
val EQS = eqs
val eq::eqs = eqs

from is a term we have.
to is a term we want.

We have the equation eq = (l = r). Can we transform from to to? Yes, if either
(subterms of from and to does not need to be considered because the terms of from
and to have been traversed as deep as possible to find a discrepancy):
-from = l = r = to
-from = r = l = to
*)

  fun instantiable_eq tyis teis ityvs itevs mark from to [] = NONE
    | instantiable_eq tyis teis ityvs itevs mark from to (eq::eqs) =
      let val (itevs_eq, eq) = strip_forall eq in
      let val (l, r) = dest_eq eq in
      let val instantiations = instantiable_l tyis teis ityvs itevs mark from to l r itevs_eq in
        if isSome instantiations then
          let val (tyis, teis, ityvs, itevs, asm_rw) = valOf instantiations in
            SOME (tyis, teis, ityvs, itevs, asm_rw)
          end
        else
          instantiable_eq tyis teis ityvs itevs mark from to eqs
      end end end

  (* from and to needs rewrite equations and potentially also type instantiations
   * to become identical. If their types can be made the same, then a template
   * for how 'to' shall be changed is returned.
   *)
  fun check_mismatch eqs tyis teis ityvs itevs from to =
    let val tyis = type_instantiate tyis teis ityvs itevs from to in
      if isSome tyis then
        let val (tyis, teis, ityvs, itevs) = valOf tyis in
        let val from = inst tyis from
            val mark = genvar (type_of to) in
        let val is_asm_rw = instantiable_eq tyis teis ityvs itevs mark from to eqs in
          if isSome is_asm_rw then
            let val (tyis, teis, ityvs, itevs, asm_rw) = valOf is_asm_rw in
              SOME (tyis, teis, ityvs, itevs, mark, [asm_rw], [mark])
            end
          else
            NONE
        end end end
      else
        NONE (* Mismatching types. *)
    end

  (* from is a variable. *)
  fun find_mismatching_instantiation_variable eqs tyis teis ityvs itevs from to bvars =
    case bvar_match from to bvars of
      FAIL => NONE
    | MATCH =>
      let val tyis = type_instantiate tyis teis ityvs itevs from to in
        if isSome tyis then
          let val (tyis, teis, ityvs, itevs) = valOf tyis in
            SOME (tyis, teis, ityvs, itevs, to, [], [])
          end
        else
          NONE
      end
    | FREE => 
      if is_in itevs from then                             (* from is an instantiable variable. *)
        let val tyis = type_instantiate tyis teis ityvs itevs from to in
          if isSome tyis then
            let val (tyis, teis, ityvs, itevs) = valOf tyis in
            let val from = inst tyis from in
            let val teis = {redex = from, residue = to}::teis
                val itevs = filter (not_same_term from) itevs in
              SOME (tyis, teis, ityvs, itevs, to, [], [])
            end end end
          else
            NONE                                           (* Only mismatching types can lead to "mismatching" failure. *)
        end
      else if same_term from to then                       (* Uninstantiable variable denotes a fixed unknown object/element/term. *)
        SOME (tyis, teis, ityvs, itevs, to, [], [])        (* Same terms, nothing to instantiate nor rewrite. *)
      else if is_var to then
        if term_to_string from = term_to_string to then    (* Same variable name: Check if only types differ. *)
          let val tyis = type_instantiate tyis teis ityvs itevs from to in
            if isSome tyis then
              let val (tyis, teis, ityvs, itevs) = valOf tyis in
                SOME (tyis, teis, ityvs, itevs, to, [], [])(* Types can be made the same. *)
              end
            else
              NONE                                         (* Types cannot be made the same. *)
          end
        else                                               (* Different variables, denoting different objects, and different types: *)
          check_mismatch eqs tyis teis ityvs itevs from to (* Requires rewriting. *)
      else                                                 (* 'from' is a variable, and 'to' is not a variable: Requires rewriting. *)
        check_mismatch eqs tyis teis ityvs itevs from to

  (* from is a constant. *)
  fun find_mismatching_instantiation_constant eqs tyis teis ityvs itevs from to =
    if is_const to then
      if same_term from to then
        SOME (tyis, teis, ityvs, itevs, to, [], [])        (* Same terms, nothing to instantiate nor substitute. *)
      else
        let val tyis = type_instantiate tyis teis ityvs itevs from to in
          if isSome tyis then
            let val (tyis, teis, ityvs, itevs) = valOf tyis in
              if same_term (inst tyis from) to then
                SOME (tyis, teis, ityvs, itevs, to, [], [])(* 'from' and 'to' denote the same constant after type instantiation. *)
              else
                NONE                                       (* 'from' and 'to' denote different constants after type instantiation. *)
            end
          else
            NONE                                           (* Cannot make the types identical.  *)
        end
    else
      check_mismatch eqs tyis teis ityvs itevs from to     (* 'from' is a constant, and 'to' is not a constant: Requires rewriting. *)

  (* from is an application. *)
  fun find_mismatching_instantiation_application find_mismatching_instantiation_rec eqs tyis teis ityvs itevs from to bvars =
    if is_comb to then
      let val (from_fun, from_arg) = dest_comb from
          val (to_fun, to_arg) = dest_comb to in
      let val mismatch_arg = find_mismatching_instantiation_rec eqs tyis teis ityvs itevs from_arg to_arg bvars in
        if isSome mismatch_arg then
          let val (tyis, teis, ityvs, itevs, template_arg, asm_rws_arg, marks_arg) = valOf mismatch_arg in
              (* Types must be updated in from_fun to reflect type updates of
               * itevs. Likewise instantiation of term variables.
               *)
          let val from_fun = subst teis (inst tyis from_fun)
              (* Type updating from_fun necessitates type updating left component
               * of bvars.
               *)
              val bvars = map (fn (f, t) => (inst tyis f, t)) bvars in
          let val mismatch_fun = find_mismatching_instantiation_rec eqs tyis teis ityvs itevs from_fun to_fun bvars in
            if isSome mismatch_fun then
              let val (tyis, teis, ityvs, itevs, template_fun, asm_rws_fun, marks_fun) = valOf mismatch_fun in
                SOME (tyis, teis, ityvs, itevs, mk_comb (template_fun, template_arg), asm_rws_fun @ asm_rws_arg, marks_fun @ marks_arg) 
              end
            else
              check_mismatch eqs tyis teis ityvs itevs from to
          end end end
        else
          check_mismatch eqs tyis teis ityvs itevs from to
      end end
    else
      check_mismatch eqs tyis teis ityvs itevs from to

  fun find_mismatching_instantiation_abstraction find_mismatching_instantiation_rec eqs tyis teis ityvs itevs from to bvars =
    if is_abs to then (* is_abs from *)
      let val (bv_from, body_from) = dest_abs from
          val (bv_to, body_to) = dest_abs to in
      let val bvars = (bv_from, bv_to)::bvars in
      let val mismatch = find_mismatching_instantiation_rec eqs tyis teis ityvs itevs body_from body_to bvars in
        if isSome mismatch then
          mismatch
        else
          check_mismatch eqs tyis teis ityvs itevs from to
      end end end
    else
      check_mismatch eqs tyis teis ityvs itevs from to

  (* Input:
   * -invalid_marks: variable names 
   * -instantiatable_vars: Variables in from that can be matched/instantiated to
   *  anything.
   * -from: A term that is to be made equal to to by term and type variable
   *  substitutions, where only term variables in instantiatable_vars can be
   *  substituted.
   * -to: A term that is to be made equal to from by variable substitutions in
   *  from.
   *
   * Output:
   * -NONE: from cannot be made equal to to by term and type variable
   *  substitutions.
   * -SOME (term_matching, type_matching, template, [(marki, to_oldi, to_newi), ...]):
   *  from is made equal to to by the term and type variable substitutions
   *  term_matching and type_matching, provided that to is first changed by
   *  substituting the occurrences of to_oldi at position marki in template to
   *  to_newi.
   *
   * There are three types of variables:
   * -Bounded variables: Remove from matching. Inconcistency is checked in
   *  combinations when matchings are merged. Are made instantiatable.
   * -Universally quantified variables: Can be matched to anything. Are made
   *  instantiatable.
   * -Term/Object/Element variables: Must not be matched and must be equal at
   *  corresponding positions in from and to.
   *)
  fun find_mismatching_instantiation_rec eqs tyis teis ityvs itevs from to bvars =
    if is_var from then
      find_mismatching_instantiation_variable eqs tyis teis ityvs itevs from to bvars
    else if is_const from then
      find_mismatching_instantiation_constant eqs tyis teis ityvs itevs from to
    else if is_comb from then
      find_mismatching_instantiation_application find_mismatching_instantiation_rec eqs tyis teis ityvs itevs from to bvars
    else
      find_mismatching_instantiation_abstraction find_mismatching_instantiation_rec eqs tyis teis ityvs itevs from to bvars

  fun find_mismatching_instantiation eqs tyis teis ityvs itevs from to =
    let val bvars = [] : (Term.term * Term.term) list in
      find_mismatching_instantiation_rec eqs tyis teis ityvs itevs from to bvars
    end

  (* Inputs:
   * -qvars: Variables in conjunct that can be used to rewrite conjunct.
   * -eqs: Equations 'l = r' that can be used to rewrite rewritable_term, both
   *  directions considered l -> r and r -> l.
   * -instantiatable_term: Term to be made equal to rewritable_term modulo
   *  instantiations of qvars.
   * -rewritable_term: Term to be made equal to instantiatable_term modulo
   *  rewrites by means of equations in eqs.
   *
   * Outputs:
   * -NONE
   * -SOME (term_instantiation, type_instantiation, template, mark_unrefl_refl_instantiations, true):
   *  *Instantiate instantiatable_term with term_instantiation and type_instantiation
   *  *Template is used to denote occurrences of subterms that shall be
   *   substituted in rewritable_term: template[fromi/marki] = rewritable_term[fromi/toi],
   *   mark_unrefl_refl_instantiations = [(marki, oldi |-> newi, 'li = ri')],
   *   where li = ri is in eqs, and either li = oldi and ri = newi or li = newi and ri = oldi.
   *  *true means that rewritable_term = 'l = r' must be reflected to 'r = l'.
   *  Result is:
   *  instantiatable_term[term_instantiation,type_instantiation] = 'r[newi/oldi] = l[newi/oldi]'.
   * -SOME (term_instantiation, type_instantiation, template, mark_unrefl_refl_instantiations, false):
   *  *Instantiate instantiatable_term with term_instantiation and type_instantiation
   *  *Template is used to denote occurrences of subterms that shall be
   *   substituted in rewritable_term: template[fromi/marki] = rewritable_term[fromi/toi],
   *   mark_unrefl_refl_instantiations = [(marki, oldi |-> newi, 'li = ri')],
   *   where li = ri is in eqs, and either li = oldi and ri = newi or li = newi and ri = oldi.
   *  *false means that rewritable_term is not an equation.
   *  Result is:
   *  instantiatable_term[term_instantiation,type_instantiation] = 'rewritable_term[newi/oldi]'.
   *)
  fun is_meet tyis teis ityvs itevs eqs instantiable_term rewritable_term =
    let val from = instantiable_term
        val to = rewritable_term in
    let val is_asm_rws = find_mismatching_instantiation eqs tyis teis ityvs itevs from to in
      if isSome is_asm_rws then
        let val (tyis, teis, ityvs, itevs, template, asm_rws, marks) = valOf is_asm_rws in
          SOME (tyis, teis, ityvs, itevs, template, asm_rws, false, marks)
        end
      else if is_eq from andalso is_eq to then
        let val to = mk_eq (rhs to, lhs to) in (* Reflect the equation to check whether that works. *)
        let val is_asm_rws = find_mismatching_instantiation eqs tyis teis ityvs itevs from to in
          if isSome is_asm_rws then
            let val (tyis, teis, ityvs, itevs, reflected_template, asm_rws, marks) = valOf is_asm_rws in
            let val template = mk_eq (rhs reflected_template, lhs reflected_template) in
              SOME (tyis, teis, ityvs, itevs, template, asm_rws, true, marks)
            end end
          else
            NONE
        end end
      else
        NONE
    end end

(*******************************************************************************)
(*******************************************************************************)
(*******************************************************************************)
(*******************************************************************************)
(*******************************************************************************)



(* Thoughts for ADD_INST_SUC_TYPE_TAC:

Given a conjunct and an assumption, both of which are instantiable, and a set of
equations without instantiable variables, identify instantiations of the conjunct
and the assumption, and rewrites of the assumption, such that the resulting terms
are identical.

When an instantiation occurs, then previous instantiations must be updated, since
their instantiation values may have the instantiable variable. This applies to
both the conjunct and the assumption, when either of the instantiations are
extended. For instance, if the instantiations of the conjunct are extended with a
subterm of the assumption that contains instantiable variables, later that
instantiable variable of the assumption might get instantiated and thus must be
updated in the previous instantiations of both the conjuncts and the assumption.
In addition, when a variable is instantiated, it must be removed from both sets
of instantiable variables of the conjunct and the assumption.

Since only instantiable variables can be instantiated, and they are disjoint
between the lemma and the assumptions, no variable capturing can occur, or
duplications which cause unnecessary restrictions.

The instantiations of the conjunct and the assumption may only contain "from"
variables that are quantified in the lemma and the assumption, respectively.
When an instantiable variable iv1 is instantiated to a term te1 containing an
instantiable variable iv2, then iv1 |-> te1 will be added to the instantiations,
and iv2 will become instantiable. If iv2 is instantiated to te2, then iv2 |-> va2
is added to the instantiations. Since the instantiations shall only have
instantiations with instantiated variables among their own quantified variables,
instantiations with instantiation variables not belonging to their own quantified
variables are removed, before instantiation.

Quantified variables in the lemma may occur as free variables in the assumptions:
Uniquify assumptions with respect to uniquified lemma.

The succedent must be updated when the conjunct gets instantiated, and its
instantiable variables must also be updated.

If a conjunct and an assumption cannot be fully instantiated, then only the
partial conjunct instantiations are keept. This avoids associating the assumption
with the conjunct if their instantiations can be extended later due to
intermediate instantiations between other conjuncts and assumptions.

Find rewrites and instantiations such that the two terms become identical:
-If corresponding variables are quantified and the variable of the conjunct does
 not occur in the succedent of the lemma, then they are instantiated to the
 quantified variable of the assumption.
-If corresponding variables are quantified and the variable of the conjunct does
 occur in the succedent of the lemma, then they remain quantified.
*)








  fun in_suc itevs_suc con_var = is_in itevs_suc con_var

(*
val from = asm
val to = con
*)

  fun find_type_instantiation ityvs tyis teis_con teis_asm from to =
    let val new_tyis = find_explicit_type_variable_instantiation from to          (* No duplicates in tym. *)
        fun update_tyis_ityvs [] = SOME (tyis, ityvs)
          | update_tyis_ityvs ({redex = f, residue = t}::new_tyis) =
            let val updated_tyis_ityvs = update_tyis_ityvs new_tyis in
              if isSome updated_tyis_ityvs then
                let val (tyis, ityvs) = valOf updated_tyis_ityvs in
                  if exists (same_type f) ityvs then (* f is instantiable. *)
                    SOME ((f |-> t)::tyis, filter (not_same_type f) ityvs)
                  else if same_type f t then         (* f is not instantiable, but is ok if f is unchanged. *)
                    updated_tyis_ityvs
                  else
                    NONE
                end
              else
                NONE
            end in
      if isSome new_tyis then
        let val new_tyis = valOf new_tyis in
        let val updated_tyis_ityvs = update_tyis_ityvs new_tyis in
          if isSome updated_tyis_ityvs then
            let val (tyis, ityvs) = valOf updated_tyis_ityvs in
            let val teis_con = map (fn {redex = f, residue = t} => {redex = inst tyis f, residue = inst tyis t}) teis_con
                val teis_asm = map (fn {redex = f, residue = t} => {redex = inst tyis f, residue = inst tyis t}) teis_asm in
              SOME (ityvs, tyis, teis_con, teis_asm)
            end end
          else
            NONE
        end end
      else
        NONE
    end

  (* Corresponding variables are quantified and the variable of the conjunct
   * occurs in the succedent of the lemma: They remain quantified.
   *)
  fun find_dmi_both_itev_suc con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs =
    let val type_instantiation = find_type_instantiation ityvs tyis teis_con teis_asm con asm in
      if isSome type_instantiation then
        let val (ityvs, tyis, teis_con, teis_asm) = valOf type_instantiation in
        let val con = inst tyis con
            val suc = inst tyis suc                   (* Updates types.                     *)
            val asm = asm

            val itevs_lem = map (inst tyis) itevs_lem
            val itevs_con = map (inst tyis) itevs_con
            val itevs_suc = map (inst tyis) itevs_suc (* Updates types.                     *)
            val itevs_asm = itevs_asm                 (* Types cannot change.               *)

            val teis_con = teis_con                   (* Type updated by type_instantiate.  *)
            val teis_asm = teis_asm

            val tyis = tyis                           (* Extended by by type_instantiate.   *)
            val ityvs = ityvs                         (* Extended by type_instantiate.      *)
            val template = asm                        (* Template for rewriting assumption. *)
            val asm_rws = []
            val marks = [] in
          SOME (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs, template, asm_rws, marks)
        end end
      else
        NONE
    end

  fun new_3teis itevs_lem itevs_oth {redex = f, residue = t} =
    if is_in itevs_oth f then
      let val new_teis_con = []
          val new_teis_asm = []
          val new_teis_udc = [{redex = f, residue = t}] in
        (new_teis_con, new_teis_asm, new_teis_udc)
      end
    else if is_in itevs_lem f then
      let val new_teis_con = [{redex = f, residue = t}]
          val new_teis_asm = []
          val new_teis_udc = [] in
        (new_teis_con, new_teis_asm, new_teis_udc)
      end
    else
      let val new_teis_con = []
          val new_teis_asm = [{redex = f, residue = t}]
          val new_teis_udc = [] in
        (new_teis_con, new_teis_asm, new_teis_udc)
      end

  fun new_23teis itevs_lem itevs_oth i_con i_asm =
    let val (new_teis_con_con, new_teis_asm_con, new_teis_udc_con) = new_3teis itevs_lem itevs_oth i_con
        val (new_teis_con_asm, new_teis_asm_asm, new_teis_udc_asm) = new_3teis itevs_lem itevs_oth i_asm in
    let val new_teis_con = new_teis_con_con @ new_teis_con_asm
        val new_teis_asm = new_teis_asm_con @ new_teis_asm_asm
        val new_teis_udc = new_teis_udc_con @ new_teis_udc_asm in
      (new_teis_con, new_teis_asm, new_teis_udc)
    end end

  (* If corresponding variables are quantified and the variable of the conjunct
   * does not occur in the succedent of the lemma, then they are instantiated
   * to a new unique variable.
   *)
  fun find_dmi_both_itev_not_suc con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs =
    let val type_instantiation = find_type_instantiation ityvs tyis teis_con teis_asm con asm in
      if isSome type_instantiation then
        let val (ityvs, tyis, teis_con, teis_asm) = valOf type_instantiation in
        let val te = genvar_term asm (* Instantiation term of same type as @asm. *)
            val itevs_lem = map (inst tyis) itevs_lem
            val itevs_con = map (inst tyis) itevs_con
            val itevs_suc = map (inst tyis) itevs_suc
            val itevs_asm = itevs_asm
            val con_ty = inst tyis con
            val suc_ty = inst tyis suc
            val asm_orig = asm in

        let val in_suc_con = false                 (* This function is only applied when con does not occur in the succedent. *)
            val in_suc_asm = exists (same_term con) (free_vars suc_ty)
            val con = te                           (* con instantiated to te. *)
            val suc = suc_ty                       (* con does not occur in suc: No need to substitute asm for con in suc. *)
            val asm = te                           (* asm instantiated to te. *)
            val i_con = con_ty |-> te
            val i_asm = asm_orig |-> te in

        let val itevs_con = filter (fn v => not_same_term con_ty v andalso not_same_term asm_orig v) itevs_con
            val itevs_suc = filter (fn v => (* con not in suc *)           not_same_term asm_orig v) itevs_suc
            val itevs_asm = filter (fn v => not_same_term con_ty v andalso not_same_term asm_orig v) itevs_asm

            val (new_teis_con, new_teis_asm, new_teis_udc) = new_23teis itevs_lem itevs_oth i_con i_asm in

        let val teis_con = (substitute_teis_to i_asm (substitute_teis_to i_con teis_con)) @ new_teis_con
            val teis_asm = (substitute_teis_to i_asm (substitute_teis_to i_con teis_asm)) @ new_teis_asm
            val teis_udc = (substitute_teis_to i_asm (substitute_teis_to i_con teis_udc)) @ new_teis_udc

            val tyis = tyis                                            (* Extended by by type_instantiate.                *)
            val ityvs = ityvs                                          (* Extended by type_instantiate.                   *)
            val template = asm_orig                                    (* Template for rewriting assumption.              *)
            val asm_rws = []                                           (* The assumption does not need to be rewritten.   *)
            val marks = [] in                                          (* No marks since the assumption is not rewritten. *)
          SOME (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs, template, asm_rws, marks)
        end end end end end
      else
        NONE
    end

  (* @con_asm: True if and only if iv is in con, and otherwise iv is in asm.
   *)
  fun new_itevs itevs_con itevs_suc itevs_asm iv te =
    let val iv_con = is_in itevs_con iv
        val iv_suc = is_in itevs_suc iv
        val iv_asm = is_in itevs_asm iv in
    (* -Variables to add: The instantiable variables occuring in the
     *  instantiation term.
     * -Variables to remove: The instantiated variable.
     * If asm is instantiated, do new instantiable variables occur in con? No,
     * because those variables already occur in itevs_con.
     *)
    let val new_itevs_con = if iv_con then filter (is_in itevs_asm) (free_vars te) else []
        val new_itevs_suc = if iv_suc then filter (is_in itevs_asm) (free_vars te) else []
        val new_itevs_asm = if iv_asm then filter (is_in itevs_con) (free_vars te) else [] in
    (* Removes the instantiated variable from all instantiable variable sets,
     * since it may occur in all of them due to instantiations of previous
     * subtrees.
     *)
    let val itevs_con = union_lists same_term (filter (not_same_term iv) itevs_con) new_itevs_con
        val itevs_suc = union_lists same_term (filter (not_same_term iv) itevs_suc) new_itevs_suc
        val itevs_asm = union_lists same_term (filter (not_same_term iv) itevs_asm) new_itevs_asm in
      (itevs_con, itevs_suc, itevs_asm)
    end end end

  fun new_teis itevs_lem itevs_oth itevs_con teis_con teis_asm teis_udc i =
    let val teis_con = substitute_teis_to i teis_con
        val teis_asm = substitute_teis_to i teis_asm
        val teis_udc = substitute_teis_to i teis_udc in
      if is_in itevs_oth (#redex i) then
        (teis_con, teis_asm, teis_udc @ [i])
      else if is_in itevs_lem (#redex i) then
        (teis_con @ [i], teis_asm, teis_udc)
      else
        (teis_con, teis_asm @ [i], teis_udc)
    end

  (* Given @teis_con and @itevs_con being type updated as a result of
   * instantiating @iv to @te, with @tyis being updated accordingly, returns
   * updated versions of the other parameters, reflecting the instantiation
   * iv |-> te.
   *
   * NOTE: iv and te must be type updated.
   *)
  fun extend_instantiations con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc iv te tyis is =
    (* Update types. *)
    let val itevs_lem = map (inst tyis) itevs_lem
        val itevs_con = map (inst tyis) itevs_con
        val itevs_suc = map (inst tyis) itevs_suc
        val itevs_asm = itevs_asm                             (* Types cannot change for assumptions. *)
        val iv = inst tyis iv
        val te = inst tyis te
        val con_ty = inst tyis con
        val suc_ty = inst tyis suc in

(*    let val con = subst [iv |-> te] con_ty
        val suc = subst [iv |-> te] suc_ty
        val asm = subst [iv |-> te] asm in*)

    (* New code: Instantiable variable of conjunct/assumption instantiated to instantiated assumption/conjunct. *)
    let val con = subst [iv |-> subst is te] con_ty
        val suc = subst [iv |-> subst is te] suc_ty
        val asm = subst [iv |-> subst is te] asm in
    let val (itevs_con, itevs_suc, itevs_asm) = new_itevs itevs_con itevs_suc itevs_asm iv te
        val (teis_con, teis_asm, teis_udc) = new_teis itevs_lem itevs_oth itevs_con teis_con teis_asm teis_udc (iv |-> subst is te) in
      (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc)
    end end end
(*
val iv = asm
val te = con
*)
  (* Only con is instantiable: Instantiate con to asm, update types, suc, and itevs.
   *)
  fun find_dmi_con con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs =
    let val type_instantiation = find_type_instantiation ityvs tyis teis_con teis_asm con asm in
      if isSome type_instantiation then
        let val (ityvs, tyis, teis_con, teis_asm) = valOf type_instantiation
            val asm_orig = asm in
        let val (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc) =
                extend_instantiations con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc con asm tyis teis_asm
            val template = asm_orig
            val asm_rws = []
            val marks = [] in
          SOME (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs, template, asm_rws, marks)
        end end
      else
        NONE
    end

  (* Only asm is instantiable.
   *)
  fun find_dmi_asm con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs =
    let val type_instantiation = find_type_instantiation ityvs tyis teis_con teis_asm con asm in
      if isSome type_instantiation then
        let val (ityvs, tyis, teis_con, teis_asm) = valOf type_instantiation
            val asm_orig = asm in
        let val (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc) =
                extend_instantiations con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc asm con tyis teis_con
            val tyis = tyis
            val ityvs = ityvs
            val template = asm_orig
            val asm_rws = []
            val marks = [] in
          SOME (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs, template, asm_rws, marks)
        end end
      else
        NONE
    end
(*
val (con0, suc0, asm0, itevs_lem0, itevs_oth0, itevs_con0, itevs_suc0, itevs_asm0, teis_con0, teis_asm0, teis_udc0, tyis0, ityvs0) =
    (con, suc, asm, itevs_lem, itevs_oth, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs)
*)  

  fun type_instantiate_teis_to tyis teis = map (fn {redex = from, residue = to} => {redex = from, residue = inst tyis to}) teis

(*
val teis = teis_con
val itevs = itevs_con
*)
  fun check_term_mismatch eqs tyis teis ityvs itevs con asm =
    let val mark = genvar (type_of asm) in
    let val is_asm_rw = instantiable_eq tyis teis ityvs itevs mark con asm eqs in
      if isSome is_asm_rw then
        let val (tyis, teis, ityvs, itevs, asm_rw) = valOf is_asm_rw in
          SOME (tyis, teis, ityvs, itevs, mark, [asm_rw], [mark])
        end
      else
        NONE
    end end

  (* check_mismatch will only succeed if there is an equation con = asm or
   * asm = con, none of which contain instantiable variables, since equations are
   * unquantified, which will only exist if there are no instantiable variables
   * in con, since the quantified variables of the lemma are renamed to not
   * overlap any variable name in the goal.
   *
   * NOTE: check_dmi does not create additional term variable instantiations.
   *)
  fun check_dmi eqs con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs =
    let val type_instantiation = find_type_instantiation ityvs tyis teis_con teis_asm con asm in
      if isSome type_instantiation then
        (* Type updates teis_con. teis_asm cannot be type instantiated. *)
        let val (ityvs, tyis, teis_con, teis_asm) = valOf type_instantiation in
        let val itevs_con = map (inst tyis) itevs_con
            val con = inst tyis con
            val asm = inst tyis asm in
        (* Equations are unquantified and quantified variables are unique. This
         * means that equations cannot be incorrectly found by accidentally
         * considering quantified variables in the assumption as unquantified
         * variables when comparing with the left and right handsides of the
         * equations.
         *)
        let val mi = check_term_mismatch eqs tyis teis_con ityvs itevs_con con asm in
          if isSome mi then
            let val (tyis, teis_con, ityvs, itevs_con, tem, asm_rws, marks) = valOf mi in
            let val con = inst tyis con
                val suc = inst tyis suc
                val asm = asm

                val itevs_lem = map (inst tyis) itevs_lem
                val itevs_con = itevs_con                 (* Type updated above and by check_term_mismatch.                  *)
                val itevs_suc = map (inst tyis) itevs_suc
                val itevs_asm = itevs_asm
    
                val teis_con = teis_con                   (* Type updated by check_term_mismatch.                            *)
                val teis_asm = teis_asm                   (* Cannot be type updated.                                         *)
                val teis_duc = map (fn {redex = f, residue = t} => {redex = inst tyis f, residue = inst tyis t}) teis_udc
    
                val tyis = tyis
                val ityvs = ityvs
                val tem = tem
                val asm_rws = asm_rws
                val marks = marks in
              SOME (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs, tem, asm_rws, marks)
            end end
          else
            NONE
        end end end
      else
        NONE
    end

  (* At least one of con and asm is a variable, but none is instantiable.
   *)
  fun find_dmi_con_asm eqs con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs =
    let val type_instantiation = find_type_instantiation ityvs tyis teis_con teis_asm con asm in
      if isSome type_instantiation then
        let val (ityvs, tyis, teis_con, teis_asm) = valOf type_instantiation in
          if same_term (inst tyis con) asm then
            let val con = inst tyis con
                val suc = inst tyis suc
                val asm = asm

                val itevs_lem = map (inst tyis) itevs_lem
                val itevs_con = map (inst tyis) itevs_con
                val itevs_suc = map (inst tyis) itevs_suc
                val itevs_asm = itevs_asm

                val teis_con = teis_con                                        (* Type updated by type_instantiate.         *)
                val teis_asm = teis_asm                                        (* Type updated by type_instantiate.         *)
                (* f does not need to be type updated as it originates from an
                 * assumption, whose type variables cannot be instantiated.
                 *)
                val teis_udc = map (fn {redex = f, residue = t} => {redex = f, residue = inst tyis t}) teis_udc

                val tyis = tyis                                                (* Extended by by type_instantiate.          *)
                val ityvs = ityvs                                              (* Extended by type_instantiate.             *)
                val template = asm                                             (* Template for rewriting assumption.        *)
                val asm_rws = []
                val marks = [] in
              SOME (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs, template, asm_rws, marks)
            end
          else (* con and asm differ. Check whether asm can be rewritten. *)
            check_dmi eqs con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs
        end
      else
        NONE
    end

  (* At least one of con and asm is a variable, none of which is bounded. *)
  fun find_dmi_fvs find_dmi_rec eqs con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs bvars =
      let val iasm = List.find (fn {redex = f, residue = t} => same_term asm f) teis_asm in
        if isSome iasm then (* asm has been instantiated, traverse that subtree instead, in order to keep the template preserved. *)
          let val template = asm in
          let val asm = (#residue o valOf) iasm in
          let val dmi = find_dmi_rec eqs con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs bvars in
            if isSome dmi then
              let val (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs, false_template, asm_rws, marks) = valOf dmi in
                SOME (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs, template, asm_rws, marks)
              end
            else
              NONE
          end end end
        else if is_in itevs_con con andalso is_in itevs_asm asm then (* Both con and asm are instantiable variables. *)
          if in_suc itevs_suc con then   (* Variable in suc. *)
            find_dmi_both_itev_suc con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs
          else                           (* Variable not in suc. *)
            find_dmi_both_itev_not_suc con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs
        else if is_in itevs_con con then (* Only con is an instantiable variable, with asm being an arbitrary term. *)
          find_dmi_con con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs
        else if is_in itevs_asm asm then (* Only asm is an instantiable variable, with con being an arbitrary term. *)
          find_dmi_asm con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs
        else (* None of con and asm is an instantiable variable, both of which are arbitrary terms. Must denote the same object *)
          find_dmi_con_asm eqs con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs
      end

  (* Both con and asm are bounded variables, occurring at matching positions. *)
  fun find_dmi_bvs con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs =
    let val type_instantiation = find_type_instantiation ityvs tyis teis_con teis_asm con asm in
      if isSome type_instantiation then
        let val (ityvs, tyis, teis_con, teis_asm) = valOf type_instantiation in
        let val con = inst tyis con
            val suc = inst tyis suc
            val asm = asm

            val itevs_lem = map (inst tyis) itevs_lem
            val itevs_con = map (inst tyis) itevs_con
            val itevs_suc = map (inst tyis) itevs_suc
            val itevs_asm = itevs_asm

            val teis_con = teis_con
            val teis_asm = teis_asm
            val teis_udc = map (fn {redex = f, residue = t} => {redex = inst tyis f, residue = inst tyis t}) teis_udc

            val tyis = tyis
            val ityvs = ityvs
            val template = asm
            val asm_rws = []
            val marks = [] in
              SOME (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs, template, asm_rws, marks)
        end end
      else
        NONE
    end

  (* At least one of con and asm is a variable. *)
  fun find_dmi_var find_dmi_rec eqs con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis teis_asm teis_udc tyis ityvs bvars =
    case bvar_match con asm bvars of
      FAIL => NONE
    | MATCH =>
      find_dmi_bvs con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis teis_asm teis_udc tyis ityvs
    | FREE =>
      find_dmi_fvs find_dmi_rec eqs con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis teis_asm teis_udc tyis ityvs bvars

  fun find_dmi_const eqs con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs =
    if is_const con andalso is_const asm then
      if same_term con asm then
        SOME (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs, asm, [], [])
      else
        let val type_instantiation = find_type_instantiation ityvs tyis teis_con teis_asm con asm in
          if isSome type_instantiation then
            let val (ityvs, tyis, teis_con, teis_asm) = valOf type_instantiation in
              if same_term (inst tyis con) asm then
                let val con = inst tyis con
                    val suc = inst tyis suc
                    val asm = asm
                    val itevs_lem = map (inst tyis) itevs_lem
                    val itevs_con = map (inst tyis) itevs_con
                    val itevs_suc = map (inst tyis) itevs_suc
                    val itevs_asm = itevs_asm
                    val teis_con = teis_con
                    val teis_asm = teis_asm
                    val teis_udc = map (fn {redex = f, residue = t} => {redex = inst tyis f, residue = inst tyis t}) teis_udc
                    val tyis = tyis
                    val ityvs = ityvs
                    val template = asm
                    val asm_rws = []
                    val marks = [] in
                  SOME (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs, template, asm_rws, marks)
                end
              else (* Same types but different constants: Check for rewrites. *)
                check_dmi eqs con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs
            end
          else
            NONE (* Cannot be made to have the same type. Can thus not become identical. *)
        end
    else
      check_dmi eqs con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs

  fun find_dmi_app find_dmi_rec eqs con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs bvars =
    if is_comb con andalso is_comb asm then
      let val (con_fun, con_arg) = dest_comb con
          val (asm_fun, asm_arg) = dest_comb asm in
      let val mi_arg = find_dmi_rec eqs con_arg suc asm_arg itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs bvars in
        if isSome mi_arg then

          let val (con_arg, suc, asm_arg, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs, tem_arg, arg_asm_rws, arg_marks) = valOf mi_arg in
          let val con_fun = subst (teis_con @ teis_asm @ teis_udc) (inst tyis con_fun)
           (* val asm_fun = subst (teis_con @ teis_asm @ teis_udc) asm_fun *) (* Removed to preserve assumption rewrite template. *)
              val bvars = map (fn (bv_con, bv_asm) => (inst tyis bv_con, bv_asm)) bvars in
          let val mi_fun = find_dmi_rec eqs con_fun suc asm_fun itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs bvars in
            if isSome mi_fun then
              let val (con_fun, suc, asm_fun, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs, tem_fun, fun_asm_rws, fun_marks) = valOf mi_fun in
              let val con = mk_comb (con_fun, con_arg)
                  val asm = mk_comb (asm_fun, asm_arg)
                  val tem = mk_comb (tem_fun, tem_arg)
                  val asm_rws = fun_asm_rws @ arg_asm_rws
                  val marks = fun_marks @ arg_marks in
                SOME (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs, tem, asm_rws, marks) 
              end end
            else
              check_dmi eqs con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs
          end end end
        else
              check_dmi eqs con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs
      end end
    else
              check_dmi eqs con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs

(*
val bvars = [] : (Term.term * Term.term) list
val con = con_arg
val asm = asm_arg

val con = con_fun
val asm = asm_fun
*)

  fun find_dmi_abs find_dmi_rec eqs con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs bvars =
    if is_abs con andalso is_abs asm then
      let val (bv_con, con) = dest_abs con
          val (bv_asm, asm) = dest_abs asm in
      let val bvars = (bv_con, bv_asm)::bvars in
      let val mi = find_dmi_rec eqs con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs bvars in
        if isSome mi then
          let val (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs, tem, asm_rws, marks) = valOf mi in
          let val con = mk_abs (inst tyis bv_con, con)
              val asm = mk_abs (bv_asm, asm)
              val tem = mk_abs (bv_asm, tem) in
            SOME (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs, tem, asm_rws, marks)
          end end
        else
          check_dmi eqs con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs
      end end end
    else
      check_dmi eqs con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs
(*
val con = con_fun
val asm = asm_fun
*)
  fun find_dmi_rec              eqs con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs bvars =
    if is_var con orelse is_var asm then
      find_dmi_var find_dmi_rec eqs con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs bvars
    else if is_const con orelse is_const asm then
      find_dmi_const            eqs con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs
    else if is_comb con orelse is_comb asm then
      find_dmi_app find_dmi_rec eqs con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs bvars
    else
      find_dmi_abs find_dmi_rec eqs con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs bvars

  fun find_dmi eqs con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs =
    let val bvars = [] : (Term.term * Term.term) list in
      find_dmi_rec eqs con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs bvars
    end
(*
val teis_con = teis
*)
  fun is_double_meet eqs con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis_con tyis ityvs =
            (* Variables in the conjuncts that are instantiable by originating
             * from some other quantified assumption.
             *
             * NOTE: Does not need to be type updated as the instantiable
             * variables originate from an assumption, whose type variables are
             * not instantiable.
             *)
    let val itevs_oth = filter (fn fv => not (is_in itevs_lem fv) andalso is_in itevs_con fv) (free_vars con)
        val teis_asm = []
        val teis_udc = [] in
    let val is_dmi = find_dmi eqs con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs in
      if isSome is_dmi then
        let val (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs, tem, asm_rws, marks) = valOf is_dmi in
           SOME (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs, tem, asm_rws, marks, false)
        end
      else if is_eq con andalso is_eq asm then
        let val asm = mk_eq (rhs asm, lhs asm) in (* Reflect the equation asm check whether that works. *)
        let val is_dmi = find_dmi eqs con suc asm itevs_lem itevs_oth itevs_con itevs_suc itevs_asm teis_con teis_asm teis_udc tyis ityvs in
          if isSome is_dmi then
            let val (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs, tem, asm_rws, marks) = valOf is_dmi in
            let val tem = mk_eq (rhs tem, lhs tem) in
              SOME (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, teis_asm, teis_udc, tyis, ityvs, tem, asm_rws, marks, true)
            end end
          else
            NONE
        end end
      else
        NONE
    end end
(*
given: is_double_meet eqs suc suc gol itevs_suc itevs_suc itevs_suc itevs_gol teis     tyis ityvs
takes: is_double_meet eqs con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis_con tyis ityvs
val (eqs, con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis_con, tyis, ityvs) =
    (eqs, suc, suc, gol, itevs_suc, itevs_suc, itevs_suc, itevs_gol, teis    , tyis, ityvs)
*)
  fun is_double_meet_q_rec eqs con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis tyis ityvs nqvs =
    let val dm = is_double_meet eqs con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis tyis ityvs in
      if isSome dm then
        let val (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis, teis_asm, teis_udc, tyis, ityvs, tem, asm_rws, marks, r) = valOf dm in
          SOME (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis, teis_asm, teis_udc, tyis, ityvs, tem, asm_rws, marks, r, nqvs)
        end
      else if is_forall asm then
        let val (itev, asm) = dest_forall asm in
        let val itevs_asm = itevs_asm @ [itev]
            val nqvs = nqvs + 1 in
        let val dm = is_double_meet_q_rec eqs con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis tyis ityvs nqvs in
          if isSome dm then
            let val (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis, teis_asm, teis_udc, tyis, ityvs, tem, asm_rws, marks, r, nqvs) = valOf dm in
            let val tem = mk_forall (itev, tem) in
              SOME (con, suc, asm, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis, teis_asm, teis_udc, tyis, ityvs, tem, asm_rws, marks, r, nqvs)
            end end
          else
            NONE
        end end end
      else
        NONE
    end

  (* Extends an instantiation teis by comparing a conjunct @con with an
   * assumption @asm, by potentially stripping and instantiating quantifiers, if
   * any, of @asm.
   *)
  fun is_double_meet_q eqs con suc asm itevs_lem itevs_con itevs_suc teis tyis ityvs =
    let val itevs_asm = []
        val nqvs = 0 in
    let val dm = is_double_meet_q_rec eqs con suc asm itevs_lem itevs_con itevs_suc itevs_asm teis tyis ityvs nqvs in
      if isSome dm then
        let val (con, suc, _, itevs_lem, itevs_con, itevs_suc, itevs_asm, teis, teis_asm, teis_udc, tyis, ityvs, tem, asm_rws, marks, r, nqvs) = valOf dm in
        let val asm_rw_is = (asm, tem, asm_rws, r, teis_asm, itevs_asm, nqvs) in
          SOME (con, suc, itevs_lem, itevs_con, itevs_suc, teis, tyis, ityvs, marks, asm_rw_is, teis_udc)
        end end
      else
        NONE
    end end


(*
val (eqs0, con0, suc0, asm0, itevs_lem0, itevs_con0, itevs_suc0, teis0, tyis0, ityvs) =
   (eqs, con, suc, asm, itevs_lem, itevs_con, itevs_suc, teis, tyis, ityvs)
val (eqs, con, suc, asm, itevs_lem, itevs_con, itevs_suc, teis, tyis, ityvs) =
    (eqs0, con0, suc0, asm0, itevs_lem0, itevs_con0, itevs_suc0, teis0, tyis0, ityvs)
*)
   

  (* Attempts to find instantiations by comparing the succedent of the lemma
   * with subterms of the conclusion of the goal, and perform additional
   * instantiations on quantified conjuncts.
   *)
  fun is_meet_subgol_suc_rec suc gol itevs_lem itevs_suc teis tyis ityvs bvars =
    let val no_bvars = not (exists (fn v => exists (same_term v) bvars) (free_vars gol)) in
    let val eqs = [] in
    let val is_dm = if no_bvars then is_double_meet_q eqs suc suc gol itevs_lem itevs_suc itevs_suc teis tyis ityvs else NONE in
      if isSome is_dm then
        let val (_, suc, itevs_lem, _, itevs_suc, teis, tyis, ityvs, _, _, teis_udc) = valOf is_dm in
          SOME (tyis, teis, ityvs, itevs_lem, itevs_suc, suc, teis_udc)
        end
      else if is_var gol orelse is_const gol then (* No subterms of the conclusion can be used to instantiate the lemma. *)
        NONE
      else if is_comb gol then
        let val (fun_gol, arg_gol) = dest_comb gol in
        let val instantiation_by_conclusion_arg = is_meet_subgol_suc_rec suc arg_gol itevs_lem itevs_suc teis tyis ityvs bvars in
          if isSome instantiation_by_conclusion_arg then (* Argument worked: Return that value. *)
            instantiation_by_conclusion_arg
          else                                           (* Argument did not work: Try the function. *)
            is_meet_subgol_suc_rec suc fun_gol itevs_lem itevs_suc teis tyis ityvs bvars
        end end
      else (* is_abs conclusion *)
        let val (bvar, body) = dest_abs gol in
        let val bvars = bvar::bvars in
          is_meet_subgol_suc_rec suc body itevs_lem itevs_suc teis tyis ityvs bvars
        end end
    end end end

  fun is_meet_subgol_suc qcons itevs_con suc gol itevs_lem itevs_suc teis tyis ityvs bvars =
    let val is = is_meet_subgol_suc_rec suc gol itevs_lem itevs_suc teis tyis ityvs bvars in
     if isSome is then
       let val (tyis, teis, ityvs, itevs_lem, itevs_suc, suc, teis_udc) = valOf is in
       let val itevs_con = filter (fn v => all (fn {redex = f, residue = _} => not_same_term v f) teis) (map (inst tyis) itevs_con)
           val qcons = map (subst teis) (map (inst tyis) qcons) in
         SOME (tyis, teis, ityvs, itevs_lem, itevs_con, itevs_suc, suc, qcons)
       end end
     else
       NONE
    end




  (* Attempts to find instantiations by comparing the succedent of the lemma
   * with subterms of the conclusion of the goal.
   *)
  fun is_meet_subcon_suc_qcons qconjuncts tyis teis ityvs itevs c succedent bvars_c =
    let val no_bounded_variables = not (exists (fn v => exists (same_term v) bvars_c) (free_vars c)) in
    let val eqs = []
        val is_asm_rws = if no_bounded_variables then is_meet tyis teis ityvs itevs eqs succedent c else NONE in
      if isSome is_asm_rws then
        let val (tyis, teis, ityvs, itevs, _, _, _, _) = valOf is_asm_rws in (* Last 4 components ignored due to no assumption being rewritten. *)
        let val qconjuncts = map (subst teis) (map (inst tyis) qconjuncts) in
          SOME (tyis, teis, ityvs, itevs, qconjuncts)
        end end
      else if is_var c orelse is_const c then (* No subterms of the conclusion can be used to instantiate the lemma. *)
        NONE
      else if is_comb c then
        let val (fun_c, arg_c) = dest_comb c in                          
        let val instantiation_by_conclusion_arg = is_meet_subcon_suc_qcons qconjuncts tyis teis ityvs itevs arg_c succedent bvars_c in
          if isSome instantiation_by_conclusion_arg then (* Argument did not work... *)
            instantiation_by_conclusion_arg
          else                                           (* ... try the function. *)
            is_meet_subcon_suc_qcons qconjuncts tyis teis ityvs itevs fun_c succedent bvars_c
        end end
      else (* is_abs conclusion *)
        let val (bvar_c, body_c) = dest_abs c in
        let val bvars_c = bvar_c::bvars_c in
          is_meet_subcon_suc_qcons qconjuncts tyis teis ityvs itevs body_c succedent bvars_c
        end end
    end end

  (* Tries to instantiate type and term variables by comparing the succedent of
   * the lemma with subterms of the conclusion of the goal. If not valid
   * instantiation is found, then NONE is returned, otherwise the complete
   * instantiations are returned.
   *)
  fun has_meet_subcon_suc tyis teis ityvs itevs succedent conclusion_subterm =
    let val (tem, tym) = match_term succedent conclusion_subterm in
    let val additional_tyis = filter (fn {redex = from, residue = to} => exists (same_type from) ityvs) tym in (* Only instantiable type variables kept of matched instantiations. *)
    let val itevs = map (inst additional_tyis) itevs in
    let val additional_teis = filter (fn {redex = from, residue = to} => exists (same_term from) itevs) tem in (* Only instantiable term variables kept of matched instantiations. *)
    let val tyis = tyis @ additional_tyis
        (* Update types and terms of existing instantiations that come from uninstantiated equality conjuncts. *)
        val teis = (map (fn {redex = f, residue = t} => {redex = inst additional_tyis f, residue = inst additional_tyis t}) teis) in
    let val teis = map (fn {redex = f, residue = t} => {redex = subst additional_teis f, residue = subst additional_teis t}) teis in
    let val teis = teis @ additional_teis in
    let val ityvs = filter (fn ityv => all (fn {redex = f, residue = t} => not_same_type ityv f) tyis) ityvs
        val itevs = filter (fn itev => all (fn {redex = f, residue = t} => not_same_term itev f) teis) itevs in
      SOME (tyis, teis, ityvs, itevs)
    end end end end end end end end
    handle _ => NONE

  (* Same as is_meet_subcon_suc_qcons except that no qconjuncts are used.
   *)
  fun find_meet_subcon_suc tyis teis ityvs itevs succedent conclusion_subterm bvars_conclusion =
    let val no_bounded_variables = not (exists (fn v => exists (same_term v) bvars_conclusion) (free_vars conclusion_subterm)) in
    let val meet_subcon_suc = if no_bounded_variables then has_meet_subcon_suc tyis teis ityvs itevs succedent conclusion_subterm else NONE in
      if isSome meet_subcon_suc then
        meet_subcon_suc
      else if is_var conclusion_subterm orelse is_const conclusion_subterm then
        NONE
      else if is_comb conclusion_subterm then
        let val (conclusion_fun, conclusion_arg) = dest_comb conclusion_subterm in
        let val meet_subcon_suc = find_meet_subcon_suc tyis teis ityvs itevs succedent conclusion_arg bvars_conclusion in
          if isSome meet_subcon_suc then
            meet_subcon_suc
          else
            find_meet_subcon_suc tyis teis ityvs itevs succedent conclusion_fun bvars_conclusion
        end end
      else (* is_abs conclusion_subterm *)
        let val (bvar, body) = dest_abs conclusion_subterm in
        let val bvars_conclusion = bvar:: bvars_conclusion in
          find_meet_subcon_suc tyis teis ityvs itevs succedent body bvars_conclusion
        end end
    end end

(*
val bvars = [] : (term * term) list
val conj = conjunct_r
val asm = asm_r
val conj = conj_f
val asm = asm_f
val conj = conj_a
val asm = asm_a
*)
  (* Traverse conj and asm in parallel until asm is a variable and conj is a
   * pattern.
   *)
  fun find_equality_subterms_expansion tyis teis ityvs itevs bvars conj asm =
    (* Bounded variables are not considered for expansion. *)
    if exists (fn (cbv, abv) => same_term conj cbv orelse same_term asm abv) bvars then
      NONE
    else if is_var asm then
      (* Assumption contains variable where conjunct contains
       * pattern/constructor. It is required that the type does not have
       * multiple patterns, which is checked by the second conjunct.
       *)
      let val is_unique_pattern = (not o is_disj o concl o SPEC_ALL o TypeBase.nchotomy_of o type_of) conj in
        if (TypeBase.is_constructor o #1 o strip_comb) conj andalso is_unique_pattern then
          let val is = type_instantiate tyis teis ityvs itevs conj asm in
            if isSome is then
              let val (tyis, teis, ityvs, itevs) = valOf is in
                SOME (tyis, teis, ityvs, itevs, asm, inst tyis conj)
              end
            else
              NONE
          end
        else
          NONE
      end
      handle _ => NONE (* Handles exception raised by TypeBase.nchotomy_of *)
    else if is_comb conj andalso is_comb asm then
      let val (conj_f, conj_a) = dest_comb conj
          val (asm_f, asm_a) = dest_comb asm in
        case find_equality_subterms_expansion tyis teis ityvs itevs bvars conj_a asm_a of
          NONE => find_equality_subterms_expansion tyis teis ityvs itevs bvars conj_f asm_f
        | SOME asm_conj => SOME asm_conj
      end
    else if is_abs conj andalso is_abs asm then
      let val (cbv, conj_body) = dest_abs conj
          val (abv, asm_body) = dest_abs asm in
        find_equality_subterms_expansion tyis teis ityvs itevs ((cbv, abv)::bvars) conj_body asm_body
      end
    else
      NONE

  fun expandable_conjunct tyis teis ityvs itevs conjunct asm =
      if is_eq conjunct andalso is_eq asm then
        let val (conjunct_l, conjunct_r) = dest_eq conjunct in
        let val (asm_l, asm_r) = dest_eq asm in
        let val expansion = find_equality_subterms_expansion tyis teis ityvs itevs [] conjunct_l asm_l in
        if isSome expansion then
          expansion
        else
        let val expansion = find_equality_subterms_expansion tyis teis ityvs itevs [] conjunct_l asm_r in
        if isSome expansion then
          expansion
        else
        let val expansion = find_equality_subterms_expansion tyis teis ityvs itevs [] conjunct_r asm_l in
        if isSome expansion then
          expansion
        else
        let val expansion = find_equality_subterms_expansion tyis teis ityvs itevs [] conjunct_r asm_r in
          expansion
        end end end end end end
      else
        find_equality_subterms_expansion tyis teis ityvs itevs [] conjunct asm
(*
val conjunct = con
val assumption = asm
*)
  fun find_expansion_conjunct_assumption tyis teis ityvs itevs_con conjunct assumption =
    let val expansion = expandable_conjunct tyis teis ityvs itevs_con conjunct assumption in
      if isSome expansion then
        let val (tyis, teis, ityvs, itevs, variable, pattern) = valOf expansion in
        let val eq = mk_eq (variable, pattern) in
        let val base_xthm = foldl (fn (xv, xthm) => EXISTS (mk_exists (xv, concl xthm), xv) xthm) (ASSUME eq) (free_vars pattern) in
        let val xthm = expand_xthm base_xthm {redex = variable, residue = pattern} in
        let val expansion_thm = REWRITE_RULE [] (DISCH ((hd o hyp) xthm) xthm) in
          SOME (tyis, teis, ityvs, itevs, expansion_thm)
        end end end end end
      else
        NONE
    end




  fun exists_substitution invalid_names xbody =
    let fun exists_substitution_rec invalid_names xbody substitution =
      case instantiate_exist xbody invalid_names of
        NONE => (xbody, substitution, invalid_names)
      | SOME (vi, xi, ibody) => exists_substitution_rec (vi::invalid_names) ibody ({redex = xi, residue = vi}::substitution)
    in
      exists_substitution_rec invalid_names xbody []
    end

  fun instantiate_expansion invalid_names xbody =
    let val (ibody, xis, invalid_names) = exists_substitution invalid_names xbody in
      (ibody, xis, invalid_names)
    end

  (* e is an assumption that is an equation, potentially universally quantified. *)
  fun instantiate_mark_asm_rws substitution mark_asm_rws =
    let fun substitute_tos teis = map (fn {redex = f, residue = t} => {redex = f, residue = substitution t}) teis in
      map (fn (m, {redex = f, residue = t}, e, eq_is, r) => (m, substitution f |-> substitution t, substitution e, substitute_tos eq_is, r)) mark_asm_rws
    end

  fun variable_to_pattern A eqs used_asms d_cons ud_cons inv_names gol suc itevs_lcs teis exps asm_rw_is asms cons ethm tyis itevs_con =
    let val (itevs_lem, _, itevs_suc) = itevs_lcs (* Use the argument itevs_con which has already been type updated. *)
        val xterm = concl ethm in
    let val (expanded_asm, xis, inv_names) = instantiate_expansion inv_names xterm
        val (xvars, xbody) = strip_exists xterm in
    let fun substitution_ty term = inst tyis term
        fun substitution_te term = ((subst xis) o (subst [lhs expanded_asm |-> rhs expanded_asm])) term in
    let val A = map substitution_te A
        val eqs = map substitution_te eqs
        val used_asms = map substitution_te used_asms
        val d_cons = map substitution_te (map substitution_ty d_cons)
        val ud_cons = map substitution_te (map substitution_ty ud_cons)
        val gol = substitution_te gol
        val suc = substitution_te (substitution_ty suc)
        val teis = substitute_teis_to (lhs expanded_asm |-> rhs expanded_asm) teis
        val exps = exps @ [(ethm, expanded_asm, xis)]
        val asm_rw_is = map (fn (asm, tem, mark_asm_rws, r, teis_asm, itevs_asm, nqvs) =>
                              (substitution_te asm,
                               substitution_te tem,
                               instantiate_mark_asm_rws substitution_te mark_asm_rws,
                               r,
                               substitute_teis_to (lhs expanded_asm |-> rhs expanded_asm) teis_asm,
                               itevs_asm,
                               nqvs
                              )) asm_rw_is
        val asms = map substitution_te asms
        val cons = map substitution_te (map substitution_ty cons) in
    (* itevs_con already type instantiated. *)
    let val itevs_lcs = (map substitution_ty itevs_lem, itevs_con, map substitution_ty itevs_suc) in
      (A, eqs, used_asms, d_cons, ud_cons, inv_names, gol, suc, itevs_lcs, teis, exps, asm_rw_is, asms, cons)
    end end end end end
(*
val bvars = [] : Term.term list
val gol = gol_fun
val gol = gol_arg
*)

  fun is_double_submeet_gol eqs suc gol itevs_suc teis tyis ityvs bvars =
    let val fvs = free_vars gol in
      if all (fn fv => not (is_in bvars fv)) fvs then
        let val itevs_gol = [] in
        let val meet = is_double_meet eqs suc suc gol itevs_suc itevs_suc itevs_suc itevs_gol teis tyis ityvs in
          if isSome meet then
            let val (_, _, _, _, itevs_suc, _, _, teis, _, teis_udc, tyis, ityvs, _, _, _, _) = valOf meet in
              SOME (tyis, teis, ityvs, itevs_suc, teis_udc)
            end
          else if is_var gol orelse is_const gol then
            NONE
          else if is_comb gol then
            let val (gol_fun, gol_arg) = dest_comb gol in
            let val meet = is_double_submeet_gol eqs suc gol_fun itevs_suc teis tyis ityvs bvars in
              if isSome meet then 
                meet
              else
                           is_double_submeet_gol eqs suc gol_arg itevs_suc teis tyis ityvs bvars
            end end
          else
            let val (bvar, gol) = dest_abs gol in
            let val bvars = bvar::bvars in
              is_double_submeet_gol eqs suc gol itevs_suc teis tyis ityvs bvars
            end end
        end end
      else if is_var gol orelse is_const gol then
        NONE
      else if is_comb gol then
        let val (gol_fun, gol_arg) = dest_comb gol in
        let val meet = is_double_submeet_gol eqs suc gol_fun itevs_suc teis tyis ityvs bvars in
          if isSome meet then 
            meet
          else
                       is_double_submeet_gol eqs suc gol_arg itevs_suc teis tyis ityvs bvars
        end end
      else
        let val (bvar, gol) = dest_abs gol in
        let val bvars = bvar::bvars in
          is_double_submeet_gol eqs suc gol itevs_suc teis tyis ityvs bvars
        end end
    end

(* CODE FOR MERGING POTENTIALLY INCONCISTENT TYPE AND TERM VARIABLE INSTANTIATIONS!

  (* Adds a type instantiation resulting by comparing the argument to the goal to
   * a type instantiation resulting by comparing the function to the goal, where
   * only unmapped types are added.
   *)
  fun extend_tyis tyis1 [] = tyis1
    | extend_tyis tyis1 ({redex = from, residue = to}::tyis2) =
      let val extended_tyis = extend_tyis tyis1 tyis2 in
      let val existing_tyi = List.find (fn {redex = f, residue = t} => same_type from f) extended_tyis in
      (* Two subterms instantiating both types: Take the first instantiation,
       * which comes from the function, and which is therefore normally larger,
       * in contrast to the instantiation from argument. This occurs
       * irrespectively of whether the instantiations are consistent or not.
       *)
        if isSome existing_tyi then
          extended_tyis
        else
          {redex = to, residue = from}::extended_tyis
      end end

val itevs_ty_fun = map (fn {redex = fr, residue = t} => {redex = inst tyis_fun f, residue = inst tyis_fun t}) itevs_fun
val itevs_ty_arg = map (fn {redex = fr, residue = t} => {redex = inst tyis_arg f, residue = inst tyis_arg t}) itevs_arg

  fun get_index_rec from n [] = raise (mk_HOL_ERR "helper_tactics" "get_index" "Instantiated variable is not instantiable.")
    | get_index_rec from n (itev_ty_arg::itevs_ty_arg) =
      if same_term from itev_ty_arg then
        n
      else
        get_index_rec from (n + 1) itevs_ty_arg

  fun get_index itevs_ty_arg from = get_index_rec from 0 itevs_ty_arg

  fun get_iv itevs_ty_fun index_arg = List.nth (itevs_ty_fun, index_arg)

  fun get_instantiation iv_ty_fun [] = raise (mk_HOL_ERR "helper_tactics" "get_instantiation" "Variable not in instantiation.")
    | get_instantiation iv_ty_fun ({redex = f,residue = t}::extended_teis) =
      if same_term iv_ty_fun f then
        t
      else
        get_instantiation iv_ty_fun extended_teis

  fun extend_teis itevs_arg teis_fun [] = teis_fun
    | extend_teis itevs_arg teis_fun ({redex = f_arg, residue = t_arg}::teis_arg) =
      let val extended_teis = extend_teis teis_fun teis_arg in
      let val index_arg = get_index itevs_arg in
      let val t_
        
      end
*)

(*
val suc = suc_arg
val suc = suc_fun
*)

  (* Given one instantiation from comparing the function of the succedent with
   * the goal, and one instantiation from comparing the argument of the succedent
   * with the goal, the two instantiations are merged if consistent, and
   * otherwise returns the largest instantiation.
   *)
  fun largest_instantiation NONE NONE = NONE
    | largest_instantiation NONE meet_arg = meet_arg
    | largest_instantiation meet_fun NONE = meet_fun
    | largest_instantiation (SOME (tyis_fun, teis_fun, ityvs_fun, itevs_fun, teis_udc_fun))
                            (SOME (tyis_arg, teis_arg, ityvs_arg, itevs_arg, teis_udc_arg)) =
      let val tyis = merge_type_matchings tyis_fun tyis_arg in
        if isSome tyis then
          let val tyis = valOf tyis in
          let val teis_fun = map (fn {redex = f, residue = t} => {redex = inst tyis f, residue = inst tyis t}) teis_fun
              val teis_arg = map (fn {redex = f, residue = t} => {redex = inst tyis f, residue = inst tyis t}) teis_arg
              val teis_udc_fun = map (fn {redex = f, residue = t} => {redex = inst tyis f, residue = inst tyis t}) teis_udc_fun
              val teis_udc_arg = map (fn {redex = f, residue = t} => {redex = inst tyis f, residue = inst tyis t}) teis_udc_arg in
          let val teis_fun = map (fn {redex = f, residue = t} => {redex = f, residue = subst (teis_arg @ teis_udc_arg) t}) teis_fun
              val teis_arg = map (fn {redex = f, residue = t} => {redex = f, residue = subst (teis_fun @ teis_udc_fun) t}) teis_arg in
          let val teis     = merge_term_matchings teis_fun teis_arg
              val teis_udc = merge_term_matchings teis_udc_fun teis_udc_arg in
            if isSome teis andalso isSome teis_udc then     (* Instantiations consistent.       *)
              let val teis = valOf teis
                  val teis_udc = valOf teis_udc
                  val itevs_arg_ty = map (inst tyis_fun) itevs_arg
                  val itevs_fun_ty = map (inst tyis_arg) itevs_fun in
              let val ityvs = filter (fn ityv => exists (same_type ityv) ityvs_arg) ityvs_fun
                  val itevs = filter (fn itev => exists (same_term itev) itevs_arg_ty) itevs_fun_ty in
                SOME (tyis, teis, ityvs, itevs, teis_udc)
              end end
            else if length tyis_fun >= length tyis_arg then (* Largest type instantiation wins. *)
              SOME (tyis_fun, teis_fun, ityvs_fun, itevs_fun, teis_udc_fun)
            else
              SOME (tyis_arg, teis_arg, ityvs_arg, itevs_arg, teis_udc_arg)
          end end end end
        else if length tyis_fun >= length tyis_arg then     (* Largest type instantiation wins. *)
          SOME (tyis_fun, teis_fun, ityvs_fun, itevs_fun, teis_udc_fun)
        else
          SOME (tyis_arg, teis_arg, ityvs_arg, itevs_arg, teis_udc_arg)
      end
(*
val suc = suc_arg
val suc = suc_fun
*)
  fun is_double_submeet_suc eqs suc gol itevs_suc teis tyis ityvs bvars =
    if all (fn fv => not (is_in bvars fv)) (free_vars suc) then
      let val meet = is_double_submeet_gol eqs suc gol itevs_suc teis tyis ityvs [] in
        if isSome meet then
          meet
        else if is_var suc orelse is_const suc then
          NONE
        else if is_comb suc then
          let val (suc_fun, suc_arg) = dest_comb suc in
          let val meet_fun = is_double_submeet_suc eqs suc_fun gol itevs_suc teis tyis ityvs bvars
              val meet_arg = is_double_submeet_suc eqs suc_arg gol itevs_suc teis tyis ityvs bvars in
            largest_instantiation meet_fun meet_arg
          end end
        else
          let val (bvar, suc) = dest_abs suc in
          let val bvars = (*bvar::*)bvars in
            is_double_submeet_suc eqs suc gol itevs_suc teis tyis ityvs bvars
          end end
      end
    else if is_var suc orelse is_const suc then
      NONE
    else if is_comb suc then
      let val (suc_fun, suc_arg) = dest_comb suc in
      let val meet_fun = is_double_submeet_suc eqs suc_fun gol itevs_suc teis tyis ityvs bvars
          val meet_arg = is_double_submeet_suc eqs suc_arg gol itevs_suc teis tyis ityvs bvars in
        largest_instantiation meet_fun meet_arg
      end end
    else
      let val (bvar, suc) = dest_abs suc in
      let val bvars = (*bvar::*)bvars in
        is_double_submeet_suc eqs suc gol itevs_suc teis tyis ityvs bvars
      end end

  (*
   * 1. An instantiation of an instantiable variable in itevs_con that is not in
   *    itevs_lem has propagated from an assumption.
   * 2. Such an instantiation is only used to update the other instantiations,
   *    conjuncts and the succedent, including undischarged conjuncts, and is not
   *    added to the lemma instantiations.
   * 3. If a conjuncts contains free variables that are instantiable, then the
   *    conjunct cannot be discharged, and is added to the list of undischarged
   *    conjuncts.
   *)
  fun add_undischarged_conjunct asm u_itevs_con u_con asm_rw_i =
      if exists (is_in u_itevs_con) (free_vars u_con) then
        (* Conjunct not discharged: Do not add assumption rewrites (the
         * assumption was used only to find instantiations), but add the conjunct
         * to undischarged conjuncts.
         *)
        ([], [], [u_con], [])
      else
        (* Conjunct discharged: Assumption used with rewrites and do not add it
         * to ud_cons.
         *)
        ([asm], [u_con], [], [asm_rw_i])

  fun find_tyis_asms_con eqs tyis teis ityvs itevs exps asm_rw_is used_asms ud_cons d_con [] =
      if null ityvs then
        SOME (tyis, teis, ityvs, itevs, exps, asm_rw_is, used_asms, ud_cons)
      else
        NONE
    | find_tyis_asms_con eqs tyis teis ityvs itevs exps asm_rw_is used_asms ud_cons d_con (asm::asms) =
      let val bvars = [] in
      let val meet = is_double_submeet_suc eqs d_con asm itevs teis tyis ityvs bvars in
        if isSome meet then
          let val (tyis, teis, ityvs, itevs, teis_udc) = valOf meet in
          let val ud_cons = map (fn ud_con => subst (teis @ teis_udc) (inst tyis ud_con)) ud_cons in
            if null ityvs then
              SOME (tyis, teis, ityvs, itevs, exps, asm_rw_is, used_asms, ud_cons)
            else
              find_tyis_asms_con eqs tyis teis ityvs itevs exps asm_rw_is used_asms ud_cons d_con asms
          end end
        else
          find_tyis_asms_con eqs tyis teis ityvs itevs exps asm_rw_is used_asms ud_cons d_con asms
      end end

  fun find_tyis_asms_cons eqs tyis teis ityvs itevs exps asm_rw_is used_asms ud_cons asms [] =
      if null ityvs then
        SOME (tyis, teis, ityvs, itevs, exps, asm_rw_is, used_asms, ud_cons)
      else
        NONE
    | find_tyis_asms_cons eqs tyis teis ityvs itevs exps asm_rw_is used_asms ud_cons A (d_con::d_cons) =
      let val is = find_tyis_asms_con eqs tyis teis ityvs itevs exps asm_rw_is used_asms ud_cons d_con A in
        if isSome is then
          let val (tyis, teis, ityvs, itevs, exps, asm_rw_is, used_asms, ud_cons) = valOf is in
            if null ityvs then
              SOME (tyis, teis, ityvs, itevs, exps, asm_rw_is, used_asms, ud_cons)
            else
              find_tyis_asms_cons eqs tyis teis ityvs itevs exps asm_rw_is used_asms ud_cons A d_cons
          end
        else
          find_tyis_asms_cons eqs tyis teis ityvs itevs exps asm_rw_is used_asms ud_cons A d_cons
      end

  (* Algorithm:
   * 1. An instantiation of an instantiable variable in itevs_con that is not in
   *    itevs_lem has propagated from an assumption.
   * 2. Such an instantiation is only used to update the other instantiations and
   *    conjuncts, including undischarged conjuncts, and is not added to the
   *    lemma instantiations.
   * 3. If a conjuncts contains free variables that are instantiable, then the
   *    conjunct cannot be discharged, and is added to the list of undischarged
   *    conjuncts.
   * 4. When all conjuncts have been processed, the succedent of the lemma is
   *    compared to the conclusion of the goal in an attempt to find addtional
   *    instantiations.
   * 5. Finally, all undischarged conjuncts are processed again in an attempt to
   *    instantiate all their variables.
   * 6. Stop when all conjuncts have been processed but the instantiations did
   *    not change (the numbers of instantiations are unchanged).
   *)
  fun find_lemma_is disch_all pis A0 eqs used_asms d_cons ud_cons inv_names gol suc itevs_lcs teis tyis ityvs exps asm_rw_is asms [] =
      let val (itevs_lem, itevs_con, itevs_suc) = itevs_lcs
          val (ptyis_length, pteis_length) = pis in
        if null ityvs andalso (*null itevs_con andalso*) null ud_cons then
          (* All type and term variables instantiated and all conjuncts
           * discharged.
           *)
          SOME (tyis, teis, ityvs, itevs_con, exps, asm_rw_is, used_asms, ud_cons)
        else
          (* Not all variables instantiated, or not all conjuncts discharged. Try
           * to find additional instantiations by comparing the succedent of the
           * lemma with subterms of the goal.
           *)
          let val bvars = [] in
          let val meet = is_double_submeet_suc eqs suc gol itevs_suc teis tyis ityvs bvars in
            if isSome meet then
              let val (tyis, teis, ityvs, itevs_suc, teis_udc) = valOf meet in
              let val d_cons = map (fn d_con => subst (teis @ teis_udc) (inst tyis d_con)) d_cons
                  val ud_cons = map (fn ud_con => subst (teis @ teis_udc) (inst tyis ud_con)) ud_cons in
                if (length tyis > ptyis_length orelse length teis > pteis_length) andalso (not o null) ud_cons then
                  (* New instantiations and remaining conjuncts: Do another round. *)
                  let val pis = (length tyis, length teis)
                      val suc = subst (teis @ teis_udc) (inst tyis suc)
                      val itevs_lem = map (inst tyis) itevs_lem
                      val itevs_con = filter (fn itev => all (fn i => not_same_term itev (#redex i)) teis) (map (inst tyis) itevs_con)
                      val asms = A0
                      val cons = ud_cons in
                  let val ud_cons = []
                      val itevs_lcs = (itevs_lem, itevs_con, itevs_suc) in
                    find_lemma_is disch_all pis A0 eqs used_asms d_cons ud_cons inv_names gol suc itevs_lcs teis tyis ityvs exps asm_rw_is asms cons
                  end end
                else if disch_all andalso (not o null) ud_cons then
                  NONE
                else if (not o null) ityvs then
                  (* All type variables must be instantiated. Compare conjuncts
                   * with assumptions.
                   *)
                  find_tyis_asms_cons eqs tyis teis ityvs itevs_suc exps asm_rw_is used_asms ud_cons A0 d_cons
                else
                  (* No additional instantiations found in this conjunction
                   * processing round: No progress made, which means no
                   * additional undischarged conjuncts can be discharged. Return.
                   *)
                  SOME (tyis, teis, ityvs, itevs_suc, exps, asm_rw_is, used_asms, ud_cons)
              end end
            else if (length tyis > ptyis_length orelse length teis > pteis_length) andalso (not o null) ud_cons then
              (* New instantiations and remaining conjuncts: Do another round. *)
              let val pis = (length tyis, length teis)
                  val cons = ud_cons
                  val asms = A0 in
              let val ud_cons = [] in
                find_lemma_is disch_all pis A0 eqs used_asms d_cons ud_cons inv_names gol suc itevs_lcs teis tyis ityvs exps asm_rw_is asms cons
              end end
            else if disch_all andalso (not o null) ud_cons then
              NONE
            else if (not o null) ityvs then
              (* All type variables must be instantiated. Compare conjuncts with
               * assumptions.
               *)
              find_tyis_asms_cons eqs tyis teis ityvs itevs_con exps asm_rw_is used_asms ud_cons A0 d_cons
            else
              (* No additional instantiations found in this conjunction
               * processing round.
               *)
              SOME (tyis, teis, ityvs, itevs_con, exps, asm_rw_is, used_asms, ud_cons)
          end end
      end
    | find_lemma_is disch_all pis A0 eqs used_asms d_cons ud_cons inv_names gol suc itevs_lcs teis tyis ityvs exps asm_rw_is [] (con::cons) =
      let val (itevs_lem, itevs_con, itevs_suc) = itevs_lcs in
        if is_eq con then
          let val (l, r) = dest_eq con in
            if same_term l r then
              (* Conjunct is of the form t = t and will be dischard by
               * REWRITE_RULE [] by the function applying find_lemma_is.
               *
               * The current conjunct can be considered discharged and the next
               * conjunct is processed.
               *)
              let val asms = A0 in
                find_lemma_is disch_all pis A0 eqs used_asms d_cons ud_cons inv_names gol suc itevs_lcs teis tyis ityvs exps asm_rw_is asms cons
              end
            else if is_in itevs_con l orelse is_in itevs_con r then
              let val (from, to) = if is_in itevs_con l then (l, r) else (r, l) in
              let val new_itevs_suc = filter (is_in itevs_con) (free_vars to) in
                if is_in new_itevs_suc from then
                  (* from is instantiated to a subterm that contains from. Cyclic
                   * instantiations are avoided and con is an undicharged
                   * conjunct.
                   *)
                  let val ud_cons = con::ud_cons
                      val asms = A0 in
                    find_lemma_is disch_all pis A0 eqs used_asms d_cons ud_cons inv_names gol suc itevs_lcs teis tyis ityvs exps asm_rw_is asms cons
                  end 
                else
                  let val d_cons = (subst [from |-> to] con)::(map (subst [from |-> to]) d_cons)
                      val ud_cons = map (subst [from |-> to]) ud_cons
                      val suc = subst [from |-> to] suc
                      val itevs_con = filter (not_same_term from) itevs_con (* from no longer instantiable in the conjunct. *)
                      val itevs_suc = union_lists same_term (filter (not_same_term from) itevs_suc) new_itevs_suc
                      val teis = (substitute_teis_to (from |-> to) teis) @ [from |-> to]
                      val asms = A0
                      val cons = map (subst [from |-> to]) cons in
                  let val itevs_lcs = (itevs_lem, itevs_con, itevs_suc) in
                    find_lemma_is disch_all pis A0 eqs used_asms d_cons ud_cons inv_names gol suc itevs_lcs teis tyis ityvs exps asm_rw_is asms cons
                  end end
              end end
            else
              let val ud_cons = con::ud_cons
                  val asms = A0 in
                find_lemma_is disch_all pis A0 eqs used_asms d_cons ud_cons inv_names gol suc itevs_lcs teis tyis ityvs exps asm_rw_is asms cons
              end
          end
        else
          let val ud_cons = con::ud_cons
              val asms = A0 in
            find_lemma_is disch_all pis A0 eqs used_asms d_cons ud_cons inv_names gol suc itevs_lcs teis tyis ityvs exps asm_rw_is asms cons
          end
      end
    | find_lemma_is disch_all pis A0 eqs used_asms d_cons ud_cons inv_names gol suc itevs_lcs teis tyis ityvs exps asm_rw_is (asm::asms) (con::cons) =
      let val (itevs_lem, itevs_con, itevs_suc) = itevs_lcs in
(* Equations used to find meet must not contain the current assumption asm that shall be matched with the current conjunct con*)
      let val meet = is_double_meet_q (filter (not_same_term asm) eqs) con suc asm itevs_lem itevs_con itevs_suc teis tyis ityvs in
        if isSome meet then
          let val (u_con, u_suc, u_itevs_lem, u_itevs_con, u_itevs_suc, u_teis, u_tyis, u_ityvs, marks, asm_rw_i, teis_udc) = valOf meet in
          let val (u_new_asm, u_d_con, u_ud_con, u_asm_rw_i) = add_undischarged_conjunct asm u_itevs_con u_con asm_rw_i in
          let val u_used_asms = used_asms @ u_new_asm
              val u_d_cons = (map (fn d_con => subst (u_teis @ teis_udc) (inst u_tyis d_con)) d_cons) @ u_d_con
              val u_ud_cons = (map (fn ud_con => subst (u_teis @ teis_udc) (inst u_tyis ud_con)) ud_cons) @ u_ud_con
              val u_inv_names = inv_names @ marks
              val u_itevs_lcs = (u_itevs_lem, u_itevs_con, u_itevs_suc)
              val u_asm_rw_is = asm_rw_is @ u_asm_rw_i
              val u_asms = A0
              val u_cons = map (subst (u_teis @ teis_udc)) (map (inst u_tyis) cons) in
          let val exp_asm_rw_is = find_lemma_is
                  disch_all pis A0 eqs u_used_asms u_d_cons u_ud_cons u_inv_names gol u_suc u_itevs_lcs u_teis u_tyis u_ityvs
                  exps u_asm_rw_is u_asms u_cons in
            if isSome exp_asm_rw_is then
              exp_asm_rw_is
            else (* Did not work with the current assumption @asm, try the following assumptions @asms. *)
              find_lemma_is disch_all pis A0 eqs used_asms d_cons ud_cons inv_names gol suc itevs_lcs teis tyis ityvs exps asm_rw_is asms (con::cons)
          end end end end
        else
          let val expansion = find_expansion_conjunct_assumption tyis teis ityvs itevs_con con asm in
            if isSome expansion then
              let val (tyis, teis, ityvs, itevs_con, ethm) = valOf expansion in
              (* The returned asms from variable_to_pattern contain updated versions of asm and asms. *)
              let val      (A0, eqs, used_asms, d_cons, ud_cons, inv_names, gol, suc, itevs_lcs, teis, exps, asm_rw_is, asms, cons) =
        variable_to_pattern A0  eqs  used_asms  d_cons  ud_cons  inv_names  gol  suc  itevs_lcs  teis  exps  asm_rw_is  (asm::asms) (con::cons) ethm tyis itevs_con in
find_lemma_is disch_all pis A0  eqs  used_asms  d_cons  ud_cons  inv_names  gol  suc  itevs_lcs  teis
                                                                                     tyis ityvs        exps  asm_rw_is  asms         cons
              end end
            else (* Current assumption and expansion did not work, try following assumptions. *)
              find_lemma_is disch_all pis A0 eqs used_asms d_cons ud_cons inv_names gol suc itevs_lcs teis tyis ityvs exps asm_rw_is asms (con::cons)
          end
      end end





(*
(* Removes the nth element, counting from 0, and returns that element and the
 * resulting list after removing that element.
 *)
fun extract_nth (l, n) =
  if n = 0 then
    (hd l, tl l)
  else if n = length l - 1 then
    (last l, List.take (l, n))
  else
    let val element = List.nth (l, n)
        val prefix = List.take (l, n)
        val suffix = List.drop (l, n + 1) in
      (element, prefix @ suffix)
    end
*)
(*
val ASMS = asms
val CONS = cons
val (con, cons) = extract_nth (cons, 3)
val (asm, asms) = extract_nth (asms, 0)
val (asm, asms) = extract_nth (asms, 0)
val (asm, asms) = extract_nth (asms, 0)
val (asm, asms) = extract_nth (asms, 0)
val (asm, asms) = extract_nth (asms, 0)
val (asm, asms) = extract_nth (asms, 0)



val (con, cons) = extract_nth (cons, 1)
val (asm, asms) = extract_nth (asms, 3)


val (pis, A, eqs, used_asms, ud_cons, inv_names, gol, suc, itevs_lcs, teis, tyis, ityvs, exps, asm_rw_is, asms, cons) =
    (pis, A, eqs, u_used_asms, u_ud_cons, u_inv_names, gol, u_suc, u_itevs_lcs, u_teis, u_tyis, u_ityvs, exps, u_asm_rw_is, u_asms, u_cons)



val (con, cons) = extract_nth (cons, 0)
val (asm, asms) = extract_nth (asms, 0)






val asm::asms = asms
val asm::asms = asms
val con::cons = cons

val asm::asms = asms

val (pis, A, eqs, used_asms, ud_cons, inv_names, gol, suc, itevs_lcs, teis, tyis, ityvs, exps, asm_rw_is, asms, cons) = (pis, A, eqs, u_used_asms, u_ud_cons, u_inv_names, gol, u_suc, u_itevs_lcs, u_teis, u_tyis, u_ityvs, exps, u_asm_rw_is, u_asms, u_cons)
...

val asm::asms = asms
val con::cons = cons

val (pis, A, eqs, used_asms, ud_cons, inv_names, gol, suc, itevs_lcs, teis, tyis, ityvs, exps, asm_rw_is, asms, cons) = (pis, A, eqs, u_used_asms, u_ud_cons, u_inv_names, gol, u_suc, u_itevs_lcs, u_teis, u_tyis, u_ityvs, exps, u_asm_rw_is, u_asms, u_cons)


val asm = List.nth (asms, 3)
val con::cons = cons
lemma


*)
  (*               A ?- t
   * -------------------------------------
   * A u {variable = pattern v1...vn} ?- t
   *
   * @exp_thm = '|- ?x1...xn. variable = pattern x1...xn'
   * @ieq = 'variable = pattern v1...vn'
   * @xis: [xi |-> vi]
   *)
  fun ADD_IEQ_TAC exp_thm ieq xis (A, t) =
      let val A' = ieq::A
          fun chooses thm ieq [] = thm
            | chooses thm ieq ({redex = x, residue = v}::xis) =     (* ieq = s[v/x] *)
              let val xterm = mk_exists (x, subst [v |-> x] ieq) in (* xterm = ?x. s, since v is fresh. *)
                chooses (CHOOSE (v, ASSUME xterm) thm) xterm xis
              end in
      let val validation = fn thm => PROVE_HYP exp_thm (chooses thm ieq xis) in
        (A', t, validation)
      end end

  fun EXPAND_TAC [] (A, t) = (A, t, fn thm => thm)
    | EXPAND_TAC ((exp_thm, exp_asm, xis)::exps) (A0, t0) =
      let val (A1, t1, v1) = ADD_IEQ_TAC exp_thm exp_asm xis (A0, t0) in
      let val (subgoals2, v2) = ASM_RW_OTHERS_TAC false exp_asm (A1, t1) in
      let val (A3, t3, v3) = EXPAND_TAC exps (hd subgoals2) in
        (A3, t3, fn thm => (v1 o v2) [v3 thm])
      end end end

  fun strip_qvs asm nqvs =
      if nqvs = 0 then
        asm
      else
        strip_qvs ((#2 o dest_forall) asm) (nqvs - 1)

  (*            A u {!x1...xn. asm} ?- t
   * ---------------------------------------------------
   * A u {!x1...xn. asm, !itevs_asm. asm[teis_asm]} ?- t
   *
   *       --------------------------------ASSUME
   *       {!x1...xn. asm} |- !x1...xn. asm
   *       --------------------------------SPEC_ALL
   *            {!x1...xn. asm} |- asm
   *       --------------------------------INST teis_asm
   *       {!x1...xn. asm} |- asm[teis_asm]
   * --------------------------------------------GENL itevs_asm    ---------------------------------------------------INPUT
   * {!x1...xn. asm} |- !itevs_asm. asm[teis_asm]                  A u {!x1...xn. asm, !itevs_asm. asm[teis_asm]} |- t
   * -----------------------------------------------------------------------------------------------------------------PROVE_HYP
   *                                            A u {!x1...xn. asm} |- t
   *)
  fun IASM_TAC asm teis_asm itevs_asm nqvs (A, t) =
    let val stripped_asm = strip_qvs asm nqvs in
    let val instantiated_stripped_asm = subst teis_asm stripped_asm in
    let val iasm = list_mk_forall (itevs_asm, instantiated_stripped_asm) in
    let val (A, t) = (iasm::A, t)
        val v = fn thm =>
                let val asm_thm = ASSUME asm in
                let val uq_asm_thm = SPEC_ALL asm_thm in
                let val iuq_asm_thm = INST teis_asm uq_asm_thm in
                let val i_asm_thm = GENL itevs_asm iuq_asm_thm in
                let val thm = PROVE_HYP i_asm_thm thm in
                  thm
                end end end end end in
      (A, t, v, iasm)
    end end end end



  fun asm_rw_substitutions [] = ([], [])
    | asm_rw_substitutions ((mark, {redex = old_subterm, residue = new_subterm}, asm_eq, is_eq, reflect)::asm_rws) =
      let val (substitution_templates, rw_thms) = asm_rw_substitutions asm_rws in
      let val asm_eq_thm = ((INST_TY_TERM (is_eq, [])) o SPEC_ALL o (fn thm => if reflect then GSYM thm else thm) o ASSUME) asm_eq in
        ({redex = mark, residue = new_subterm}::substitution_templates, {redex = mark, residue = asm_eq_thm}::rw_thms)
      end end

  (* A u {l1 = r1, ..., lm = rm, rm+1 = lm+1, ..., rn = ln} u {asm} ?- t
   * ----------------------------------------------------------------------------
   * A u {l1 = r1, ..., lm = rm, rm+1 = lm+1, ..., rn = ln} u {asm, new_asm} ?- t
   *
   * new_asm = template[marki |-> ri, i <= m; marki |-> li, i >= m + 1] 
   *
   *     asm = template[marki |-> li, i <= m; marki |-> ri, i >= m + 1]
   *
   * mark_unrefl_refl_subst = (
   *  [(mark1  , l1  , r1  , l1   = r1  ), ..., (markm, lm, rm, lm = rm)],
   *  [(markm+1, lm+1, rm+1, rm+1 = lm+1), ..., (markn, ln, rn, rn = ln)]
   * )
   *)
  fun ADD_RW_ASM_TAC asm template asm_rws (old_A, old_t) =
    let val (substitution_templates, rw_thms) = asm_rw_substitutions asm_rws in
    let val new_asm = subst substitution_templates template in
    let val new_A = new_asm::old_A
        val new_t = old_t
        val validation = fn new_thm =>
        (* A u {l1 = r1, ..., lm = rm, rm+1 = lm+1, ..., rn = ln} u {asm, new_asm} |- t
         * ----------------------------------------------------------------------------
         *     A u {l1 = r1, ..., lm = rm, rm+1 = lm+1, ..., rn = ln} u {asm} |- t
         *
         *                        ----------ASSUME asm
         *                        asm |- asm
         * ----------------------------------------------------SUBST mark_to_thm template
         * {l1=r1...lm=rm,rm+1=lm+1...rn=ln} u {asm} |- new_asm    A u {l1=r1...lm=rm,rm+1=lm+1...rn=ln} u {asm,new_asm} |- t
         * ------------------------------------------------------------------------------------------------------------------PROVE_HYP
         *                         A u {l1=r1 ... lm=rm, rm+1=lm+1 ... rn=ln} u {asm} |- t
         *)
          let val asm_thm = ASSUME asm in
          let val new_asm_thm = SUBST rw_thms template asm_thm in
          let val old_thm = PROVE_HYP new_asm_thm new_thm in
            old_thm
          end end end in
      (new_A, new_t, validation, new_asm)
    end end end

(*
val template = asm_rw_template
val asm_rws = mark_unrefl_refl_substs
val (old_A, old_t) = (A0, t0)
*)

  (* A u {l1 = r1, ..., lm = rm, rm+1 = lm+1, ..., rn = ln} u {asm} ?- t
   * ----------------------------------------------------------------------------
   * A u {l1 = r1, ..., lm = rm, rm+1 = lm+1, ..., rn = ln} u {asm, new_asm} ?- t
   *
   * new_asm = template[marki |-> ri, i <= m; marki |-> li, i >= m + 1] 
   *
   *     asm = template[marki |-> li, i <= m; marki |-> ri, i >= m + 1]
   *
   * mark_unrefl_refl_subst = (
   *  [(mark1  , l1  , r1  , l1   = r1  ), ..., (markm, lm, rm, lm = rm)],
   *  [(markm+1, lm+1, rm+1, rm+1 = lm+1), ..., (markn, ln, rn, rn = ln)]
   * )
   *
   * new_asm is reflected if reflect_asm is true (meaning that new_asm is an
   * equation).
   *)
  fun ADD_RW_ASM_REFL_TAC asm reflect_asm asm_rw_template mark_unrefl_refl_substs (A0, t0) =
    if reflect_asm then
      let val (A1, t1, v1, new_asm1) = ADD_RW_ASM_TAC asm asm_rw_template mark_unrefl_refl_substs (A0, t0) in
      let val (subgoals2, v2) = REFL_ASM_TAC new_asm1 (A1, t1) in
      let val (A2, t2) = hd subgoals2
          val (qvs, eq) = strip_forall new_asm1 in
      let val (l, r) = dest_eq eq in
      let val reflected_eq = mk_eq (r, l) in
      let val reflected_new_asm1 = list_mk_forall (qvs, reflected_eq) in
        (A2, t2, fn thm => (v1 o v2) [thm], reflected_new_asm1)
      end end end end end end
    else
      ADD_RW_ASM_TAC asm asm_rw_template mark_unrefl_refl_substs (A0, t0)

  (* Algorithm:
   * 1. Rewrite and reflect.
   * 2. Instantiate.
   *)
  fun ADD_IASM_REFL_TAC (asm, asm_rw_template, mark_unrefl_refl_substs, reflect_asm, teis_asm, itevs_asm, nqvs) (A0, t0) =
    let val (A1, t1, v1, new_asm1) = ADD_RW_ASM_REFL_TAC asm reflect_asm asm_rw_template mark_unrefl_refl_substs (A0, t0) in
    let val (A2, t2, v2, new_asm2) = IASM_TAC new_asm1 teis_asm itevs_asm nqvs (A1, t1) in
      (A2, t2, v1 o v2, [new_asm1, new_asm2])
    end end

(*
val (asm, asm_rw_template, mark_unrefl_refl_substs, reflect_asm, teis_asm, itevs_asm, nqvs) = asm_rw_i
*)

  (* @asm: Assumeption to instantiate or rewrite, or both.
   * @asm_rw_tem: Assumption but with marks at positions that should be rewritten
   *  as specified by mark_unrefl_refl_substs.
   * @mark_unrefl_refl_substs: A list of quituples
   *  [(mark, old_subterm |-> new_subterm, qeq, is_eq, reflect_eq)], where
   *  -eq = 'old_subterm = new_subterm' if reflect_eq = false, and
   *  -eq = 'new_subterm = old_subterm' if reflect_eq = true.
   * @reflect_asm: True if and only if asm shall be reflected, implying that asm
   *  is an equation.
   * @teis_asm: substititions from quantified variables to instantiation values.
   * @itevs_asm: Variables remainining uninstantiated, after stripping off @nqvs
   *  quantifiers and instantiating the quantified variables according to
   *  @teis_asm. This means length @teis_asm + length @itevs_asm = @nqvs.
   * @nqvs: How many quantifiers of asm to strip off, without necessarily
   *  instantiating all of them.
   *)
  fun RW_ASMS_TAC [] (A, t) = (A, t, fn thm => thm, [])
    | RW_ASMS_TAC (asm_rw_i::asm_rw_is) (A0, t0) =
      let val (A1, t1, v1, new_asms1) = ADD_IASM_REFL_TAC asm_rw_i (A0, t0) in
      let val (A2, t2, v2, new_asms2) = RW_ASMS_TAC asm_rw_is (A1, t1) in
        (A2, t2, v1 o v2, new_asms1 @ new_asms2)
      end end
(*
val (A0, t0) = (A1, t1)
val asm_rw_i0::asm_rw_i1::[] = asm_rw_is
val asm_rw_i = asm_rw_i1

val asm_rw_i::asm_rw_is = length asm_rw_is
val (A', t') = (A1, t1)
val (A0, t0) = (A1, t1)




RW_ASMS_TAC asm_rw_is (A2, t2)

val (A0, t0) = (A2, t2)
val asm_rw_i::asm_rw_is = asm_rw_is
val (A0, t0) = (A1, t1)
val asm_rw_i::asm_rw_is = asm_rw_is

*)













  (* Renames the type variables of a given theorem such that no type variable in
   * the theorem occurs in the goal (A, t).
   *
   * This is used to avoid instantiating a type variable alpha of @lemma to beta,
   * when beta occurs in @lemma. This can cause type conflicts in the theorem
   * when not all type variables of the theorem are instantiated simultaneously.
   *)
  fun uniquify_tyvs A t lemma =
         (* list_mk_conj is used to form one term containing all type variables
          * in the theorem, from which type_vars_in_term will extract all type
          * variables without duplicates.
          *)
    let val invalid_type_variables = (type_vars_in_term o list_mk_conj) (t::A)
        val (hypotheses, conclusion) = dest_thm lemma in
    let val type_variables = type_vars_in_term (list_mk_conj (conclusion::hypotheses))
        fun uniquify_type_variable renamings invalid_type_variables original_type_variable =
      let fun uniquify_type_variable_rec type_variable =
        if exists (same_type type_variable) invalid_type_variables then
          let val type_variable_name = (hd o tl o String.explode o dest_vartype) type_variable in
          let val next_type_variable = (mk_vartype o String.implode) [#"'", Char.succ type_variable_name] in
            uniquify_type_variable_rec next_type_variable
          end end
        else
          (invalid_type_variables @ [type_variable], renamings @ [{redex = original_type_variable, residue = type_variable}]) in
        uniquify_type_variable_rec original_type_variable
      end
        fun rename_type_variables (type_variable, (invalid_names, renamings)) =
            uniquify_type_variable renamings invalid_names type_variable in
    let val renaming_substitutions = #2 (foldl rename_type_variables (invalid_type_variables, []) type_variables) in
    let val type_renamed_lemma = INST_TYPE renaming_substitutions lemma in
      type_renamed_lemma
    end end end end

  fun is_identity_tyis [] = true
    | is_identity_tyis ({redex = from, residue = to}::is) = same_type from to andalso is_identity_tyis is

  fun uniquify_tevs A t lemma = uniquify_qimp_qvs (map term_to_string (all_vars (list_mk_conj (t::A)))) lemma

  fun eq_substitution [] [] = ([], [])
    | eq_substitution (_::_) [] =
      raise (mk_HOL_ERR "helper_tactics" "eq_substitution" "More \"from\"-components than \"to\"-components.")
    | eq_substitution [] (_::_) =
      raise (mk_HOL_ERR "helper_tactics" "eq_substitution" "More \"to\"-components than \"from\"-components.")
    | eq_substitution (from::froms) (to::tos) =
      let val (from_tos, to_froms) = eq_substitution froms tos in
        ((from |-> to)::from_tos, (to |-> from)::to_froms)
      end

  fun generate_substitutions [] [] = ([], [])
    | generate_substitutions [] (_::_) = raise (mk_HOL_ERR "helper_tactics" "generate_substitutions" "More to values.")
    | generate_substitutions (_::_) [] = raise (mk_HOL_ERR "helper_tactics" "generate_substitutions" "More from values.")
    | generate_substitutions (f::fs) (t::ts) =
      let val (renamings, reverse_renamings) = generate_substitutions fs ts in
        ((f |-> t)::renamings, (t |-> f)::reverse_renamings)
      end

  fun uniquify_quantified_assumptions_rec invalid_names [] = ([], invalid_names)
    | uniquify_quantified_assumptions_rec invalid_names (asm::asms) =
      let val (qasm_renamings, invalid_names) = uniquify_quantified_assumptions_rec invalid_names asms in
        if is_forall asm then
          let val (qvs, unq_asm) = strip_forall asm in
          let val (nvs, invalid_names) = rename_tevs invalid_names qvs in
          let val (renamings, reverse_renamings) = generate_substitutions qvs nvs in
          let val nasm = list_mk_forall (nvs, subst renamings unq_asm) in
            ((asm, qvs, nasm, nvs)::qasm_renamings, invalid_names)
          end end end end
        else
          (qasm_renamings, invalid_names)
      end
(*
  fun new_to_old_asm nasm [] =
      raise (mk_HOL_ERR "helper_tactics" "new_to_old_asm" "New assumption not associated with an old assumption.")
    | new_to_old_asm nasm ((new, old)::new_to_old) = if same_term nasm new then old else new_to_old_asm nasm new_to_old

  fun new_to_old_asms new_to_old [] = []
    | new_to_old_asms new_to_old (nasm::nasms) = (new_to_old_asm nasm new_to_old)::(new_to_old_asms new_to_old nasms)      
*)
  fun uniquify_quantified_assumptions invalid_names A =
    let val invalid_names = union_lists equal invalid_names (map term_to_string (free_varsl A)) in
    let val (qasm_renamings, invalid_names) = uniquify_quantified_assumptions_rec invalid_names A in
      qasm_renamings
    end end








(***************************)
  fun rename_forall_imp_conv qx nvs =
      let val qx_thm = ASSUME qx in                     (* !X. P X |- !X. P X     *)
      let val qx_hyp_y_thm = SPECL nvs qx_thm in        (* !X. P X |- P Y         *)
      let val qx_hyp_qy_thm = GENL nvs qx_hyp_y_thm in  (* !X. P X |- !Y. P y     *)
      let val qx_imp_qy_thm = DISCH qx qx_hyp_qy_thm in (* |- !X. P X ==> !Y. P y *)
        qx_imp_qy_thm
      end end end end

  (* Given '!X. P X' returns '|- (!Y. P Y) = (!X. P X)'.
   *
   *                               --------------------ASSUME !X. P X
   *                               {!X. P X} |- !X. P X
   *                               --------------------SPECL Y
   *                                 {!X. P X} |- P Y
   *                              ----------------------GENL Y
   *                              {!X. P X} |- (!Y. P Y)
   *                             ------------------------DISCH !X. P X
   * |- !Y. P Y ==> (!X. P X)    |- !X. P X ==> (!Y. P Y)
   * ----------------------------------------------------IMP_ANTISYM_RULE
   *             |- (!X. P X) = (!Y. P Y)
   *)
  fun rename_forall_eq_conv qx qvs qy nvs =
      let val reverse_renaming = (#1 o strip_forall) qx in
      let val qx_imp_qy_thm = rename_forall_imp_conv qx nvs in
      let val qy_imp_qx_thm = rename_forall_imp_conv qy qvs in
      let val qy_eq_qx_thm = IMP_ANTISYM_RULE qy_imp_qx_thm qx_imp_qy_thm in
        qy_eq_qx_thm
      end end end end
(*
val qasm = “!(x : 'a) (y : 'b) (z : 'c). P x y z : bool”
val renaming = [“(a : 'a)”, “(b : 'b)”, “(c : 'c)”]
*)

  fun replace_assumption asm_old asm_new [] = []
    | replace_assumption asm_old asm_new (asm::asms) =
      if same_term asm_old asm then
        asm_new::asms
      else
        asm::(replace_assumption asm_old asm_new asms)

  (* A u {!X. P X} ?- t
   * ------------------qasm = !X. P X, renaming = Y
   * A u {!Y. P Y} ?- t
   *
   *  A u {!Y. P Y} |- t
   * --------------------
   * A |- (!Y. P Y) ==> t
   * --------------------SUBST mark |-> |- (!Y. P Y) = (!X. P X), (mark ==> t)
   * A |- (!X. P X) ==> t
   * --------------------
   *  A u {!X. P X} |- t
   *)
  fun UNIQUIFY_FORALL_TAC qasm qvs nasm nvs (A, t) =
      let val (A', t') = (replace_assumption qasm nasm A, t)
          val v = fn thm =>
                  let val imp_thm = DISCH nasm thm
                      val mark = genvar bool
                      val rw_thm = rename_forall_eq_conv qasm qvs nasm nvs in
                  let val template = mk_imp (mark, concl thm)
                      val rw_thm_substs = [mark |-> rw_thm] in
                  let val imp_rw_thm = SUBST rw_thm_substs template imp_thm in
                  let val thm = UNDISCH imp_rw_thm in
                    thm
                  end end end end in
        (A', t', v)
      end

  fun UNIQUIFY_FORALLS_TAC [] (A, t) = (A, t, fn thm => thm)
    | UNIQUIFY_FORALLS_TAC ((qasm, qvs, nasm, nvs)::qasm_renamings) (A, t) =
      let val (A, t, v1) = UNIQUIFY_FORALL_TAC qasm qvs nasm nvs (A, t) in
      let val (A, t, v2) = UNIQUIFY_FORALLS_TAC qasm_renamings (A, t) in
        (A, t, v1 o v2)
      end end

  fun REVERSE_UNIQUIFY_FORALLS_TAC [] (A, t) = (A, t, fn thm => thm)
    | REVERSE_UNIQUIFY_FORALLS_TAC ((qasm, qvs, nasm, nvs)::qasm_renamings) (A, t) =
      let val (A, t, v1) = UNIQUIFY_FORALL_TAC nasm nvs qasm qvs (A, t) in
      let val (A, t, v2) = REVERSE_UNIQUIFY_FORALLS_TAC qasm_renamings (A, t) in
        (A, t, v1 o v2)
      end end

(***************************)





  fun is_eq_reflected_neg_eq neg_eq_ud_con neg_eq_asm =
    if is_neg neg_eq_asm then
      if (is_eq o dest_neg) neg_eq_asm then
        let val (l, r) = (dest_eq o dest_neg) neg_eq_asm in
        let val reflected_neg_eq_asm = (mk_neg o mk_eq) (r, l) in
          if same_term neg_eq_ud_con reflected_neg_eq_asm then
            SOME (neg_eq_ud_con, neg_eq_asm)
          else
            NONE
        end end
      else
        NONE
    else
      NONE

  fun find_neg_eqs_to_reflect neg_eq_ud_con [] = NONE
    | find_neg_eqs_to_reflect neg_eq_ud_con (neg_eq_asm::neg_eq_asms) =
      let val neg_eq_ud_con_neg_eq_asm = is_eq_reflected_neg_eq neg_eq_ud_con neg_eq_asm in
        if isSome neg_eq_ud_con_neg_eq_asm then
          neg_eq_ud_con_neg_eq_asm
        else
          find_neg_eqs_to_reflect neg_eq_ud_con neg_eq_asms
      end

  fun find_neg_eqs_to_reflects neg_eq_asms [] = []
    | find_neg_eqs_to_reflects neg_eq_asms (neg_eq_ud_con::neg_eq_ud_cons) =
      let val d_con_neg_eqs_to_reflects = find_neg_eqs_to_reflects neg_eq_asms neg_eq_ud_cons in
      let val neg_eq_ud_con_neg_eq_asm = find_neg_eqs_to_reflect neg_eq_ud_con neg_eq_asms in
        if isSome neg_eq_ud_con_neg_eq_asm then
          (valOf neg_eq_ud_con_neg_eq_asm)::d_con_neg_eqs_to_reflects
        else
          d_con_neg_eqs_to_reflects
      end end

  (*
   *   ----------------ASSUME r <> l
   *   r <> l |- r <> l
   * ---------------------SYNTAX rewrite
   * r <> l |- r = l ==> F
   * --------------------SUBST (marker |-> (SPECL [l, r] INST_TYPE [alpha |-> type_of l] boolTheory.EQ_SYM_EQ) 'marker ==> f'
   * r <> l |- l = r ==> F
   * ---------------------SYNTAX rewrite
   * r <> l |- l <> r
   *)
  fun reflect_neg_eq_thm neg_eq =
    let val neg_eq_imp_f_thm = SYM (List.nth (CONJUNCTS (SPECL [dest_neg neg_eq] boolTheory.IMP_CLAUSES), 4))
        val (l, r) = (dest_eq o dest_neg) neg_eq
        val r_eq_l_thm = ASSUME neg_eq
        val marker = genvar_term T in
    let val neg_eq_thm = SUBST [marker |-> neg_eq_imp_f_thm] marker r_eq_l_thm
        val template = mk_imp (marker, F) in
    let val neg_r_eq_l_imp_f_thm = SUBST [marker |-> (SPECL [l, r] (INST_TYPE [alpha |-> type_of l] boolTheory.EQ_SYM_EQ))] template neg_eq_thm
        val neg_eq_imp_f_thm = List.nth (CONJUNCTS (SPECL [mk_eq (r, l)] boolTheory.IMP_CLAUSES), 4) in
    let val neg_eq_thm = SUBST [marker |-> neg_eq_imp_f_thm] marker neg_r_eq_l_imp_f_thm in
      neg_eq_thm
    end end end end

  (* A u {l <> r} ?- t
   * -----------------
   * A u {r <> l} ?- t
   *)
  fun add_reflected_asms_thms [] = []
    | add_reflected_asms_thms ((con_to_discharge, asm_to_reflect)::dischargable_cons_asms_to_reflect) =
      let val neg_eq_sym_thm = reflect_neg_eq_thm asm_to_reflect in
        neg_eq_sym_thm::(add_reflected_asms_thms dischargable_cons_asms_to_reflect)
      end

  fun find_neg_eq_asms ud_cons A =
    let fun is_neg_eq neg_eq = if is_neg neg_eq then (is_eq o dest_neg) neg_eq else false in
    let val neg_eq_ud_cons = filter is_neg_eq ud_cons
        val neg_eq_asms = filter is_neg_eq A in
    let val dischargable_cons_asms_to_reflect = find_neg_eqs_to_reflects neg_eq_asms neg_eq_ud_cons in
    let val (discharged_cons, asms_to_remove) = unzip dischargable_cons_asms_to_reflect in
    let val thms = add_reflected_asms_thms dischargable_cons_asms_to_reflect in
      (thms, discharged_cons, asms_to_remove)
    end end end end end






  fun REMOVE_ASMS_TAC [] (A, t) = (A, t, (fn thm => thm) : Thm.thm -> Thm.thm)
    | REMOVE_ASMS_TAC (asm::asms) (A, t) =
      let val (subgoals, validation) = REMOVE_ASM_TAC asm (A, t) in
      let val (A1, t1) = hd subgoals
          val v1 = fn thm => validation [thm] in
      let val (A2, t2, v2) = REMOVE_ASMS_TAC asms (A1, t1) in
        (A2, t2, v1 o v2)
      end end end

  fun list_to_string element_to_string [] = ""
    | list_to_string element_to_string (e::es) = String.concat [element_to_string e, " ", list_to_string element_to_string es]

  fun quantified_variables_not_occurring_in_lemma implication_variables itevs_lem =
    let val unused_variables = filter (fn fv => all (not_same_term fv) implication_variables) itevs_lem in
      if null unused_variables then
        ()
      else
        let val unused_variable_names = list_to_string term_to_string unused_variables in
        let val error_message = String.concat ["Quantified variables not occuring in the body of the lemma: ", unused_variable_names] in
          raise (mk_HOL_ERR "helper_tactics" "ADD_INST_SUC_TYPE_TAC" error_message)
        end end
    end

  fun find_lemma_is_prologue type_instantiable A t lemma =
    (* Can only change type variables of lemma if they may be instantiated. *)
    let val lemma = if type_instantiable then uniquify_tyvs A t lemma else lemma in
    let val ityvs = if type_instantiable then type_vars_in_term (list_mk_conj ((concl lemma)::(hyp lemma))) else []
    (* Quantified variables in the lemma do not overlap any variables in the goal, both quantified and unquantified.
     * This means that  *)
        val (imp, itevs_lem) = uniquify_tevs A t lemma in
    let val renamed_lemma = GENL itevs_lem imp in
    let val pis = (0, 0)
        val invalid_names = map term_to_string (all_varsl (((concl renamed_lemma)::(hyp renamed_lemma)) @ A)) in
    let val qasm_renamings = uniquify_quantified_assumptions invalid_names A in
    let val (A0, t0, v0) = UNIQUIFY_FORALLS_TAC qasm_renamings (A, t) in
    let val eqs = filter (is_eq o #2 o strip_forall) A0
        val used_asms = []
        val d_cons = []
        val ud_cons = []
        val inv_names = free_varsl (t::A0)
        val gol = t
        val implication = concl imp in
    let val implication_variables = free_vars implication
        val (antecedent, suc) = dest_imp implication in
        (* Error message to prohibit problems with instantiating quantified variables. *)
    let val _ = quantified_variables_not_occurring_in_lemma implication_variables itevs_lem
        val itevs_con = itevs_lem
        val itevs_suc = filter (is_in itevs_lem) (free_vars suc)
        val teis = []
        val tyis = []
        val exps = []
        val asm_rw_is = []
        val asms = A0
        val cons = strip_conj antecedent in
    let val itevs_lcs = (itevs_lem, itevs_con, itevs_suc) in
      (pis, A0, eqs, used_asms, d_cons, ud_cons, inv_names, gol, suc, itevs_lcs, teis, tyis, ityvs, exps, asm_rw_is, asms, cons, imp, t0, qasm_renamings, v0) :
           (int * int) * term list * term list * term list * term list *
           term list * term list * term * term *
           (term list * term list * term list) * {redex : term, residue : term} list * {redex : hol_type, residue : hol_type} list *
           hol_type list *
           (thm * term * ({redex : term, residue : term} list)) list *
           (term * term * (term * {redex: term, residue: term} * term * ({redex : term, residue : term} list) * bool) list * bool *
            {redex: term, residue: term} list * term list * int) list *
           term list * term list * thm * term * ((term * term list * term * term list) list) * (thm -> thm)
    end end end end end end end end end end    

  (*
   * A |- B ==> C
   * ------------DISCH
   * A u B |- C
   * ------------SUBST (SYM o neg_conj_disj_imp_simp_conv) C
   * A u B |- ~~C
   * -------------------NOT_ELIM
   * A u B |- ~C ==> F
   * -------------------DISCH
   * A u B u {~C} |- F
   * -------------------UNDISCH B
   * A u {~C} |- B ==> F
   * --------------------REWRITE_RULE
   * A u {~C} |- B' ==> F
   * --------------------DISCH
   * A u B' u {~C} |- F
   * ------------------UNDISCH ~C
   * A u B' |- ~C ==> F
   * ------------------NOT_INTRO
   * A u B' |- ~~C
   * -------------SUBST (neg_conj_disj_imp_simp_conv) ~~C
   * A u B' |- C
   * -------------UNDISCH B'
   * A |- B' ==> C
   *)
   fun SIMP_ANT_RULE thm =
     if (is_imp o concl) thm then
       let val imp = concl thm in       (* B ==> C *)
       let val (b, c) = dest_imp imp in (* (B, C) *)
       let val thm1 = UNDISCH thm in    (* A u B |- C *)
       let val not_not_c_eq_c = neg_conj_disj_imp_simp_conv ((mk_neg o mk_neg) c) in (* |- ~~C = C *)
         if isSome not_not_c_eq_c then
           let val not_not_c_eq_c = valOf not_not_c_eq_c in
           let val marker = genvar bool in
           let val thm2 = SUBST [marker |-> SYM not_not_c_eq_c] marker thm1 in (* A u B |- ~~C *)
           let val thm3 = NOT_ELIM thm2 in (* A u B |- ~C ==> F *)
           let val thm4 = UNDISCH thm3 in (* A u B u {~C} |- F *)
           let val thm5 = DISCH b thm4 in (* A u {~C} |- B ==> F *)
           let val thm6 = REWRITE_RULE [] thm5 in (* A u {~C} |- B' ==> F *)           (* Performs simplifications on B to produce B'. *)
           let val b' = (#1 o dest_imp o concl) thm6 in (* B' *)
           let val thm7 = UNDISCH thm6 in (* A u B' u {~C} |- F *)
           let val thm8 = DISCH (mk_neg c) thm7 in (* A u B' |- ~C ==> F *)
           let val thm9 = NOT_INTRO thm8 in (* A u B' |- ~~C *)
           let val thm10 = SUBST [marker |-> not_not_c_eq_c] marker thm9 in (* A u B' |- C *)
           let val thm11 = DISCH b' thm10 in
             thm11
           end end end end end end end end end end end end end
         else
           thm
       end end end end
     else
       thm


  (* @source_tactic: String name of the tactic invoking this tactic. Used for
   *  error messages.
   * @type_instantiable: True if and only if the lemma can be type instantiated.
   * @lemma: Lemma of the form A |- !X. B X /\ ... C X ==> D X, with D I to be
   *  added with I being an instantiation of X such that B I ... C I can be
   *  inferred from the assumptions of the goal via rewriting with help from
   *  equations among assumptions.
   * @invalid_names: Invalid variable names replacing existantially quantified
   *  variables. Initially, this list is set to the names of all free variables
   *  among the assumptions and the conclusion. During execution it is expanded
   *  with names of variables for expansions and marks in templates for rewrites.
   * @asms: Assumptions of the goal, that can be used to match conjuncts of the
   *  lemma.
   * @eqs: Equations among the assumptions of the goal, that can be used to
   *  rewrite assumptions of the goal to match conjuncts of the lemma.
   * @tyis: Type instantiations to be applied on the lemma.
   * @teis: Term instantiations to replace quantified variables of the lemma.
   * @exps: List of pairs of an expansion theorem and variables replacing the
   *  existantially quantified variables of the expansion theorem, used to match
   *  patterns of in a conjunct of the lemma.
   * @asm_rws: A list of quadruples
   *  (asm, asm_rw_template, mark_unrefl_refl_substs, reflect_asm):
   *  -asm: The assumption being matching to a conjunct.
   *  -asm_rw_template: Template used to rewrite asm to become conjunct.
   *  -mark_unrefl_refl_substs: A pair of lists, the first with equations to
   *   rewrite asm at marked positions according to asm_rw_template, and the
   *   second with equations to be reflected before rewriting asm at marked
   *   positions according to asm_rw_template.
   *  -reflect_asm: True if and only if asm (is an equation that) shall be
   *   reflected after being instantiated to become a conjunct.
   *
   * Algorithm:
   *  type_instantiation = []
   *  term_instantiation = []
   *  conjuncts = conjuncts of antecedent
   *  asm_rws = []
   *  for each conjunct in conjuncts
   *    (teis, tyis, asm, asm_rw_template, mark_unrefl_refl_substs, reflect_asm, exp) = match conjunct to assumptions or expand
   *    type_instantiation = merge_type_instantiations type_instantiation tyis
   *    term_instantiation = merge_term_instantiations term_instantiation teis
   *    asm_rws = asm_rws + [(asm, asm_rw_template, mark_unrefl_refl_substs, reflect_asm)]
   *    
   *    if failure with matching, expand or backtrack (e.g. matching against an
   *    incorrect assumption that is similar to the correct one). Remove asm from
   *    others at current step.
   *
   *  lemma = INST_TYPE type_instantiation lemma
   *  lemma = INST_TERM term_instantiation lemma
   *  lemma = CONJ_ANT_TO_HYP lemma
   *
   *  Apply EXPAND_TAC on exps
   *  Apply ADD_RW_ASM_REFL_TAC on itself and asw_rws and collect all new assumption due to rewriting of assumptions.
   *
   *  ASSUME lemma
   *
   *  REMOVE new_asms.
   *
   *
   *
   *    A ?- t
   * --------------lemma: B |- !X. C1 X /\ ... /\ Cn X ==> C X, B subset of A.
   * A u {C V} ?- t
   *
   * Where V is an instantiation of X, based on all Ci in A, and equalities
   * l = r in A enabling substitutions of hypotheses in A to discharge all Ci.
   *
   * Equalitites in lemma conjuncts (e.g. Ck: l = r or r = l does not matter, if
   * l = r or r = l is in A.
   *)
  fun ADD_INST_SUC_TYPE_TAC simp_conc disch_all source_tactic type_instantiable remove_used_asms lemma (A, t) =
    let val (pis, A0, eqs, used_asms, d_cons, ud_cons, inv_names, gol, suc, itevs_lcs, teis, tyis, ityvs, exps, asm_rw_is, asms, cons, imp, t0, qasm_renamings, v0) = find_lemma_is_prologue type_instantiable A t lemma in
    let val is_exps_asm_rws = find_lemma_is disch_all pis A0 eqs used_asms d_cons ud_cons inv_names gol suc itevs_lcs teis tyis ityvs exps asm_rw_is asms cons in
      if isSome is_exps_asm_rws then
        let val (tyis, teis, ityvs, itevs, exps, asm_rw_is, used_asms, ud_cons) = valOf is_exps_asm_rws in
          if type_instantiable orelse is_identity_tyis tyis then
            (* Uninstantiated variables in conclusion are quantified.
             * Uninstantiated variables cannot occur free among hypotheses since
             * all antecedent conjuncts must be instantiated in order to be
             * discharged.
             *
             * REWRITE_RULE removes conjuncts that are identity equalities.
             * SIMP_ANT_RULE removes only identity equalities in the antecedent.
             *)
            let fun to_hyp thm = if (is_imp o concl) thm then CONJ_ANT_TO_HYP thm else thm in
            let val simp_ant_only = if simp_conc then REWRITE_RULE [] else SIMP_ANT_RULE in
            let val simplified_thm = (to_hyp o simp_ant_only o (INST_TY_TERM (teis, tyis))) imp in
            (* Adds undischarged conjuncts as to the antecedent after removing
             * all conjuncts of the antecedent into the hypotheses. *)
            let val (refl_neg_eq_thms, discharged_cons, neg_eq_asms_to_remove) = find_neg_eq_asms ud_cons A0 in

            let val thm = GENL itevs (HYPS_IMP_TO_CONJS_IMP_RULE simplified_thm (filter (not_in discharged_cons) ud_cons)) in
            let val (subgoals1, v1) = MAP_EVERY ASSUME_TAC refl_neg_eq_thms (A0, t0) in
            let val ((A1, t1), v1) = (hd subgoals1, fn thm => v1 [thm]) in
            let val (A2, t2, v2) = EXPAND_TAC exps (A1, t1) in
            let val (A3, t3, v3, new_asms) = RW_ASMS_TAC asm_rw_is (A2, t2) in

            let val (subgoals4, v4) = (ASSUME_TAC thm THEN SPLIT_ASM_TAC) (A3, t3) in
            let val asms_to_remove = if remove_used_asms then neg_eq_asms_to_remove @ used_asms @ new_asms else new_asms
                val (A4, t4) = hd subgoals4
                val v4 = fn thm => v4 [thm] in
            let val (A5, t5, v5) = REMOVE_ASMS_TAC asms_to_remove (A4, t4) in
            let val (A6, t6, v6) = REVERSE_UNIQUIFY_FORALLS_TAC qasm_renamings (A5, t5) in
            let val (subgoals7, v7) = SPLIT_ASM_TAC (A6, t6) in
              (subgoals7, v0 o v1 o v2 o v3 o v4 o v5 o v6 o v7)
            end end end end end end end end end end end end end end
          else
            raise (mk_HOL_ERR "helper_tactics" source_tactic "Disallowed type instantiation necessary.")
        end
      else
        raise (mk_HOL_ERR "helper_tactics" source_tactic "Could not discharge antecedent.")
    end end


fun EXPAND_TAC2 exps (A1, t1) =
  let val (A2, t2, v2) = EXPAND_TAC exps (A1, t1) in
    ([(A2, t2)], v2 o hd)
  end

fun RW_ASMS_TAC2 asm_rw_is (A2, t2) =
  let val (A3, t3, v3, new_asms) = RW_ASMS_TAC asm_rw_is (A2, t2) in
    ([(A3, t3)], v3 o hd)
  end




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
  fun ITAC lemma (A, t) =
    let val disch_all = false
        val source_tactic = "ITAC"
        val type_instantiable = true
        val remove_used_asms = false in
      ADD_INST_SUC_TYPE_TAC true disch_all source_tactic type_instantiable remove_used_asms lemma (A, t)
    end

  fun FITAC lemma (A, t) = (* F for forcing all conjuncts to be discharged. *)
    let val disch_all = true
        val source_tactic = "ITAC"
        val type_instantiable = true
        val remove_used_asms = false in
      ADD_INST_SUC_TYPE_TAC true disch_all source_tactic type_instantiable remove_used_asms lemma (A, t)
    end

  fun IRTAC lemma (A, t) =
    let val disch_all = false
        val source_tactic = "IRTAC"
        val type_instantiable = true
        val remove_used_asms = true in
      ADD_INST_SUC_TYPE_TAC true disch_all source_tactic type_instantiable remove_used_asms lemma (A, t)
    end

  fun FIRTAC lemma (A, t) =
    let val disch_all = true
        val source_tactic = "IRTAC"
        val type_instantiable = true
        val remove_used_asms = true in
      ADD_INST_SUC_TYPE_TAC true disch_all source_tactic type_instantiable remove_used_asms lemma (A, t)
    end



  fun SAITAC lemma (A, t) =
    let val disch_all = false
        val source_tactic = "ITAC"
        val type_instantiable = true
        val remove_used_asms = false in
      ADD_INST_SUC_TYPE_TAC false disch_all source_tactic type_instantiable remove_used_asms lemma (A, t)
    end

  fun SAFITAC lemma (A, t) = (* F for forcing all conjuncts to be discharged. *)
    let val disch_all = true
        val source_tactic = "ITAC"
        val type_instantiable = true
        val remove_used_asms = false in
      ADD_INST_SUC_TYPE_TAC false disch_all source_tactic type_instantiable remove_used_asms lemma (A, t)
    end

  fun SAIRTAC lemma (A, t) =
    let val disch_all = false
        val source_tactic = "SAIRTAC"
        val type_instantiable = true
        val remove_used_asms = true in
      ADD_INST_SUC_TYPE_TAC false disch_all source_tactic type_instantiable remove_used_asms lemma (A, t)
    end

  fun SAFIRTAC lemma (A, t) =
    let val disch_all = true
        val source_tactic = "SAFIRTAC"
        val type_instantiable = true
        val remove_used_asms = true in
      ADD_INST_SUC_TYPE_TAC false disch_all source_tactic type_instantiable remove_used_asms lemma (A, t)
    end




  (* A u {!X. C1 /\.../\ Cn ==> C} ?- t
   * ----------------------------------
   *         A u {C} ?- t
   *
   * If Ci are in A or can be derived to be in A by means of equations in A.
   *)
  fun AI_REMOVE_USED_ASMS_TAC invalid_asms disch_all source_tactic remove_used_asms (A, t) =
    let fun is_qimp term =
      if is_forall term then
        ((fn imp => is_imp imp andalso (not o is_neg) imp) o #2 o strip_forall) term
      else
        false in
    let val qimp = List.find (fn asm => is_qimp asm andalso all (not_same_term asm) invalid_asms) A in
      if isSome qimp then
        let val qimp = valOf qimp in
        let val type_instantiable = false
            val lemma = ASSUME qimp in 
        let val (subgoals1, v1) = ADD_INST_SUC_TYPE_TAC true disch_all source_tactic type_instantiable remove_used_asms lemma (A, t) in
        let val (A1, t1) = hd subgoals1 in
        let val A2 = filter (not_same_term qimp) A1
            val t2 = t1 in
          ([(A2, t2)], v1)
        end end end end end
        handle _ =>
          if disch_all then
            AI_REMOVE_USED_ASMS_TAC ((valOf qimp)::invalid_asms) disch_all source_tactic remove_used_asms (A, t)
          else
            raise (mk_HOL_ERR "helper_tactics" source_tactic "Could not discharge all conjuncts in the antecedent of an assumption.")
      else
        let val imp = List.find (fn imp => is_imp imp andalso all (not_same_term imp) invalid_asms andalso List.all (is_in A) ((strip_conj o #1 o dest_imp) imp)) A in
          if isSome imp then
            ADTAC remove_used_asms (A, t)
          else
            raise (mk_HOL_ERR "helper_tactics" source_tactic "Cound not find an implication among the assumptions.")
        end
    end end

  fun AITAC (A, t) =
    let val invalid_asms = []
        val disch_all = false
        val source_tactic = "AITAC"
        val remove_used_asms = false in
      ((AI_REMOVE_USED_ASMS_TAC invalid_asms disch_all source_tactic remove_used_asms) THEN SPLIT_ASM_TAC) (A, t)
    end

  fun FAITAC (A, t) =
    let val invalid_asms = []
        val disch_all = true
        val source_tactic = "FAITAC"
        val remove_used_asms = false in
      ((AI_REMOVE_USED_ASMS_TAC invalid_asms disch_all source_tactic remove_used_asms) THEN SPLIT_ASM_TAC) (A, t)
    end

  fun AIRTAC (A, t) =
    let val invalid_asms = []
        val disch_all = false
        val source_tactic = "AIRTAC"
        val remove_used_asms = true in
      ((AI_REMOVE_USED_ASMS_TAC invalid_asms disch_all source_tactic remove_used_asms) THEN SPLIT_ASM_TAC) (A, t)
    end

  fun FAIRTAC (A, t) =
    let val invalid_asms = []
        val disch_all = true
        val source_tactic = "FAIRTAC"
        val remove_used_asms = true in
      ((AI_REMOVE_USED_ASMS_TAC invalid_asms disch_all source_tactic remove_used_asms) THEN SPLIT_ASM_TAC) (A, t)
    end





(******************************************************************************)
(******************************************************************************)
(******************************************************************************)
(******************************************************************************)
(******************************************************************************)

  fun has_removable_conjunct tyis teis ityvs itevs eqs conjunct [] = NONE
    | has_removable_conjunct tyis teis ityvs itevs eqs conjunct (other::others) =
      case is_meet tyis teis ityvs itevs eqs conjunct other of
        NONE => has_removable_conjunct tyis teis ityvs itevs eqs conjunct others
      | SOME (tyis, teis, ityvs, itevs, template, asm_rws, reflect_other, marks) =>
        SOME (tyis, teis, other,        template, asm_rws, reflect_other, marks)

  fun has_removable_conjuncts tyis teis ityvs itevs eqs others [] = NONE
    | has_removable_conjuncts tyis teis ityvs itevs eqs others (conjunct::conjuncts) =
      case has_removable_conjunct tyis teis ityvs itevs eqs conjunct others of
        NONE => has_removable_conjuncts tyis teis ityvs itevs eqs others conjuncts
      | SOME (tyis, teis, other,        template, asm_rws, reflect_other, marks) =>
        SOME (tyis, teis, other,        template, asm_rws, reflect_other, marks)

  fun is_simplifiable_implication eqs qimp others =
    let val tyis = []
        val teis = []
        val ityvs = []
        val (itevs, imp) = strip_forall qimp
        val conjuncts = (strip_conj o #1 o dest_imp) imp in
      has_removable_conjuncts tyis teis ityvs itevs eqs others conjuncts
    end

  (* Inputs:
   * -eqs: ['l1 = r1', ..., 'ln = rn']
   * -imp_otherss: [(qimp1, [t11, ..., t1m]), ..., (qimpq, [tq1, ..., tqr])]
   *
   * Outputs: If there is a (potentially universally quantified) implication
   * qimpi '!x1...xs. a1 /\ ... /\ at ==> a' that can be instantiated such that
   * an antecedent conjunct ak is equal to a term tij' where tij' is tij but
   * potentially rewritten with the equalities in eqs (both from left to right
   * and right to left), then the output is:
   * SOME (qimp, conjunct, term_substitution, type_substitution,
   *       other, template, mark_unrefl_refl_substitutions, reflect_other):
   * -qimp: '!x1...xs. a1 /\ ... /\ at ==> a'
   * -conjunct: ak that can be made equal to tij'.
   * -term_substitution: How to instantiate the universally quantified variables
   *  of qimp.
   * -type_substitution: How to type instantiate qimp.
   * -other: tij, or if other is an equation and reflect_other is true, then
   *  other must be reflected for conjunct and other to become the same term
   *  under the given substitutions.
   * -template, mark_unrefl_refl_substitutions: How to instantiate tij to become
   *  tij'.
   *)
  fun has_simplifiable_implication eqs [] = NONE
    | has_simplifiable_implication eqs ((qimp, others)::imp_otherss) =
      case is_simplifiable_implication eqs qimp others of
        NONE => has_simplifiable_implication eqs imp_otherss
      | SOME (tyis, teis, other, template, asm_rws, reflect_other, marks) =>
        SOME (qimp, teis, tyis, other, template, asm_rws, reflect_other)

  (* Given a substitution, returns the from terms. *)
  fun term_subst_to_froms [] = []
    | term_subst_to_froms ({redex = from, residue = to}::term_subst) = from::(term_subst_to_froms term_subst)

  (* new_asm, old_asm, [a1, ..., old_asm1, ..., old_asmn, ..., am]
   *                   [a1, ..., new_asm1, ..., new_asmn, ..., am]
   *)
  fun update_asm new_asm old_asm [] = []
    | update_asm new_asm old_asm (asm::asms) =
      let val updated_asms = update_asm new_asm old_asm asms in
        if Term.compare (old_asm, asm) = EQUAL then
          new_asm::updated_asms
        else
          asm::updated_asms
      end

  (*  A u {!x1...xn. P} ?- t
   * ------------------------old_asm = !x1...xn. P, term_subst = [xi |-> vi, .., xj |-> vj], where xi' are uninstantiated.
   * A u {!x1'...xm'. P} ?- t
   *
   * Algorithm:
   * ----------------------------ASSUME
   * {!x1...xn. P} |- !x1...xn. P
   * ----------------------------SPEC_ALL
   * {!x1...xn. P} |- P
   * ------------------------------GENL new_qvars
   * {!x1...xn. P} |- !x1'...xm'. P                  A u {!x1'...xm'. P} |- t
   * ------------------------------------------------------------------------PROVE_HYP
   *                        A u {!x1...xn. P} |- t
   *)
  fun INST_ASM_TAC (term_subst, type_subst) old_asm (old_A, old_t) =
    let val (old_qvars, unq_asm) = strip_forall old_asm
        val ivars = term_subst_to_froms term_subst in
    let val new_qvars = filter (fn qv => not (is_in ivars qv)) old_qvars
        val new_asm_inst = subst term_subst (inst type_subst unq_asm) in
    let val new_asm = list_mk_forall (new_qvars, new_asm_inst) in
    let val new_A = update_asm new_asm old_asm old_A
        val new_t = old_t
        val validation = fn new_thm =>
          (* A u {!x1'...xm'. P} |- t
           * ------------------------
           *  A u {!x1...xn. P} |- t
           *)
          let val old_asm_thm = ASSUME old_asm in
          let val unq_old_asm_thm = SPEC_ALL old_asm_thm in
          let val inst_old_asm_thm = INST_TY_TERM (term_subst, type_subst) unq_old_asm_thm in
          let val quant_inst_asm_thm = GENL new_qvars inst_old_asm_thm in
          let val old_thm = PROVE_HYP quant_inst_asm_thm new_thm in
            old_thm
          end end end end end in
      (new_A, new_t, validation, new_asm)
    end end end end

  (* Returns
   * SOME (rw_term, rw_term_template, mark_unrefl_refl_subst, reflect_rw_term) if
   * it is possible to find a term rw_term in last argument which can be made
   * equal to term_to_meet by rewriting rw_term with equalities in eqs (both from
   * left to right and right to left are considered).
   *
   * The result is rw_term_template[newi/marki] = term_to_meet, where
   * -mark_unrefl_refl_subst = (mark_unrefl, mark_refl)
   * -mark_unrefl: [(marki, oldi |-> newi, oldi = newi)], oldi = newi is in eqs.
   * -mark_refl:   [(marki, oldi |-> newi, oldi = newi)], newi = oldi is in eqs.
   *)
  fun has_meetable_term tyis teis term_to_meet eqs [] = NONE
    | has_meetable_term tyis teis term_to_meet eqs (rw_term::rw_terms) =
      case is_meet tyis teis [] [] eqs term_to_meet rw_term of
        NONE => has_meetable_term tyis teis term_to_meet eqs rw_terms
      | SOME (_, _, _, _, rw_term_template, asm_rws, reflect_rw_term, _) =>
        (* First three components ignored; no variable is instantiatable. *)
        SOME (rw_term, rw_term_template, asm_rws, reflect_rw_term)

  (* A u {t(X), eq1, ..., eqn} ?- t(Y)
   * ---------------------------------
   *                   -
   *
   * If there exists eqi in A such that t[eqi/X] = t(Y), and eqi = 'xi = yi' or
   * eqi = 'yi = xi'.
   *
   * Algorithm:
   * Match assumption to conclusion, if mismatch, see if l->r or r->l equations
   * exist that can rewrite the assumption to become the conclusion, and then
   * solve the goal.
   *)
  fun ASMS_IMP_CON_TAC (A, t) =
    let val (subgoals1, v1) = TRY EQ_PAIR_ASM_TAC (A, t) in
    let val (A1, t1) = hd subgoals1 in
      case has_meetable_term [] [] t1 (filter is_eq A1) A1 of
        NONE => raise (mk_HOL_ERR "helper_tactics" "ASMS_IMP_CON_TAC" "No assumptions can be rewritten by means of other assumptions to produce a new assumption that is the goal.")
      | SOME (asm_to_rw, rw_asm_template, mark_unrefl_refl_subst, reflect_asm) =>
        let val (_, _, v2, new_asm2) = ADD_RW_ASM_REFL_TAC asm_to_rw reflect_asm rw_asm_template mark_unrefl_refl_subst (A1, t1) in
          ([], fn _ => v1 [v2 (ASSUME new_asm2)])
        end
    end end


  (* Attempts to solve a goal by rewriting assumptions and then derive the
   * conclusion from the rewritten assumptions.
   *)
  val STAC =
    FIRST_PROVE [ASM_REWRITE_TAC [],
                 LRTAC THEN ASM_REWRITE_TAC [],
                 RLTAC THEN ASM_REWRITE_TAC [],
                 LRTAC THEN RLTAC THEN ASM_REWRITE_TAC [],
                 RLTAC THEN LRTAC THEN ASM_REWRITE_TAC []]



  fun SOLVE_F_ASM_TAC (A, t) =
    case List.find (same_term F) A of
      NONE => raise (mk_HOL_ERR "helper_tactics" "SOLVE_F_ASM_TAC" "No false assumption.")
    | SOME _ => (MATCH_MP_TAC FALSITY THEN ASMS_IMP_CON_TAC) (A, t);



















  (****************************************************************************)
  (*Start of tactic for rewriting assumptions and conclusion with lemma********)
  (****************************************************************************)

  fun is_match [] subterm = false
    | is_match (lhs::lhss) subterm =
        let val _ = match_term lhs subterm in true end
        handle _ => is_match lhss subterm

  fun substitute_goal_conv lemmas subterm =
    let val lemma =
      case List.find (fn lemma => is_match [(#1 o dest_eq o concl o SPEC_ALL) lemma] subterm) lemmas of
        NONE => fail (print "substitute_goal_conv: Cannot happen.\n")
      | SOME lemma => lemma in
    let val unquantified_lemma = SPEC_ALL lemma in
    let val lhs = (#1 o dest_eq o concl) unquantified_lemma in
    let val matching = match_term lhs subterm in
      INST_TY_TERM matching unquantified_lemma
    end end end end

  fun ETAC_CONJ lemma =
    let val lemmas = CONJUNCTS (SPEC_ALL lemma) in
    let val eq_lemmas = filter (is_eq o concl o SPEC_ALL) lemmas in
    let val lhss = map (#1 o dest_eq o concl o SPEC_ALL) eq_lemmas in
    let val has_matches = has_terms_subterm_property (is_match lhss) in
      SPECIFIC_REWRITE_TACTIC_TEMPLATE
        "helper_tactics" "ETAC" "No subterm of the assumptions nor the conclusion match the left hand side of the lemma.\n"
        has_matches
        (substitute_goal_conv eq_lemmas)
    end end end end

  fun ETAC lemma (A, t) =
    let val (subgoals, v) = (ETAC_CONJ lemma THEN SPLIT_ASM_TAC) (A, t) in
      (subgoals, v)
    end
    handle _ =>
    let val (subgoals, v) = (ETAC_CONJ (GSYM lemma) THEN SPLIT_ASM_TAC) (A, t) in
      (subgoals, v)
    end    

  fun some_lemma_conv eq_lemma instantiatable_variables subterm =
    case find_explicit_variable_instantiation instantiatable_variables ((boolSyntax.lhs o concl) eq_lemma) subterm of
      NONE => NONE
    | SOME instantiation => SOME (INST_TY_TERM instantiation eq_lemma)

  fun have_matching_lemma_rw term [] = NONE
    | have_matching_lemma_rw term ((eq_lemma, instantiatable_variables)::eq_lemma_instantiatable_variables) =
      case some_subterm_rw (some_lemma_conv eq_lemma instantiatable_variables) term of
        NONE => have_matching_lemma_rw term eq_lemma_instantiatable_variables
      | SOME thm => SOME thm

  fun have_terms_subterm_matching_lemma_rw eq_lemma_instantiatable_variables [] = NONE
    | have_terms_subterm_matching_lemma_rw eq_lemma_instantiatable_variables (term::terms) =
      case have_matching_lemma_rw term eq_lemma_instantiatable_variables of
        NONE => have_terms_subterm_matching_lemma_rw eq_lemma_instantiatable_variables terms
      | SOME thm => SOME (term, thm)

  fun SOLVE_T_CON_TAC (A, t) =
    if same_term t T then
      ([], fn thms => boolTheory.TRUTH)
    else
      ALL_TAC (A, t)

  fun LEMMA_COND_CON_TAC tactic_name no_lemma_error_message include_conclusion lemma (A, t) =
    let val instantiatable_variables = (#1 o strip_forall o concl) lemma in
    let val lemmas = CONJUNCTS (SPEC_ALL lemma)
        fun to_eq_lemmas lemma =
          let val lemma_instantiatable_variables = instantiatable_variables @ ((#1 o strip_forall o concl) lemma)
              val unquantified_lemma = SPEC_ALL lemma in
            if (is_eq o concl) unquantified_lemma then (* Makes |- l = r to |- l = r and |- r = l to handle both directions. *)
              [(          unquantified_lemma, lemma_instantiatable_variables)] @
              let val r = (boolSyntax.rhs o concl) unquantified_lemma in (* Prevents F = t and T = t. *)
              let val not_f_or_t_rhs = not (same_term F r orelse same_term T r) in
                if not_f_or_t_rhs then [(SYM unquantified_lemma, lemma_instantiatable_variables)] else []
              end end
            else if (is_neg o concl) lemma then (* Rewrites a lemma of the form !X.~P to P = F *)
              let fun is_t_eq_f_eq_neg_t thm = same_term F ((boolSyntax.rhs o boolSyntax.lhs o concl) thm) in
              let val t_eq_f_eq_neg_t_thm =
                case List.find is_t_eq_f_eq_neg_t ((CONJUNCTS o SPEC_ALL) boolTheory.EQ_CLAUSES) of
                  NONE => raise (mk_HOL_ERR "helper_tactics" tactic_name "boolTheory.EQ_CLAUSES does not contain (t <=> F) <=> ~t")
                | SOME t_eq_f_eq_neg_t_thm => t_eq_f_eq_neg_t_thm in
              let val instantiatable_variable = (boolSyntax.lhs o boolSyntax.lhs o concl) t_eq_f_eq_neg_t_thm in
              let val neg_inst_eq_inst_eq_f_thm = SYM (INST_TY_TERM ([instantiatable_variable |-> (dest_neg o concl) unquantified_lemma], []) t_eq_f_eq_neg_t_thm)
                  val mark = genvar bool in
                [(SUBST [mark |-> neg_inst_eq_inst_eq_f_thm] mark unquantified_lemma, lemma_instantiatable_variables)]
              end end end end
            else
              [(EQT_INTRO unquantified_lemma, lemma_instantiatable_variables)]
          end in
    let val eq_lemma_instantiatable_variables = foldl (fn (lemma, eq_lemmas) => (to_eq_lemmas lemma) @ eq_lemmas) [] lemmas in
      case have_terms_subterm_matching_lemma_rw eq_lemma_instantiatable_variables ((if include_conclusion then [t] else []) @ A) of
        NONE => raise (mk_HOL_ERR "helper_tactics" tactic_name no_lemma_error_message)
      | SOME (rw_term, rw_thm) => ((RW_TERM_TAC rw_term rw_thm) THEN (REPEAT NEG_CONJ_DISJ_IMP_SIMP_TAC) THEN SPLIT_ASM_TAC THEN SOLVE_T_CON_TAC THEN TRY SOLVE_F_ASM_TAC THEN TRY ASMS_IMP_CON_TAC) (A, t)
    end end end

  fun LEMMA_ASM_TAC lemma = LEMMA_COND_CON_TAC "LEMMA_ASM_TAC" "No equational lemma applicable to any assumption." false lemma

  fun LEMMA_TAC lemma = LEMMA_COND_CON_TAC "LEMMA_TAC" "No equational lemma applicable to any assumption nor the conclusion." true lemma

(*
  (*  A u {a1, ..., an} ?- t
   * -----------------------
   * A u {b1, ..., bn} ?- t'
   *
   * lemma: A' |- !X. (!X1. l1 = r1) /\ ... /\ (!Xm. lm = rm), A' subset of A.
   * each ai = lj[Vj/XjX] and bi = rj[Vj/XjX], and
   * t = lj[Vj/XjX] and t' = rj[Vj/XjX] or t = t'.
   *)
  fun LEMMA_EQ_TAC lemma =
    let val lemmas = CONJUNCTS (SPEC_ALL lemma)
        fun to_eq_lemma lemma = if (is_eq o concl o SPEC_ALL) lemma then lemma else (EQT_INTRO o SPEC_ALL) lemma in
    let val rw_lemmas = foldl (fn (lemma, rw_lemmas) => (to_eq_lemma lemma)::rw_lemmas) [] lemmas in
    let fun tactic (A, t) =
      case have_terms_subterm_matching_lemma_rw rw_lemmas (t::A) of
        NONE => raise (mk_HOL_ERR "helper_tactics" "LEMMA_EQ_TAC" "No equational lemma applicable to any assumption nor the conclusion.")
      | SOME (rw_term, rw_thm) =>
        case has_subterm_rw t_disjunct_conv is_t_disj_or_disj_t ((boolSyntax.rhs o concl) rw_thm) of
          NONE => RW_TERM_TAC rw_term rw_thm (A, t)                            (* No subterms of the form: T \/ A, or A \/ T *)
        | SOME rw_thm2 => RW_TERM_TAC rw_term (TRANS rw_thm rw_thm2) (A, t) in (* Remove subterms of the form: T \/ A, or A \/ T *)
      tactic THEN REPEAT tactic
    end end end

  fun LEMMA_TAC lemma =
    LEMMA_EQ_TAC lemma ORELSE
    LEMMA_DISJ_NEG_TAC lemma ORELSE
    FAIL_TAC "No equational or negated lemma applicable to an assumption or the conclusion."
*)
  (****************************************************************************)
  (*End of tactic for rewriting assumptions and conclusion with lemma**********)
  (****************************************************************************)



  (****************************************************************************)
  (*Start of tactic for rewriting assumptions with lemma***********************)
  (****************************************************************************)

  (* True if and only if l can be matched to subterm.
   *)
  fun is_matchable l subterm = let val _ = match_term l subterm in true end handle _ => false

  (* SOME 'A |- old = new', where term = '...old...' and lemma can be
   * instantiated to 'A |- old = new'
   *)
  fun has_applicable_rw_lemma term rw_lemma =
    let val l = (boolSyntax.lhs o concl) rw_lemma in
      case has_subterm_property (is_matchable l) term of
        NONE => NONE
      | SOME (mark, template, subterm_with_property) =>
        let val matching = match_term l subterm_with_property in
          SOME (INST_TY_TERM matching rw_lemma)
        end
    end

  (* SOME 'A |- old = new' if there is a lemma that can be instantiated to
   * 'A |- old = new' such that old occurs as a subterm in term.
   *)
  fun has_applicable_rw_lemmas term [] = NONE
    | has_applicable_rw_lemmas term (rw_lemma::rw_lemmas) =
      case has_applicable_rw_lemma term rw_lemma of
        NONE => has_applicable_rw_lemmas term rw_lemmas
      | SOME rw_thm => SOME rw_thm

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
  fun RW_ASM_LEMMA_TAC asm lemma (A, t) =
    let val lemmas = map SPEC_ALL (CONJUNCTS (SPEC_ALL lemma)) in
    let val rw_lemmas = filter (is_eq o concl) lemmas in
      case has_applicable_rw_lemmas asm rw_lemmas of
        NONE => raise (mk_HOL_ERR "helper_tactics" "RW_ASM_LEMMA_TAC" "Lemma cannot be used to rewrite the given assumption.")
      | SOME rw_lemma =>
        let val (old, new) = (dest_eq o concl) rw_lemma in
        let val asm1 = subst [old |-> new] asm in
        let val A1 = asm1::(filter (fn a => Term.compare (asm, a) <> EQUAL) A)
            val t1 = t in
        let val v1 = fn subgoal_achieving_thm =>
              let val discharged_thm = DISCH asm1 subgoal_achieving_thm
                  val preferred_marker = mk_var ("marker", type_of old) in
              let val marker = gen_variant is_constname "" (free_varsl (t1::A1)) preferred_marker in
              let val template = mk_imp(subst [old |-> marker] asm, t1) in
              let val imp_thm = SUBST [marker |-> SYM rw_lemma] template discharged_thm in
              let val goal_achieving_thm = UNDISCH imp_thm in
                goal_achieving_thm
              end end end end end
            val (subgoals2, v2) = SPLIT_ASM_TAC (A1, t1) in
          (subgoals2, v1 o v2)
        end end end end
    end end

  (* SOME ('...old...', 'B |- old = new') if some rw_lemma can be instantiated to
   * 'B |- old = new', and '...old...' is term.
   *)
  fun has_applicable_terms_rw_lemmas rw_lemmas [] = NONE
    | has_applicable_terms_rw_lemmas rw_lemmas (term::terms) =
      case has_applicable_rw_lemmas term rw_lemmas of
        NONE => has_applicable_terms_rw_lemmas rw_lemmas terms
      | SOME rw_lemma => SOME (term, rw_lemma)

  (* A u {...old...} ?- t
   * --------------------
   * A u {...new...} ?- t
   *
   * lemma is of the form
   * 'B |- !x1...xn. (!y11...y1m. t1) /\ ... /\ (!yp1...ypk. tp)
   * and can be instantiated to 'B |- old = new'.
   *)
  fun RW_HYP_LEMMA_TAC lemma (A, t) =
    let val lemmas = map SPEC_ALL (CONJUNCTS (SPEC_ALL lemma)) in
    let val rw_lemmas = filter (is_eq o concl) lemmas in
      case has_applicable_terms_rw_lemmas rw_lemmas A of
        NONE => raise (mk_HOL_ERR "helper_tactics" "RW_HYP_LEMMA_TAC" "No assumption can be rewritten with the given lemma.")
      | SOME (asm, lemma) => RW_ASM_LEMMA_TAC asm lemma (A, t)
    end end

  fun ASETAC lemma =
    (RW_HYP_LEMMA_TAC lemma) THEN (REPEAT (RW_HYP_LEMMA_TAC lemma))

  (* choose_applications creates a proof tree of the following form:
   *
   * ?xn. r = t v1...vn-1 xn |- ?xn. r = t v1...vn-1 xn                             A u {r = t v1...vn} |- s
   * -------------------------------------------------------------------------------------------------------CHOOSE (vn, ASSUME xtermn)
   *                                  A u {?xn. r = t v1...vn-1 xn} |- s
   *
   *                                               ...
   *
   * ?x2...xn. r = t v1 x2...xn |- ?x2...xn. r = t v1 x2...xn       A u {?x3...xn. r = t v1 v2 x3...xn} |- s
   * -------------------------------------------------------------------------------------------------------CHOOSE (v2, ASSUME xterm2)
   * ?x1...xn. r = t x1...xn |- ?x1...xn. r = t x1...xn                A u {?x2...xn. r = t v1 x2...xn} |- s
   * -------------------------------------------------------------------------------------------------------CHOOSE (v1, ASSUME xterm1)
   *                                   A u {?x1...xn. r = t x1...xn} |- s
   *
   * where choose_applications : inst_var_map -> xterm -> inst_thm -> thm:
   * -inst_var_map: Is of the form [(xn, vn), ..., (x1, v1)] and specifies which
   *  instantiation variable vi shall be substituted by which existentially
   *  quantified variable xi.
   * -xterm: The existentially quantified term that is gradually extended with
   *  an existential variable from inst_var_map and occurring in the left fringe
   *  of the proof tree by application of ASSUME. Is initially r = t v1...vn.
   * -inst_thm: The initial theorem that CHOOSE shall be repetitively applied
   *  on, by adding an existentially quantified formula to the assumptions. Is
   *  initially A u {r = t v1...vn} |- ...r with....
   * -thm: The theorem resulting from the repetitive application of CHOOSE.
   *
   * choose_applications creates the proof tree by starting from the top right
   * leaf, and generating the left fringe by applying ASSUME.
   *
   * The idea behind the definition of choose_applications is:
   * 1. Produce xtermi given xtermi+1 with one additional quantifier by looking
   *    at the head of inst_var_map, (xi, vi):
   *    xtermi = mk_exists (xi, subst [vi |-> xi] xtermi+1),
   *    where the substitution of xi for vi ensures that the instantiation of
   *    the existentially quantified variable is correct.
   * 2. Produce the existential theorem: xthmi = ASSUME xtermi.
   * 3. Produce the theorem for the next iteration: thmi = CHOOSE (vi, xthmi)
   * 4. Get tail of quantifier-variable mapping:
   *    inst_var_mapi = tl inst_var_mapi-1.
   *
   * Each application of CHOOSE is:
   *
   *  extended_xthm       inst_thm
   *  ----------------------------CHOOSE
   *      extended_int_sthm
   *
   * The recursion stops when inst_var_map = [], returning inst_thm.
   *)
  fun choose_applications [] xterm inst_thm = inst_thm
      (* xterm: ?xi+1..xn. P xi+1..xn, inst_thm: A u {?xi-1..xn. P v1..xn}|- t *)
    | choose_applications ((vi, xi)::maps) xterm inst_thm =
        (* The substitution ensures that the existentially quantified variable
         * replaces the instantiated variable. *)
        (* ?xi...xn. P xi...xn *)
        let val extended_xterm = mk_exists (xi, subst [vi |-> xi] xterm) in
        (* ?xi...xn. P xi...xn |- ?xi...xn. P xi...xn*)
        let val extended_xthm = ASSUME extended_xterm in
        let val extended_inst_thm = CHOOSE (vi, extended_xthm) inst_thm in
          choose_applications maps extended_xterm extended_inst_thm
        end end end

  (****************************************************************************)
  (*End of tactic for rewriting assumptions with lemma*************************)
  (****************************************************************************)



  (****************************************************************************)
  (*Start of RECORD tactic*****************************************************)
  (****************************************************************************)

  (*    A u {recordl = recordr} ?- t
   * ----------------------------------, where fi has the name given by field_name.
   * A u {recordl.fi = recordr.fi} ?- t
   *)
  fun ADD_RECORD_ACCESSOR_ASM_TAC field_name (A, t) =
    let fun is_record_eq term = if is_eq term then (TypeBase.is_record_type o type_of o boolSyntax.lhs) term else false in
    let val record_l_rs = map dest_eq (filter is_record_eq (filter is_eq A))
        fun has_field_name record_info = (fst record_info) = field_name in
    let val (l, r) = case List.find (fn (l, r) => exists has_field_name ((TypeBase.fields_of o type_of) l)) record_l_rs of
        NONE => raise (mk_HOL_ERR "helper_tactics" "ADD_RECORD_ACCESSOR_ASM_TAC" "No accessor with given name for record equalities.")
      | SOME (l, r) => (l, r) in
    let val accessor = case List.find has_field_name ((TypeBase.fields_of o type_of) l) of
        NONE => raise (mk_HOL_ERR "helper_tactics" "ADD_RECORD_ACCESSOR_ASM_TAC" "CANNOT HAPPEN!")
      | SOME (name, record_info) => #accessor record_info in
    let val accessor_type = type_of accessor in
    let val argument_type = (hd o #2 o dest_type) accessor_type
        val record_type = type_of l in
    let val type_matching = match_type argument_type record_type in
    let val inst_accessor = inst type_matching accessor in
    let val l_field = mk_comb (inst_accessor, l)
        val r_field = mk_comb (inst_accessor, r) in
    let val l_field_eq_r_field = mk_eq (l_field, r_field) in
    let val A' = l_field_eq_r_field::(filter (fn asm => not (same_term (mk_eq (l, r)) asm)) A)
        val t' = t
        val validation = fn thms =>
          let val subgoal_achieving_thm = hd thms
              val field_accessor_eq_thm = REFL inst_accessor
              val record_eq_thm = ASSUME (mk_eq (l, r)) in
          let val record_field_eq_thm = MK_COMB (field_accessor_eq_thm, record_eq_thm) in
          let val goal_achieving_thm = PROVE_HYP record_field_eq_thm subgoal_achieving_thm in
            goal_achieving_thm
          end end end in
      ([(A', t')], validation)
    end end end end end end end end end end end

  (* Given a term that has record type, returns the names of the fields of that
   * record type according to the names given in the record definition.
   *)
  fun field_names record = map #1 ((TypeBase.fields_of o type_of) record)

 (* Given 'A |- ?x1...xn. t' and ["xname1", ..., "xnamen"]
   * Returns 'A |- ?xname1...xnamen. t[xname1...xnamen/x1...xn]'
   *)
  fun rename_xthm xthm xnames =
    let val (xvars, term) = (strip_exists o concl) xthm in
    let val xvar_xnames = zip xvars xnames in
    let val (new_xvars, matching) = foldl
      (fn ((xv, xn), (nxvs, m)) => let val v = mk_var (xn, type_of xv) in (nxvs @ [v], {redex = xv, residue = v}::m) end)
      ([], [])
      xvar_xnames in
    let val renamed_term = subst matching term in
    let val renamed_xterm = list_mk_exists (new_xvars, renamed_term) in
    let val renamed_hyp_xthm = ASSUME renamed_xterm in
    let val renamed_xthm = PROVE_HYP xthm renamed_hyp_xthm in
      renamed_xthm
    end end end end end end end

  (* Given a term record returns a theorem:
   * |- ?field_name1...field_namen. record = record_type field_name1...field_namen
   *)
  fun record_eq_record_type_xthm record =
    let val nchotomy_thm = (TypeBase.nchotomy_of o type_of) record in
    let val xthm = ISPEC record nchotomy_thm
        val xvar_names = field_names record in
    let val renamed_xthm = rename_xthm xthm xvar_names in
      renamed_xthm
    end end end

  (* True if and only if term is of the form 'record_type v1...vn'.
   *)
  fun is_record_type_fields term =
    if is_comb term andalso (TypeBase.is_record_type o type_of) term then
      let val (record_constructor, field_values) = strip_comb term in
        TypeBase.is_constructor record_constructor
      end
    else
      false

  (* Input: Term record of type <|f1;...;fn|>
   * Output: accessor and update functions of record.
   *)
  fun accessor_updators_of record =
    let val info = (TypeBase.fields_of o type_of) record in
    let val accessor_updators = map (fn (_, {accessor = a, fupd = u, ty = ty}) => (a, u)) info in
      accessor_updators
    end end

  (* True if and only if instance is the same term as other, ignoring type
   * variables.
   *)
  fun is_instance_of instance other =
    (let val _ = match_term other instance in true end handle _ => false) andalso is_const instance andalso is_const other

  (* Given a term record of record type, returns [fi, ..., fj] if record is of
   * the form 'r with <|...; fi := vi; ...; fj := vj; ...|>'.
   *)
  fun withs_of accessor_updators record =
    if is_comb record then
      let val (updator_k_app, updated_record) = dest_comb record in
        if is_comb updator_k_app then
          let val updator = rator updator_k_app in
            if exists (fn (_, u) => is_instance_of updator u) accessor_updators then
              let val (base_record, updators) = withs_of accessor_updators updated_record in
                (base_record, updator::updators)
              end
            else
              (record, [])
          end
        else
          (record, [])
      end
    else
      (record, [])

  (* Input: Term.
   * Output: True if and only if term is of the form
   * '(record with <|...; fi := vi; ...|>).fi', where record is not of the form
   * 'record_type v1...vn'.
   *)
  fun is_record_withs_accessed term =
    if is_comb term then
      let val (accessor, record_withs) = dest_comb term in
        if (TypeBase.is_record_type o type_of) record_withs andalso (not o is_record_type_fields) record_withs then
          let val accessor_updators = accessor_updators_of record_withs in
            case List.find (fn (a, _) => is_instance_of accessor a) accessor_updators of
              NONE => false
            | SOME (_, updator) =>
              let val applied_updators = #2 (withs_of accessor_updators record_withs) in
                exists (fn u => is_instance_of u updator) applied_updators
              end
          end
        else
          false
      end
    else
      false

  (* True if and only if term is of the form
   * 'record with <|fi := vi; ...; fj := vj|>'.
   *)
  fun is_record_with term =
    if is_comb term andalso (TypeBase.is_record_type o type_of) term then
      let val (update_function, record) = (fn (update, arguments) => (update, last arguments)) (strip_comb term) in
        if (TypeBase.is_record_type o type_of) record then
          let val update_functions = map (fn (name, {accessor = a, fupd = f, ty = t}) => f) ((TypeBase.fields_of o type_of) record) in
            exists (fn f => let val _ = match_term f update_function in true end handle _ => false) update_functions
          end
        else
          false
      end
    else
      false

  (* Input: Term of the form 'r with <|fi := vi; ...; fj := vj|>'.
   * Output: Term 'r'.
   *)
  fun record_with_to_record record =
    if is_record_with record then
      (record_with_to_record o rand) record
    else
      record

  (* True if and only if term is of the form 'record.field'.
   *)
  fun is_record_field_access term =
    if is_comb term then
      let val (field_accessor, record) = dest_comb term in
        if (TypeBase.is_record_type o type_of) record then
          let val field_infos = (TypeBase.fields_of o type_of) record in
          let val accessor_functions = map (fn (name, {accessor = a, fupd = fupd, ty = ty}) => a) field_infos in
            exists (fn a => let val _ = match_term a field_accessor in true end handle _ => false) accessor_functions
          end end
        else
          false
      end
    else
      false

  (* True if and only if term is of the form '(record_type f1...fn).fi'.
   *)
  fun is_record_type_fields_access term =
    if is_record_field_access term then
      let val record = (#2 o dest_comb) term in
        is_record_type_fields record
      end
    else
      false

  (* Input: Term.
   * Output: True if and only if term is of the form
   * '(record with <|...; fi := vi; ...|>).fj', where record is not of the form
   * 'record_type v1...vn', nor '(record_type v1...vn).fi'.
   *)
  fun is_record_withs_access term =
    if is_comb term then
      let val (accessor, record_withs) = dest_comb term in
      let val updated_record = record_with_to_record record_withs in
        if (TypeBase.is_record_type o type_of) record_withs andalso
           (not o is_record_type_fields) record_withs andalso
           (not o is_record_type_fields_access) updated_record then (* Prevents '(record_type v1...vn).fi'. *)
          let val accessor_updators = accessor_updators_of record_withs
              val applied_updators = #2 (withs_of accessor_updators record_withs) in
            exists (fn (a, _) => is_instance_of accessor a) accessor_updators andalso
            exists (fn updator => exists (fn (_, u) => is_instance_of updator u) accessor_updators) applied_updators
          end
        else
          false
      end end
    else
      false

  (* True if and only if term is of the form
   * 'record_type v1...vn with <|fi := vi; ...; fj := vj|>', which restricts to only one with.
   *)
  fun is_record_type_fields_withs term =
    is_record_with term andalso (is_record_type_fields o record_with_to_record) term

  (* True if and only if term is of the form
   * 'record_type v1...vn with fi := vi', which restricts to only one with.
   *)
  fun is_record_type_fields_single_with term =
    is_record_with term andalso
    (is_record_type_fields o record_with_to_record) term andalso
    (not o is_record_with o #2 o dest_comb) term

  (* True if and only if term is of the form
   * 'record_type x1...xn', where at least one xi is of the form (K vi fi).
   *)
  fun is_record_type_k_app term =
    if is_comb term then
      let val (record_constructor, fields) = strip_comb term
          fun is_K_app field =
                if is_comb field then
                  let val (k, args) = strip_comb field in
                    (let val _ = match_term “combin$K : 'a -> 'b -> 'a” k in true end handle _ => false) andalso length args = 2
                  end
                else
                  false in
        exists is_K_app fields
      end
    else
      false

  (* Input: 'record_state v1...vn with fi := vi', where there is only one with.
   * Output: '|- record_state v1...vn with fi := vi = record_state v1...(K vi fi)...vn'.
   *)
  fun record_type_fields_single_with_to_k_app_thm record_type_fields_single_with =
    let val update_thms = (TypeBase.updates_of o type_of) record_type_fields_single_with
        fun is_update_eq_thm thm =
          let val _ = match_term ((boolSyntax.lhs o #2 o strip_forall o concl) thm) record_type_fields_single_with in
            true
          end handle _ => false in
    let val update_thm = case List.find is_update_eq_thm update_thms of
        NONE =>
        let val error_message = concat ["Cannot find field update theorem: ", term_to_string record_type_fields_single_with] in
          raise (mk_HOL_ERR "helper_tactics" "record_type_fields_single_with_to_k_app_thm" error_message)
        end
      | SOME update_thm => update_thm
        val (update_function_k_app, record_type_fields) = dest_comb record_type_fields_single_with in
    let val k_app = rand update_function_k_app
        val fields = (#2 o strip_comb) record_type_fields in
    let val record_type_fields_single_with_eq_record_type_fields_k_app_thm = ISPECL (k_app::fields) update_thm in
      record_type_fields_single_with_eq_record_type_fields_k_app_thm
    end end end end

  (* Given: 'record_type v1...vn with <|fi := vi; ...; fj := vj|>'
   * Output:
   * '|- record_type v1...vn with <|fi := vi; ...; fj := vj|>
   *     =
   *     record_type v1...(k vi fi)...(K vj fj)...vn'
   *)
  fun record_type_fields_withs_conv record_type_fields_withs =
    if is_record_type_fields_single_with record_type_fields_withs then
      record_type_fields_single_with_to_k_app_thm record_type_fields_withs
    else
      let val (update_function_k_app, record_type_fields) = dest_comb record_type_fields_withs in
      let val rw_thm = record_type_fields_withs_conv record_type_fields in
      let val record_type_fields = (boolSyntax.rhs o concl) rw_thm
          val record_type_fields_withs_eq_one_less_with_thm = AP_TERM update_function_k_app rw_thm in
      let val record_type_fields_one_less_with = (boolSyntax.rhs o concl) record_type_fields_withs_eq_one_less_with_thm in
      let val record_type_fields_one_less_with_eq_no_withs_thm =
            record_type_fields_single_with_to_k_app_thm record_type_fields_one_less_with in
      let val record_type_fields_k_apps_thm =
            TRANS record_type_fields_withs_eq_one_less_with_thm record_type_fields_one_less_with_eq_no_withs_thm in
        record_type_fields_k_apps_thm
      end end end end end end

  (* Input: 'record_type v1...(K vi fi)...(K vj fj)...vn'
   * Output: '|- record_type v1...(K vi fi)...(K vj fj)...vn = record_type v1...vi...vj...vn'
   *)
  fun record_type_k_app_conv record_type_k_app =
    let val fields = (#2 o strip_comb) record_type_k_app
        fun is_k k = let val _ = match_term “combin$K : 'a -> 'b -> 'a” k in true end handle _ => false in
    let val k_apps = filter (fn f => let val k = (#1 o strip_comb) f in is_k k end) fields in
    let val k_arguments = map (#2 o strip_comb) k_apps in
    let val k_app_thms = map (fn arguments => ISPECL arguments combinTheory.K_THM) k_arguments (* [|- K v f = v, ...] *)
        val record_type_k_app_refl_thm = REFL record_type_k_app (* |- record_type v1...K e v...vn = record_type v1...K e v...vn *)
        fun eq_thm_to_sub thm =
          let val old = (boolSyntax.lhs o concl) thm in
          let val mark = genvar_term old in
            ({redex = mark, residue = thm}, [{redex = old, residue = mark}])
          end end in
    let val (substitution, record_type_k_app_template) = foldl
      (fn (thm, (substitution, template)) => let val (s, t) = eq_thm_to_sub thm in (s::substitution, subst t template) end)
      ([], record_type_k_app)
      k_app_thms in
    let val template = mk_eq (record_type_k_app, record_type_k_app_template) in
    let val thm = SUBST substitution template record_type_k_app_refl_thm in
      thm
    end end end end end end end

  (* Input: '(record_type v1...vn).fi'.
   * Output: '|- (record_type v1...vn).fi = vi'.
   *)
  fun record_type_fields_access_conv record_type_fields_access =
    let val (accessor_function, record_type_fields) = dest_comb record_type_fields_access in
    let val accessor_thms = (TypeBase.accessors_of o type_of) record_type_fields
        fun is_accessor_thm thm =
          let val a = (rator o boolSyntax.lhs o #2 o strip_forall o concl) thm in
          let val _ = match_term a accessor_function in
            true
          end handle _ => false
          end
        val fields = (#2 o strip_comb) record_type_fields in
    let val accessor_thm =
      case List.find is_accessor_thm accessor_thms of
        NONE => raise (mk_HOL_ERR "helper_tactics" "record_type_fields_access_conv" "Input term does not access a record field.")
      | SOME thm => ISPECL fields thm in
      accessor_thm
    end end end

(*  fun has_record_field_access term = has_subterm_property is_record_field_access term*)
(*  fun has_record_primitive terms = has_terms_subterm_property is_record_primitive terms*)

  fun has_record_withs_access terms = has_terms_subterm_property is_record_withs_access terms

  fun has_record_type_fields_withs terms = has_terms_subterm_property is_record_type_fields_withs terms

  fun has_record_type_k_app terms = has_terms_subterm_property is_record_type_k_app terms

  fun has_record_type_fields_access terms = has_terms_subterm_property is_record_type_fields_access terms

  (* Given a term record occurring in t and that is a primitive record,
   * transforms that record term to a term of form 'record_type v1...vn'.
   *
   * A record is primitive if it is of record type, and it is a variable or a
   * function application where the function is not a record constructor, a
   * record field update nor a record field access.
   *
   *        A ?- ...record...
   * --------------------------------
   * A ?- ...(record_type v1...vn)...
   *)
  fun RECORD_TO_RECORD_TYPE_TAC record (A, t) =
    let val record_eq_record_type_fields_xthm = record_eq_record_type_xthm record in
    let val (subgoals1, v1) = ASSUME_TAC record_eq_record_type_fields_xthm (A, t)
        val xeq_asm = concl record_eq_record_type_fields_xthm in
    let val (A2, t2, v2, record_eq_record_type) = REMOVE_XEQ_TAC xeq_asm [] (hd subgoals1) in
    let val (subgoals3, v3) = ASM_RW_OTHERS_TAC false record_eq_record_type (A2, t2) in
    let val (A3, t3) = hd subgoals3 in
      (A3, t3, fn thm => v1 [(v2 o v3) [thm]])
    end end end end end

  (* Step 1: record to record_type.
   *
   * A ?- ...(record1 with <|...; f1i := v1i; ...|>).f1j
   *      ...(recordm with <|...; fmi := vmi; ...|>).fmj...
   * ------------------------------------------------------
   * A ?- ...(record_type1 v11...v1n).f1j
   *      ...(record_typem vm1...vmp).fmj...
   *
   * recordi is not of the form
   * 'record_typei vi1..vin' nor
   * '(record_typei vi1..vin).fij'.
   *)
  val RECORD_WITHS_ACCESS_TO_RECORD_TYPE_TAC =
    let fun tactic (A, t) =
      case has_record_withs_access (t::A) of
        NONE => raise (mk_HOL_ERR "helper_tactics" "RECORD_WITHS_ACCESS_TO_RECORD_TYPE_TAC"
              "No access to updated record field, with updated record not being an applied constructor (record_type v1...vn).")
      | SOME (mark, template, subterm, term) =>
        let val record_withs_accessed = subterm in
        let val (accessor, record_withs) = dest_comb record_withs_accessed in
        let val updated_record = record_with_to_record record_withs in
        let val (A', t', v') = RECORD_TO_RECORD_TYPE_TAC updated_record (A, t) in
          ([(A', t')], v' o hd)
        end end end end in
      tactic (*THEN (REPEAT tactic)*)
    end

  (* Step 2: Remove withs from record_type.
   *
   * A ?- ...(record_type1 v11...v1n with <|f1i := v1i; ...; f1j := v1j|>)
   *      ...(record_typem vm1...vmp with <|fmk := vmk; ...; fml := vml|>)...
   * ------------------------------------------------------------------------
   * A ?- ...(record_type1 v11...(K v1i f1i)...(K v1j f1j)...v1n)
   *      ...(record_typem vm1...(K vmk fmk)...(K vml fml)...vmp)...
   *)
  val RECORD_TYPE_WITH_TO_RECORD_TYPE_K_APPS_TAC =
    let fun tactic (A, t) =
      case has_record_type_fields_withs (t::A) of
        NONE => raise (mk_HOL_ERR "helper_tactics" "RECORD_TYPE_WITH_TO_RECORD_TYPE_K_APPS_TAC" "No record fields are updated.")
      | SOME (mark, template, subterm, term) =>
        let val record_type_fields_withs = subterm in
        let val rw_thm = record_type_fields_withs_conv record_type_fields_withs in
(*          SUBST_TAC [rw_thm] (A, t)*)
          ETAC rw_thm (A, t)
        end end in
      tactic (*THEN (REPEAT tactic)*)
    end

  (* Step 3: Remove K applications in record_type.
   *
   * A ?- ...(record_type1 v11...(K v1i f1i)...(K v1j f1j)...v1n)
   *      ...(record_typem vm1...(K vmk fmk)...(K vml fml)...vmp)...
   * ---------------------------------------------------------------
   * A ?- ...(record_type1 v11...v1i...v1j...v1n)
   *      ...(record_typem vm1...vmk...vml...vmp)...
   *)
  val RECORD_TYPE_K_APPS_TO_RECORD_TYPE_FIELDS_TAC =
    let fun tactic (A, t) =
      case has_record_type_k_app (t::A) of
        NONE => raise (mk_HOL_ERR "helper_tactics" "RECORD_TYPE_K_APPS_TO_RECORD_TYPE_FIELDS_TAC" "No record field applies K.")
      | SOME (mark, template, subterm, term) =>
        let val record_type_k_app = subterm in
        let val rw_thm = record_type_k_app_conv record_type_k_app in
(*          SUBST_TAC [rw_thm] (A, t)*)
          ETAC rw_thm (A, t)
        end end in
      tactic (*THEN (REPEAT tactic)*)
    end

  (* Step 4: Extract field from record type field access.
   *
   * A ?- ...(record_type1 v11...v1i...v1j...v1n).f1i...(record_typem vm1...vmk...vml...vmp).fmk
   * -------------------------------------------------------------------------------------------
   *                                      A ?- ...v1i...vmk...
   *)
  val RECORD_TYPE_FIELD_ACCESS_TO_VALUE_TAC =
    let fun tactic (A, t) =
      case has_record_type_fields_access (t::A) of
        NONE => raise (mk_HOL_ERR "helper_tactics" "RECORD_TYPE_FIELD_ACCESS_TO_VALUE_TAC" "No field access on record constructor.")
      | SOME (mark, template, subterm, term) =>
        let val record_type_fields_access = subterm in
        let val rw_thm = record_type_fields_access_conv record_type_fields_access in
(*          SUBST_TAC [rw_thm] (A, t)*)
          ETAC rw_thm (A, t)
        end end in
      tactic (*THEN (REPEAT tactic)*)
    end

  (* Splits up and simplifies all records, record field accesses, and record
   * field updates, in the conclusion.
   *
   * Algorithm:
   * 1. Rewrite 'record' to 'record_type v1...vn'.
   * 2. Rewrite '(record_type v1...vn) with <|fi := vi; ...; fj := vj|>' to
   *    'record_type v1...(K vi fi)...(K vj fj)...vn'.
   * 3. Rewrite 'record_type v1...(K vi fi)...(K vj fj)...vn' to
   *    'record_type v1...vi...vj...vn'.
   * 4. Rewrite '(record_type v1...vi...vj...vn).fk' to 'vk'.
   * 5. Repeat any of steps 1-4 as long as there exists a record which can be
   *    simplified (split up into smaller parts, where 'record_type v1...vn' is
   *    the atomic structure).
   *)
  val RECORD_TAC = REPEAT (CHANGED_TAC (
    TRY RECORD_WITHS_ACCESS_TO_RECORD_TYPE_TAC THEN
    TRY RECORD_TYPE_WITH_TO_RECORD_TYPE_K_APPS_TAC THEN
    TRY RECORD_TYPE_K_APPS_TO_RECORD_TYPE_FIELDS_TAC THEN
    TRY RECORD_TYPE_FIELD_ACCESS_TO_VALUE_TAC))


  (****************************************************************************)
  (*End of Record tactic*******************************************************)
  (****************************************************************************)



  (****************************************************************************)
  (*Start of unfolding function definition tactic******************************)
  (****************************************************************************)

  (* Input:
   * -A function name "function_name".
   * -A term term.
   *
   * Output:
   * -False: term is not of the form '<function_name> b1...bn', or is not applied
   *  on all arguments.
   * -True: term is of the form '<function_name> b1...bn', and is applied on all
   *  arguments (that is the function has n arguments).
   *)
  fun is_specified_function_application function_name term =
    if is_comb term then
      let val (function, arguments) = strip_comb term in
      let val function_is_constant = is_const function
          val names_match = function_name = term_to_string function
(*          val all_arguments_applied = (#1 o dest_type o type_of) term <> "fun"*) in (* Some functions return functions. *)
        function_is_constant andalso names_match (*andalso all_arguments_applied*)
      end end
    else
      false

  (* Input:
   * -function_application of the form 'function_name' with n arguments.
   * -A list of terms.
   *
   * Output:
   * -NONE: There is no subterm in terms of the form 'function_name b1...bn'.
   * -SOME subterm: There is a subterm in terms of the form 'function_name b1...bn'.
   *)
  fun has_specified_function_application function_name =
    has_terms_subterm_property (is_specified_function_application function_name)

  (* Input:
   * -A term function_application of the form 'function_name a1...an'.
   *
   * Output:
   * -A theorem of the form
   *  '|- function_name a1...an = function_body[a1...an/x1...xn]'.
   *)
  fun function_application_conv function_application_term =
    let val function = (#1 o strip_comb) function_application_term in
    let val theory_name = #Thy (dest_thy_const function) in
    let val definition_thms = flatten (map (CONJUNCTS o #2) (DB.definitions theory_name)) (* Try definitions first. *)
        fun find_definition_match thm = match_term ((boolSyntax.lhs o #2 o strip_forall o concl) thm) function_application_term in
    let fun is_definition_thm thm = let val _ = find_definition_match thm in true end handle _ => false in
    let val instantiated_thm = case List.find is_definition_thm definition_thms of
        NONE => (* Try theorems second. *)
        let val thms = flatten (map (CONJUNCTS o #2) (DB.theorems theory_name)) in
          case List.find is_definition_thm thms of
            NONE => raise (mk_HOL_ERR "helper_tactics" "function_application_conv" "No applicable definition theorem found: If the function is defined by pattern matching, expand an argument.\n")
          | SOME thm => INST_TY_TERM (find_definition_match thm) (SPEC_ALL thm)
        end
      | SOME thm => INST_TY_TERM (find_definition_match thm) (SPEC_ALL thm) in
      instantiated_thm
    end end end end end

  fun has_string_specified_function_application function_name [] = NONE
    | has_string_specified_function_application function_name (term::terms) =
      if String.isSubstring function_name (term_to_string term) then
        case has_subterm_property (is_specified_function_application function_name) term of
          NONE => has_string_specified_function_application function_name terms
        | SOME (mark, template, subterm_with_property) => SOME (mark, template, subterm_with_property, term)
      else
        has_string_specified_function_application function_name terms

  fun UNFOLD_FUN_TAC function_name =
    SPECIFIC_REWRITE_TACTIC_TEMPLATE
      "helper_tactics" "UNFOLD_FUN_TAC" "No application of a function with the given name."
      (has_string_specified_function_application function_name) function_application_conv (* Checks if the function occurs via text substring function for optimization. *)

  (****************************************************************************)
  (*End of unfolding function definition tactic********************************)
  (****************************************************************************)









  (****************************************************************************)
  (*Start of equality transitive simplification among assumptions tactic*******)
  (****************************************************************************)

  fun is_transitive_equal left right =
    if is_eq left andalso is_eq right then
      let val (lhs1, rhs1) = dest_eq left
          val (lhs2, rhs2) = dest_eq right in
        Term.compare (rhs1, lhs2) = EQUAL
      end
    else
      false

  fun is_transitive_equals term1 [] = NONE
    | is_transitive_equals term1 (term2::term2s) =
        if is_transitive_equal term1 term2 then
          SOME (term1, term2)
        else if is_transitive_equal term2 term1 then
          SOME (term2, term1)
        else
          is_transitive_equals term1 term2s

  fun has_transitive_equals [] = NONE
    | has_transitive_equals (term::terms) =
        case is_transitive_equals term terms of
          NONE => has_transitive_equals terms
        | SOME (left, right) => SOME (left, right)

  (* A u {lhs1 = rhs1, lhs2 = rhs2} |- t ==> A u {lhs1 = rhs2} |- t *)
  fun EQ_TRANS_ASM_TAC (A, t) =
    case has_transitive_equals A of
      NONE => raise (mk_HOL_ERR "helper_tactics" "EQ_TRANS_ASM_TAC" "No equalities to merge.\n")
    | SOME (left_eq, right_eq) =>
        let val new_eq = mk_eq ((#1 o dest_eq) left_eq, (#2 o dest_eq) right_eq)
            val A_without_eqs = filter
              (fn term => Term.compare (term, left_eq ) <> EQUAL andalso
                          Term.compare (term, right_eq) <> EQUAL) A in
        let val subgoals = [(new_eq::A_without_eqs, t)]
            val validation_function = fn thms =>
              let val subgoal_achieving_thm = hd thms
                  val left_right_lhs_rhs_thm = TRANS (ASSUME left_eq) (ASSUME (right_eq)) in
              let val A_left_right_eqs_lhs_rhs_thm = foldl
                    (fn (a, thm) => ADD_ASSUM a thm) left_right_lhs_rhs_thm A_without_eqs in
              let val goal_achieving_thm =
                  PROVE_HYP A_left_right_eqs_lhs_rhs_thm subgoal_achieving_thm in
                goal_achieving_thm
              end end end in
          (subgoals, validation_function)
        end end

  (****************************************************************************)
  (*End of equality transitive simplification among assumptions tactic*********)
  (****************************************************************************)



  (****************************************************************************)
  (*Start of equality reflection of assumption whose right hand side occurs in*)
  (*the conclusion of the goal.************************************************)
  (****************************************************************************)

  fun has_rhs rhs term =
    if Term.compare (rhs, term) = EQUAL then
      true
    else if is_var term orelse is_const term then
      false
    else if is_comb term then
      let val (function, argument) = dest_comb term in
        if has_rhs rhs argument then
          true
        else
          has_rhs rhs function
      end
    else (* is_abs term*)
      ((has_rhs rhs) o #2 o dest_abs) term

  fun REFL_ASM_IN_GOAL_TAC (A, t) =
    let val eqs = filter is_eq A
        fun find_eq_to_reflect [] = raise (mk_HOL_ERR "helper_tactics" "REFL_ASM_IN_GOAL_TAC" "No equality among assumptions whose right hand side occurs in the conclusion of the goal.\n")
          | find_eq_to_reflect (eq::eqs) =
              if has_rhs ((#2 o dest_eq) eq) t  then
                eq
              else
                find_eq_to_reflect eqs in
    let val eq_to_reflect = find_eq_to_reflect eqs in
      REFL_ASM_TAC eq_to_reflect (A, t)
    end end

  (****************************************************************************)
  (*End of equality reflection of assumption whose right hand side occurs in***)
  (*the conclusion of the goal.************************************************)
  (****************************************************************************)



  (****************************************************************************)
  (*Start of tactic that reflects all equalities among the assumptions that****)
  (*have variables on both sides and where the right hand side variables are***)
  (*primed.********************************************************************)
  (****************************************************************************)

  (* '{l1 = r1', ... ln = rn'} u A ?- t'
   * ==>
   * '{r1' = l1, ... rn' = ln} u A ?- t'
   *)
  fun REFL_PRIMED_RHS_ASMS_TAC (A, t) =
    let val eqs = filter is_eq A in
    let val var_eqs = filter (fn eq => (is_var o boolSyntax.lhs) eq andalso (is_var o boolSyntax.rhs) eq) eqs in
    let val primed_rhs_eqs = filter (fn eq => (last o explode o term_to_string o boolSyntax.rhs) eq = #"'") var_eqs in
      if null primed_rhs_eqs then
        raise (mk_HOL_ERR "helper_tactics" "ASM_VAR_EQ_RW_ASMS_TAC" "No equality with variables on both sides with the right hand side being primed exists to rewrite another assumption.\n")
      else
        let fun REFLECT_EQS_TAC [] = ALL_TAC
              | REFLECT_EQS_TAC (eq::eqs) = (REFL_ASM_TAC eq) THEN (REFLECT_EQS_TAC eqs) in
          REFLECT_EQS_TAC primed_rhs_eqs (A, t)
        end
    end end end

  (****************************************************************************)
  (*Start of tactic that reflects all equalities among the assumptions that****)
  (*have variables on both sides and where the right hand side variables are***)
  (*primed.********************************************************************)
  (****************************************************************************)


  (* A u {l = functiona0_ai-1 ai...an} ?- t
   * --------------------------------------
   * A u {functiona0_ai-1 ai...an = l} ?- t
   *)
  fun REFL_EQ_FUN_ASM_TAC function_string (A, t) =
    let fun is_prefix term =
      if function_string = term_to_string term then
        true
      else if is_comb term then
          (is_prefix o rator) term
      else
        false in
    let val eqs = filter is_eq A in
      case List.find (fn eq => let val (l, r) = dest_eq eq in is_prefix l orelse is_prefix r end) eqs of
        NONE => raise (mk_HOL_ERR "helper_tactics" "REFL_EQ_FUN_ASM_TAC" "String does not match a prefix of a function application.")
      | SOME eq => REFL_ASM_TAC eq (A, t)
    end end



  (* A u {l = r} ?- t
   * ----------------substring is a substring of "l = r"
   * A u {r = l} ?- t
   *)
  fun REFL_SUBSTRING_TAC substring (A, t) =
    case List.find (fn a => String.isSubstring substring (term_to_string a)) A of
      NONE => raise (mk_HOL_ERR "helper_tactics" "REFL_SUBSTRING_TAC" "No assumption containing the given substring.")
    | SOME assumption_to_reflect => REFL_ASM_TAC assumption_to_reflect (A, t)






  (****************************************************************************)
  (*Start of tactic that removes an equality assumption and substitutes its****)
  (*right hand side for its left hand side in another assumption.**************)
  (****************************************************************************)

  (* 'A u {lhs = rhs, ...lhs...} ?- t'
   * ==>
   * 'A u {...rhs...} ?- t'
   *)
  fun ASM_EQ_RW_ASM_TAC (A, t) =
    let val eqs = filter is_eq A in
    let val As = map (fn eq => filter (fn ass => Term.compare (eq, ass) <> EQUAL) A) eqs (* [(eq1, A - {eq1})...], eqi in A *)
        fun has_lhs_in_assumption [] = NONE
          | has_lhs_in_assumption ((eq, asss)::eq_assss) =
              case has_subterms ((#1 o dest_eq) eq) asss of
                NONE => has_lhs_in_assumption eq_assss
              | SOME ass => SOME (eq, ass) in
      case has_lhs_in_assumption (zip eqs As) of
        NONE => raise (mk_HOL_ERR "helper_tactics" "ASM_EQ_RW_ASM_TAC"
                                  "No equation among the assumptions with a left hand side that occurs in another assumptions.")
      | SOME (eq, ass) => (RM_ASM_RW_ASM_TAC eq ass) (A, t)
    end end

  (* 'A u {lhs = rhs, ...lhs...} ?- t'
   * ==>
   * 'A u {lhs = rhs,...rhs...} ?- t'
   *)
  fun KEEP_ASM_EQ_RW_ASM_TAC (A, t) =
    let val eqs = filter is_eq A in
    let val As = map (fn eq => filter (fn ass => Term.compare (eq, ass) <> EQUAL) A) eqs (* [(eq1, A-{eq1})...], where each eqi ∈ A.*)
        fun has_lhs_in_assumption [] = NONE
          | has_lhs_in_assumption ((eq, asss)::eq_assss) =
              case has_subterms ((#1 o dest_eq) eq) asss of
                NONE => has_lhs_in_assumption eq_assss
              | SOME ass => SOME (eq, ass) in
      case has_lhs_in_assumption (zip eqs As) of
        NONE => raise (mk_HOL_ERR "helper_tactics" "KEEP_ASM_EQ_RW_ASM_TAC"
                                  "No equation among the assumptions with a left hand side that occurs in another assumptions.")
      | SOME (eq, ass) => (KEEP_ASM_RW_ASM_TAC eq ass) (A, t)
    end end

  (* 'A u {l1=r1...ln=rn} u {...l1...ln} ?- t'
   * ==>
   * 'A u {...r1...rn} ?- t[ri/li]'
   *
   * 1. Fix an equation. If there is no assumption or conclusion containing the left hand side of the equation, fail.
   * 2. As long as there is an assumption containing its left hand side, rewrite that assumption.
   * 3. If the conclusion contains the left hand side, rewrite the conclusion.
   * 4. Remove the equation.
   * 5. Repeat 1-4.
   *)
  val RM_ASM_EQS_RW_TAC =
    let fun tactic (A, t) = 
      let val eqs = filter is_eq A
          fun other_assumptions other = filter (fn a => Term.compare (other, a) <> EQUAL) A in
      let val eq_other_assumptionss = map (fn eq => (eq, other_assumptions eq)) eqs
          fun is_subterm_of_terms subterm terms = filter (is_subterm subterm) terms in
      let val eq_in_other_assumptions = map (fn (eq, os) => (eq, is_subterm_of_terms (boolSyntax.lhs eq) os)) eq_other_assumptionss in
      let val (eq, not_empty_in_other_assumptions) =
        case List.find (fn (eq, others) => (not o null) others orelse is_subterm (boolSyntax.lhs eq) t) eq_in_other_assumptions of
          NONE => raise (mk_HOL_ERR "helper_tactics" "RM_ASM_EQS_RW_TAC"
            "No equation among the assumptions with a left hand side that occurs in another assumptions or the conclusion.\n")
        | SOME eq_others => eq_others in
      let val REMOVE_EQ_TAC = WEAKEN_TAC (fn a => Term.compare (a, eq) = EQUAL) (* Remove equality. *)
          val RW_GOAL_TAC = SUBST_TAC [ASSUME eq] in                            (* Rewrite conclusion. *)
      let fun ASM_RW_ASMS_TAC [] = RW_GOAL_TAC THEN REMOVE_EQ_TAC
            | ASM_RW_ASMS_TAC (ass::asss) = (KEEP_ASM_RW_ASM_TAC eq ass) THEN (ASM_RW_ASMS_TAC asss) in
        ASM_RW_ASMS_TAC not_empty_in_other_assumptions (A, t)
      end end end end end end in
      tactic THEN REPEAT tactic
    end

  (****************************************************************************)
  (*End of tactic that removes an equality assumption and substitutes its******)
  (*right hand side for its left hand side in another assumption.**************)
  (****************************************************************************)


  (* A u {lhs = rhs} u {...rhs...} ?- t
   * ----------------------------------
   *       A u {...lhs...} ?- t
   *)
  fun ASM_RHS_RW_ASM_TAC (A, t) =
    let val eqs = filter is_eq A in
    let fun is_same t1 t2 = Term.compare (t1, t2) = EQUAL in
    let fun not_same t1 t2 = not (is_same t1 t2) in
    let val eq_paired_other_assumptions = map (fn eq => (eq, filter (not_same eq) A)) eqs in
    let val eq_other_assumptions = flatten (map (fn (eq, asms) => map (fn a => (eq, a)) asms) eq_paired_other_assumptions) in
      case List.find (fn (eq, a) => is_subterm (boolSyntax.rhs eq) a) eq_other_assumptions of
        NONE =>
        raise (mk_HOL_ERR "helper_tactics" "ASM_RHS_RW_ASM_TAC"
                          "No equation among the assumptions with a right hand side that occurs in another assumption.")
      | SOME (eq, assumption_to_rewrite) =>
        let val (subgoals1, validation1) = REFL_ASM_TAC eq (A, t)
            val (l, r) = dest_eq eq in
        let val reflected_eq = mk_eq (r, l) in
        let val (subgoals2, validation2) = RM_ASM_RW_ASM_TAC reflected_eq assumption_to_rewrite (hd subgoals1) in
          (subgoals2, fn thms => validation1 [validation2 thms])
        end end end
    end end end end end

  (* A u {lhs = rhs} u {...lhs..., ..., ...lhs...} ?- t
   * --------------------------------------------------
   *      A u {...rhs..., ..., ...rhs...} ?- t
   *)
  fun ASM_RHS_RW_ASMS_TAC (A, t) =
    let val eqs = filter is_eq A in
    let fun rhs_occurs_in eq t = is_subterm (boolSyntax.rhs eq) t in
    let val eq_paired_other_assumptions = map (fn eq => (eq, filter (fn a => not_same_term eq a andalso rhs_occurs_in eq a) A)) eqs in
    let val eq_not_empty_other_assumptions = filter (fn (eq, others) => (not o null) others) eq_paired_other_assumptions in
      if null eq_not_empty_other_assumptions then
        raise (mk_HOL_ERR "helper_tactics" "ASM_RHS_RW_ASMS_TAC"
                          "No equation among the assumptions with a right hand side that occurs in another assumption.")
      else
        let val (eq, others) = hd eq_not_empty_other_assumptions in
        let val (subgoals1, validation1) = REFL_ASM_TAC eq (A, t)
            val (l, r) = dest_eq eq in
        let val rw_eq = mk_eq (r, l)
            fun tactic [] (A, t) = ([(filter (not_same_term rw_eq) A, t)], fn thms => hd thms) (* Remove assumption used for rewrite. *)
              | tactic (to_rw::to_rws) (A, t) =
                let val (subgoals1, validation1) = KEEP_ASM_RW_ASM_TAC rw_eq to_rw (A, t) in
                let val (subgoals2, validation2) = tactic to_rws (hd subgoals1) in
                  (subgoals2, fn thms => validation1 [validation2 thms])
                end end in
        let val (subgoals2, validation2) = tactic others (hd subgoals1) in
          (subgoals2, fn thms => validation1 [validation2 thms])
        end end end end
    end end end end


  (****************************************************************************)
  (*Start of tactic that uses all equations with with variables on both sides**)
  (*among the assumptions and for which there is another assumption with their*)
  (*left hand side in, to rewrite the latter and remove the former equations.**)
  (****************************************************************************)

  (* '{var1 = var2, ..., var(n-1) = varn} u {...var1..., ..., ...var(n-1)...} u A ?- t'
   * ==>
   * '{...var2..., ..., ...varn...} u A ?- t'
   *)
  val ASM_VAR_EQ_RW_ASMS_TAC =
    let fun tactic (A, t) = 
      let val eqs = filter is_eq A in
      let val var_eqs = filter (fn eq => let val (l, r) = dest_eq eq in is_var l andalso is_var r end) eqs
          fun other_assumptions other = filter (fn a => Term.compare (other, a) <> EQUAL) A in
      let val var_eqs_other_assumptions = map (fn eq => (eq, other_assumptions eq)) var_eqs
          fun is_in var terms = filter (var_occurs var) terms in
      let val eqs_lhs_other_assumptions = map (fn (eq, os) => (eq, is_in (boolSyntax.lhs eq) os)) var_eqs_other_assumptions in
      let val (eq, not_empty_other_assumptions) =
        case List.find (fn (eq, others) => (not o null) others) eqs_lhs_other_assumptions of
          NONE => raise (mk_HOL_ERR "helper_tactics" "ASM_VAR_EQ_RW_ASMS_TAC"
            "No equality with variables on both sides exists such that another assumption contains the left hand side variable.")
        | SOME eq_others => eq_others in
      let val REMOVE_EQ_TAC = WEAKEN_TAC (fn a => Term.compare (a, eq) = EQUAL) (* Remove equality. *)
          val RW_GOAL_TAC = SUBST_TAC [ASSUME eq] in                            (* Rewrite conclusion. *)
      let fun ASM_RW_ASMS_TAC [] = RW_GOAL_TAC THEN REMOVE_EQ_TAC
            | ASM_RW_ASMS_TAC (ass::asss) = (KEEP_ASM_RW_ASM_TAC eq ass) THEN (ASM_RW_ASMS_TAC asss) in
        ASM_RW_ASMS_TAC not_empty_other_assumptions (A, t)
      end end end end end end end in
      tactic THEN REPEAT tactic
    end

  (****************************************************************************)
  (*End of tactic that uses all equations with with variables on both sides**)
  (*among the assumptions and for which there is another assumption with their*)
  (*left hand side in, to rewrite the latter and remove the former equations.**)
  (****************************************************************************)



  (****************************************************************************)
  (*Start of tactic that removes an assumption and uses it to rewrite an*******)
  (*assumption that is a universally quantified implication.*******************)
  (****************************************************************************)

  (* Returns SOME [...(f, t)...] if and only if it is possible to match the term
   * from to the term to via the matching [...(f, t)...]
   *)
  fun find_matching from to =
    if Type.compare (type_of from, type_of to) <> EQUAL then
      NONE
    else if is_var from then
      SOME [{redex = from, residue = to}]
    else if is_const from andalso is_const to then
      if Term.compare (from, to) = EQUAL then
        SOME []
      else
        NONE
    else if is_comb from andalso is_comb to then
      let val (function_from, argument_from) = dest_comb from
          val (function_to, argument_to) = dest_comb to in
        case (find_matching function_from function_to, find_matching argument_from argument_to) of
          (_, NONE) => NONE
        | (NONE, _) => NONE
        | (SOME function_matching, SOME argument_matching) => merge_term_matchings function_matching argument_matching
      end
    else if is_abs from andalso is_abs to then
      let val (var_from, body_from) = dest_abs from
          val (var_to, body_to) = dest_abs to in
        case find_matching body_from body_to of
          NONE => NONE
        | SOME matching => (
            case filter (fn {redex = v1, residue = v2} => same_term var_from v1 orelse same_term var_to v2) matching of
              [] => SOME matching (* Neither bounded variable occurs in their respective bodies. *)
            | bound_matching =>
                (* Bounded variables occur at same positions. *)
                if all (fn {redex = f, residue = t} => same_term var_from f andalso same_term var_to t) bound_matching then
                  (* Remove bounded variables from matching. *)
                  SOME (filter (fn {redex = f, residue = t} => not_same_term var_from f andalso not_same_term var_to t) matching)
                else
                  NONE)
      end
    else (* Structure not matching of from and to. *)
      NONE

  (* SOME [...(fi, ti)...] if and only if it is possible to match a subterm of
   * term to subterm to via the matching [...(fi, ti)...], where each fi si in
   * matchable_variables.
   *)
  fun has_subterm_matchable_match matchable_variables term subterm =
    let fun has_subterm_match_rec matchable_variables term subterm =
      case find_matching term subterm of
        NONE => traverse_term matchable_variables term subterm
      | SOME matching =>
          (* All matched variables must be matchable, or that they are unchanged (matched to themselves). *)
          if all (fn {redex = from, residue = to} => exists (same_term from) matchable_variables orelse same_term from to) matching then
            SOME matching
          else
            traverse_term matchable_variables term subterm
        and traverse_term matchable_variables term subterm =
          if is_var term orelse is_const term then
            NONE
          else if is_comb term then
            if is_forall term then (* Removes x in !x. P from matchable variables, to not instantiate unwanted variables. *)
              let val (qv, body) = dest_forall term in
              let val matchable_variables = filter (not_same_term qv) matchable_variables in
                has_subterm_match_rec matchable_variables body subterm
              end end
            else if is_exists term then (* Removes x in ?x. P from matchable variables, to not instantiate of unwanted variables. *)
              let val (qv, body) = dest_exists term in
              let val matchable_variables = filter (not_same_term qv) matchable_variables in
                has_subterm_match_rec matchable_variables body subterm
              end end
            else
              let val (function, argument) = dest_comb term in
                case has_subterm_match_rec matchable_variables function subterm of
                  NONE => has_subterm_match_rec matchable_variables argument subterm
                | SOME matching => SOME matching
              end
          else (* is_abs term *)
            let val (variable, body) = dest_abs term in
              has_subterm_match_rec (filter (same_term variable) matchable_variables) ((#2 o dest_abs) term) subterm
            end in
      has_subterm_match_rec matchable_variables term subterm
    end

  (* Inputs:
   * -A term subformula of type boolean.
   * -Terms formulas of type boolean.
   *
   * Outputs: Some (formula, matching) if and only if the universally quantified
   * variables of formula can be instantiated as specified by matching such that
   * subformula appears as a subformula in the instantiation of formula, where
   * formula occurs in formulas.
   *)
  fun has_formulas_subformula subformula [] = NONE
    | has_formulas_subformula subformula (formula::formulas) =
        let val (matchable_variables, formula_body) = strip_forall formula in
          case has_subterm_matchable_match matchable_variables formula_body subformula of
            NONE => has_formulas_subformula subformula formulas
          | SOME matching => SOME (formula, matching)
        end

  (* Input: A list of pairs (subformula, formulas).
   *
   * Output: SOME (subformula, formula, matching) if and only if formula can be
   * instantiated with matching such that subformula appears in formula as a
   * subformula, where formula occurs in the second component of the pair in
   * which subformula occurs in.
   *)
  fun find_formula_subformula_instantiation [] = NONE
    | find_formula_subformula_instantiation ((subformula, formulas)::subformula_formulass) =
        case has_formulas_subformula subformula formulas of
          NONE => find_formula_subformula_instantiation subformula_formulass
        | SOME (formula, matching) => SOME (subformula, formula, matching)

  (* Inputs:
   * -A subformula of type boolean.
   * -A formula of type boolean.
   * -A list matching of pairs of variables for which the variable of first
   *  component should be replaced by the term of the second component in
   *  formula, leading subformula to be a subformula of formula.
   *
   * Output:
   * [subformula, formula] |- !X'. unquantified_formula[matching/(X-{X'})],
   * where unquantified_formula is:
   * -formula but with the leading universal quantification of X (list of
   *  variables), and where X-{X'} are instantiated by matching and X' are
   *  uninstantiated by matching.
   * -simplified, by for instance removing subformula from assumptions of formula
   *  if formula is an implication.
   *)
  fun INST_FORALL_RULE subformula formula term_matching =
    let fun member element list = exists (same_term element) list in
    let val matchable_variables = (#1 o strip_forall) formula
        val instantiated_variables = map (fn {redex = from, residue = to} => from) term_matching in
    let val uninstantiated_variables = filter (fn mv => not (member mv instantiated_variables)) matchable_variables
        val sub_thm = ASSUME subformula
        val formula_thm = (SPEC_ALL o ASSUME) formula in
    let val instantiated_thm = GENL uninstantiated_variables (INST_TY_TERM (term_matching, []) formula_thm) in
    let val simplified_thm = REWRITE_RULE [sub_thm] instantiated_thm in
      simplified_thm
    end end end end end






  (* 'A u {P} u {!x1...xn. A /\ ...P... /\ B ==> C} |- t'
   * ==>
   * 'A u {A /\ ... /\ B ==> C}[v1...vn/x1...xn] |- t'
   *)
  fun ASM_INST_ASM_TAC (A, t) =
    let fun collect_qimp_otherss asm =
      if (is_imp o #2 o strip_forall) asm then
        let val others = filter (not_same_term asm) A in
          if (not o null) others then [(asm, others)] else []
        end
      else
        [] in
    let val assumption_other_assumptionss = foldl (fn (asm, asm_otherss) => (collect_qimp_otherss asm) @ asm_otherss) [] A in
      case find_formula_subformula_instantiation assumption_other_assumptionss of
        NONE => raise (mk_HOL_ERR "helper_tactics" "ASM_INST_ASM_TAC" "No assumption can be matched such that another assumption appears in it as a subformula.")
      | SOME (subformula, formula, matching) =>
          let val thm = INST_FORALL_RULE subformula formula matching in
          let val (subgoals, validation) = ASSUME_TAC thm (A, t) in
          let val A' = filter (fn a => not_same_term subformula a andalso not_same_term formula a) ((#1 o hd) subgoals) in
            (* ASSUME_TAC does not change t, so it is kept, and formula and subformula are removed from the assumptions. *)
            ([(A', t)], validation)
          end end end
    end end

  (* 'A u {P} u {!x1...xn. A /\ ...P... /\ B ==> C} |- t'
   * ==>
   * 'A u {P} u {A /\ ... /\ B ==> C}[v1...vn/x1...xn] |- t'
   *)
  fun KEEP_ASM_INST_ASM_TAC (A, t) =
    let fun collect_qimp_otherss asm =
      if (is_imp o #2 o strip_forall) asm then
        let val others = filter (not_same_term asm) A in
          if (not o null) others then [(asm, others)] else []
        end
      else
        [] in
    let val assumption_other_assumptionss = foldl (fn (asm, asm_otherss) => (collect_qimp_otherss asm) @ asm_otherss) [] A in
      case find_formula_subformula_instantiation assumption_other_assumptionss of
        NONE => raise (mk_HOL_ERR "helper_tactics" "KEEP_ASM_INST_ASM_TAC" "No assumption can be matched such that another assumption appears in it as a subformula.")
      | SOME (subformula, formula, matching) =>
          let val thm = INST_FORALL_RULE subformula formula matching in
          let val (subgoals, validation) = ASSUME_TAC thm (A, t) in
          let val A' = filter (not_same_term formula) ((#1 o hd) subgoals) in
            (* ASSUME_TAC does not change t, so it is kept, and formula and subformula are removed from the assumptions. *)
            ([(A', t)], validation)
          end end end
    end end





























  (* Inputs:
   * -tm_ty_matching: [x1 |-> z1, ..., xm |-> zm]
   * -uninst_vars = [y1, ..., yn]
   * -Aiinst: Ai z1...zm
   * -orig_imp: !x1, ..., xm, y1, ..., yn. A1 /\ ... /\ Ai-1 /\ Ai /\ Ai+1 /\ ... /\ Ap ==> A
   * -simp_imp_thm: {Ai, !y1...yn. A1 /\ ... /\ Ai-1 /\ Ai+1 /\ ... /\ Ap ==> A} u B |- t
   *
   * Output: {Ai z1...zm, !x1, ..., xm, y1, ..., yn. A1 /\ ... /\ Ai-1 /\ Ai /\ Ai+1 /\ ... /\ Ap ==> A} u B |- t
   *
   * Algorithm:
   * {P, !y1...yn.         A /\               C ==> E} u B |- t                 <---GIVEN FORMULA
   * ----------------------------------------------------------
   * {P, !x1...xm y1...yn. A /\ P(x1...xm) /\ C ==> E} u B |- t					<---TO PROVE
   * 
   * 
   * ------------------------------------------------------------------------------------------------ASSUME
   * !x1...xm y1...yn. A /\ P(x1...xm) /\ C ==> E u B |- !x1...xm y1...yn. A /\ P(x1...xm) /\ C ==> E
   * ------------------------------------------------------------------------------------------------SPEC_ALL
   * !x1...xm y1...yn. A /\ P(x1...xm) /\ C ==> E u B |- A /\ P(x1...xm) /\ C ==> E
   * ------------------------------------------------------------------------------INST_TY_TERM
   * !x1...xm y1...yn. A /\ P(x1...xm) /\ C ==> E u B |- A /\ P /\ C ==> E
   * 
   * MP above and below.
   * 
   * ----------------------------------------ASSUME
   * {A /\ P /\ C ==> E} |- A /\ P /\ C ==> E
   * ----------------------------------------CONJ_ANT_TO_HYP
   * {A /\ P /\ C ==> E, A, P, C} |- E
   * --------------------------------------HYP_IMP_TO_CONJ_IMP_RULE 'A' u 'C'
   * {A /\ P /\ C ==> E, P} |- A /\ C ==> E
   * ---------------------------------------------DISCH 'A /\ P /\ C ==> E'
   * {P} |- (A /\ P /\ C ==> E) ==> (A /\ C ==> E)
   * 
   * MP on above conclusions give:
   * {!x1...xm y1...yn. A /\ P(x1...xm) /\ C ==> E} u B |- A /\ P /\ C ==> E    {P} |- (A /\ P /\ C ==> E) ==> (A /\ C ==> E)
   * ------------------------------------------------------------------------------------------------------------------------MP
   *                   {!x1...xm y1...yn. A /\ P(x1...xm) /\ C ==> E, P} u B |- A /\ C ==> E
   *              -------------------------------------------------------------------------------GENL uninst_vars
   *              {!x1...xm y1...yn. A /\ P(x1...xm) /\ C ==> E, P} u B |- !y1...yn. A /\ C ==> E
   *              -------------------------------------------------------------------------------PROVE_HYP with given formula
   *                         {!x1...xm y1...yn. A /\ P(x1...xm) /\ C ==> E, P} u B |- t
   *
   * Test code combined with the body of :
     val orig_imp = “!x1 y1 x2 y2 x3 y3 x4.
       A1 x1 y1 x2 y2 x3 y3 x4 /\ A2 x1 y1 x2 y2 x3 y3 x4 /\ A3 x1 x2 x3 x4 /\ A4 x1 y1 x2 y2 x3 y3 x4 /\ A5 x1 y1 x2 y2 x3 y3 x4
       ==>
       A x1 y1 x2 y2 x3 y3 x4”
     val orig_imp = “!x1 y1 x2 y2 x3 y3 x4.
       A1 x1 x2 x3 x4
       ==>
       A x1 y1 x2 y2 x3 y3 x4”
     val Aiinst = (#1 o dest_imp o #2 o strip_forall) orig_imp
     val (A, t) = ([orig_imp, Aiinst, “OTHER_ASSUMPTIONS : bool”], F)
   *)
  fun gen_simp_imp_thm tm_ty_matching uninst_vars Aiinst orig_imp simp_imp_thm =
    let val orig_imp__orig_imp_thm = ASSUME orig_imp in
    let val orig_imp__unquant_orig_imp_thm = SPEC_ALL orig_imp__orig_imp_thm in
    let val orig_imp__inst_orig_imp_thm = INST_TY_TERM tm_ty_matching orig_imp__unquant_orig_imp_thm in

    let val inst_orig_imp = concl orig_imp__inst_orig_imp_thm in
    let val inst_orig_imp__inst_orig_imp_thm = ASSUME inst_orig_imp in
    let val inst_orig_imp_hyps_con_thm = CONJ_ANT_TO_HYP inst_orig_imp__inst_orig_imp_thm
        val Aiinsts = (strip_conj o #1 o dest_imp) inst_orig_imp in
    let val other_Ais =
      let fun other_Ais acc [] = acc
            | other_Ais acc (A::As) = if same_term A Aiinst then other_Ais acc As else other_Ais (A::acc) As in
      other_Ais [] Aiinsts end in
    let val inst_orig_imp_Ai__simp_imp_thm =
      foldl (fn (Ai, thm) => HYP_IMP_TO_CONJ_IMP_RULE Ai thm) inst_orig_imp_hyps_con_thm other_Ais in
    let val Aiinst__other_Ais_imp_simp_imp_thm = DISCH inst_orig_imp inst_orig_imp_Ai__simp_imp_thm in

    let val q_imp_Aiinst__other_Ais_imp_thm = MP Aiinst__other_Ais_imp_simp_imp_thm orig_imp__inst_orig_imp_thm in
    let val q_imp_Aiinst__q_other_Ais_imp_thm = GENL uninst_vars q_imp_Aiinst__other_Ais_imp_thm in
    let val q_imp_Aiinst__con_thm = PROVE_HYP q_imp_Aiinst__q_other_Ais_imp_thm simp_imp_thm in
      q_imp_Aiinst__con_thm
    end end end end end end end end end end end end

  (* A u {P, !x1...xm y1...yn. A /\ ... /\ B /\ P(x1...xm) /\ C /\ ... /\ D ==> E} ?- t
   * ----------------------------------------------------------------------------------The number of conjuncts in antecedent
   * A u {P, !y1...yn.         A /\ ... /\ B /\               C /\ ... /\ D ==> E} ?- t
   *
   * Aiinst: P
   * qimp: !x1...xm y1...yn. A /\ ... /\ B /\ P(x1...xm) /\ C /\ ... /\ D ==> E
   *)
  fun ASM_SIMP_IMP_ASM_TAC (qimp, Aiinst, (term_matching, type_matching)) (A, t) =
    let val ivars = map (fn {redex = from, residue = to} => from) term_matching in
    let val (qvars, imp) = strip_forall qimp in
    let val univars = filter (fn qv => all (not_same_term qv) ivars) qvars
        val inst_imp = subst term_matching (inst type_matching imp) in
    let val (inst_ant, inst_suc) = dest_imp inst_imp in
    let val simp_inst_ant_conjs = filter (not_same_term Aiinst) (strip_conj inst_ant) in
    let val simp_inst_imp = if null simp_inst_ant_conjs then inst_suc else mk_imp (list_mk_conj simp_inst_ant_conjs, inst_suc) in
    let val qimp_simp = list_mk_forall (univars, simp_inst_imp) in
    let val A' = update_asm qimp_simp qimp A
        val t' = t
        val validation = fn subgoal_achieving_thm =>
          (* A u {P, !        y1...yn. A /\ ... /\ B /\               C /\ ... /\ D ==> E} |- t
           * ----------------------------------------------------------------------------------
           * A u {P, !x1...xm y1...yn. A /\ ... /\ B /\ P(x1...xm) /\ C /\ ... /\ D ==> E} |- t
           *)
          let val simp_imp_thm = subgoal_achieving_thm in
          let val goal_achieving_thm = gen_simp_imp_thm (term_matching, type_matching) univars Aiinst qimp simp_imp_thm in
            goal_achieving_thm
          end end in
      (A', t', validation, qimp_simp)
    end end end end end end end end

  (* Input:
   * -qimp: !x1...xn. a1 x1...xn /\ ... /\ am x1...xn ==> a x1...xn
   * -other: term.
   *
   * Output:
   * -SOME (term_matching, type_matching) if [x1...xn] |-> [v1...vn] such that
   *  there is a k and ak v1...vn = other, where term_matching and type_matching
   *  specify the instantiation of xi to vi.
   * -NONE otherwise.
   *)
  fun find_qimp_instantiation qimp other =
    let val (instantiatable_variables, imp) = strip_forall qimp in
    let val conjuncts = (strip_conj o #1 o dest_imp) imp in
    let fun find_match [] = NONE
          | find_match (conjunct::conjuncts) =
            case find_explicit_variable_instantiation instantiatable_variables conjunct other of
              NONE => find_match conjuncts
            | SOME term_type_matching => SOME term_type_matching in
      find_match conjuncts
    end end end

  fun find_qimp_instantiations qimp [] = NONE
    | find_qimp_instantiations qimp (other::others) =
      case find_qimp_instantiation qimp other of
        NONE => find_qimp_instantiations qimp others
      | SOME matching => SOME (other, matching)

  fun find_qimp_instantiationss [] = NONE
    | find_qimp_instantiationss ((qimp, others)::qimp_otherss) =
      case find_qimp_instantiations qimp others of
        NONE => find_qimp_instantiationss qimp_otherss
      | SOME (other, matching) => SOME (qimp, other, matching)

  
  fun SIMP_QIMP_COND_ONCE_TAC once (qimp, Aiinst, term_type_matching) (A0, t0) =
    let fun is_qimp term = (is_imp o #2 o strip_forall) term in
    let val (A1, t1, validation1, simp_qimp) = ASM_SIMP_IMP_ASM_TAC (qimp, Aiinst, term_type_matching) (A0, t0) in
      if once then (* Perform tactic once. *)
        (A1, t1, validation1)
      else         (* Perform tactic until there are no assumption that can simply the implication. *)
        let val simp_qimp_otherss = if is_qimp simp_qimp then [(simp_qimp, filter (not_same_term simp_qimp) A1)] else [] in
         case find_qimp_instantiationss simp_qimp_otherss of
           NONE => (A1, t1, validation1)                   (* No further simplifications possible: Termination. *)
         | SOME qimp_Aiinst_term_type_matching1 =>
           let val (A2, t2, validation2) = SIMP_QIMP_COND_ONCE_TAC once qimp_Aiinst_term_type_matching1 (A1, t1) in (* Further simplifications possible: Recursive call. *)
             (A2, t2, validation1 o validation2)
           end
        end
    end end

  (* A u {P, !x1...xm y1...yn. A /\ ... /\ B /\ P(x1...xm) /\ C /\ ... /\ D ==> E} ?- t
   * ---------------------------------------------------------------------------------- if once = true
   * A u {P, !y1...yn.         A /\ ... /\ B /\               C /\ ... /\ D ==> E} ? -t
   *
   * A u {Ai, ..., Aj, !x1...xm y1...yn. A /\ ... /\ Ai /\ ... /\ C /\ ... /\ Aj /\ ... /\ D ==> E} ?- t
   * ---------------------------------------------------------------------------------------------------if once = false
   * A u {Ai, ..., Aj, !        y1...yn. A /\ ... /\ ...       /\ C /\ ... /\           /\ D ==> E} ? -t
   *
   * An implication is simplified as much as possible by removing conjuncts from
   * the antecedent that occur among the assumptions.
   *)
  fun ASM_INST_IMP_ASM_ONCE_OR_REPEAT_TAC once (A : Term.term list, t : Term.term) =
    let fun is_qimp term = (is_imp o #2 o strip_forall) term in
    let val qimps = filter is_qimp A in
    let val qimp_otherss = map (fn qimp => (qimp, filter (not_same_term qimp) A)) qimps in
      case find_qimp_instantiationss qimp_otherss of
        NONE => raise (mk_HOL_ERR "helper_tactics" "ASM_INST_IMP_ASM_ONCE_OR_REPEAT_TAC" "No assumption can simplify another assumption being an implication.")
      | SOME qimp_Aiinst_term_type_matching =>
        let val (A', t', validation') = SIMP_QIMP_COND_ONCE_TAC once qimp_Aiinst_term_type_matching (A, t) in
          ([(A', t')], (validation' o hd))
        end
    end end end

  (* A u {P, !x1...xm y1...yn. A /\ ... /\ B /\ P(x1...xm) /\ C /\ ... /\ D ==> E} ?- t
   * ----------------------------------------------------------------------------------
   * A u {P, !y1...yn.         A /\ ... /\ B /\               C /\ ... /\ D ==> E} ? -t
   *
   * An implication is simplified by removing one conjunct from the antecedent
   * that occur among the assumptions.
   *)
  val ASM_INST_IMP_ASM_ONCE_TAC = ASM_INST_IMP_ASM_ONCE_OR_REPEAT_TAC true

  (* A u {Ai, ..., Aj, !x1...xm y1...yn. A /\ ... /\ Ai /\ ... /\ C /\ ... /\ Aj /\ ... /\ D ==> E} ?- t
   * ---------------------------------------------------------------------------------------------------
   * A u {Ai, ..., Aj, !        y1...yn. A /\ ... /\ ...       /\ C /\ ... /\           /\ D ==> E} ? -t
   *
   * An implication is simplified as much as possible by removing conjuncts from
   * the antecedent that occur among the assumptions.
   *)
  val ASM_INST_IMP_ASM_TAC = ASM_INST_IMP_ASM_ONCE_OR_REPEAT_TAC false
























  (* Both are variables:
   * 1. Both are instantiatable: Map from |-> to.
   *    -If one or the other is bounded by abstraction, then the mapping will be
   *     checked at that point.
   *    -If none of them are bounded by abstraction, then it is unknown how to
   *     instantiate the implication, in order ot instantiate other conjuncts or
   *     the conclusion to be useful, and then the instantiation fails.
   * 2. Only from is instantiatable: Instantiate from to to.
   * 3. Only to is instantiatable: Instantate to to from.
   * 4. None is instantiatable: Must be the same variable. Otherwise fail.
   *
   * Only from is a variable, and to is not a variable: Then from must be instantiatable. Otherwise fail.
   *
   * Only to is a variable, and from is not a variable: Then to must be instantiatable. Otherwise fail.
   *)
  fun find_double_inst_var iv_imp iv_asm imp asm =
    if is_var imp andalso is_var asm then (* Both variables. *)
      if is_instantiatable_variable iv_imp imp andalso is_instantiatable_variable iv_asm asm then (* Both instantiatable. *)
        case find_explicit_type_variable_instantiation asm imp of
          NONE => NONE
        | SOME type_matching => (* Type instantiate asm, leaving more flexibility for later instantiations of qimp. *)
          SOME (([], []), ([], []), ([(imp, asm)], type_matching))
      else if is_instantiatable_variable iv_imp imp then                                          (* Only imp instantiatable. *)
        case find_explicit_type_variable_instantiation imp asm of
          NONE => NONE
        | SOME type_matching => SOME (([{redex = inst type_matching imp, residue = asm}], type_matching), ([], []), ([], []))
      else if is_instantiatable_variable iv_asm asm then                                          (* Only asm instantiatable. *)
        case find_explicit_type_variable_instantiation asm imp of
          NONE => NONE
        | SOME type_matching => SOME (([], []), ([{redex = inst type_matching asm, residue = imp}], type_matching), ([], []))
      else if same_term imp asm then                                                           (* None instantiatable. WHAT ABOUT TYPE VARIABLES??????????????????????????????????????????????????????????????????????????????????????????????*)
        SOME (([], []), ([], []), ([], []))                                                       (* Denote same object: Ok. *)
      else
        NONE                                                                                      (* Denote different objects: Nok. *)
    else if is_var imp andalso is_instantiatable_variable iv_imp imp then (* Only imp is variable *)
      case find_explicit_type_variable_instantiation imp asm of
        NONE => NONE
      | SOME type_matching => SOME (([{redex = inst type_matching imp, residue = asm}], type_matching), ([], []), ([], []))
    else if is_var asm andalso is_instantiatable_variable iv_asm asm then (* Only asm is variable. *)
      case find_explicit_type_variable_instantiation asm imp of
        NONE => NONE
      | SOME type_matching => SOME (([], []), ([{redex = inst type_matching asm, residue = imp}], type_matching), ([], []))
    else (* Cannot match uninstantiatable variable to non-variables. *)
      NONE

  fun find_double_inst_const iv_imp iv_asm imp asm = (* At least one of imp and asm is a constant. Consider all cases. *)
    if is_const imp andalso is_const asm then
      if term_to_string imp = term_to_string asm then             (* Do not compare types here. *)
        case find_explicit_type_variable_instantiation asm imp of (* Compare types here, where asm is type instantiated. *)
          NONE => NONE
        | SOME type_matching => SOME (([], []), ([], type_matching), ([], [])) (* Type instantiate asm for flexibility of imp. *)
      else
        NONE
    else if is_const imp andalso is_var asm andalso is_instantiatable_variable iv_asm asm then (* asm to be instantiated. *)
      case find_explicit_type_variable_instantiation asm imp of (* Compare types here, where asm is type instantiated. *)
        NONE => NONE
      | SOME type_matching =>
        SOME (([], []), ([{redex = inst type_matching asm, residue = imp}], type_matching), ([], [])) (* Type instantiate asm. *)
    else if is_const asm andalso is_var imp andalso is_instantiatable_variable iv_imp imp then (* imp to be instantiated. *)
      case find_explicit_type_variable_instantiation imp asm of (* Compare types here, where imp is type instantiated. *)
        NONE => NONE
      | SOME type_matching =>
        SOME (([{redex = inst type_matching imp, residue = asm}], type_matching), ([], []), ([], [])) (* Type instantiate imp. *)
    else
      NONE

  fun split_list_some_property some_property [] = ([], [])
    | split_list_some_property some_property (e::es) =
      let val (properties, not_properties) = split_list_some_property some_property es in
      case some_property e of
        NONE => (properties, e::not_properties)
      | SOME new_e => (new_e::properties, not_properties)
      end

  (* imp_inst: true if imp is instantiated, and false if asm is instantiated. *)
  fun update_inst imp_inst old_inst bi_inst inst_var inst_term =
    let fun some_property (imp_var, asm_var) =
      if same_term inst_var (if imp_inst then imp_var else asm_var) then
        SOME {redex = if imp_inst then asm_var else imp_var, residue = inst_term}
      else
        NONE in
    let val (additional_inst, new_bi_inst) = split_list_some_property some_property bi_inst in
      case merge_term_matchings additional_inst old_inst of
        NONE => NONE
      | SOME merged_inst => SOME (merged_inst, new_bi_inst)
    end end

  (* If x is instantiated, then x must be removed from bi-instantiation, and all
   * its pair mates in the bi-instantiation shall be instantiated to the same
   * term, if consistency is preserved, otherwise failure. This is repeated as
   * long as there is an instantiated variable in the bi-instantiation.
   *
   * If un_inst is a unidirectional instantiation from imp, then
   * bi_to_this (a, b) = a, bi_to_other (a, b) = b, where (a, b) is in bi_inst.
   * If un_inst is a unidirectional instantiation from asm, then
   * bi_to_this (a, b) = b, bi_to_other (a, b) = a, where (a, b) is in bi_inst.
   *)
  fun update_insts inst_imp inst_asm bi_inst =
    (* Exists an instantiation for imp that occur in bi-directional instantiation. *)
    case List.find (fn {redex = inst_var, residue = _} => exists (fn (impv, _) => same_term inst_var impv) bi_inst) inst_imp of

      (* Obtain instantiation. *)
      SOME {redex = inst_var, residue = inst_term} =>
       (* Variable inst_var in imp is instantiated to inst_term: Update asm. *)
      (case update_inst false inst_asm bi_inst inst_var inst_term of
        NONE => NONE
      | SOME (merged_inst_asm, new_bi_inst) => update_insts inst_imp merged_inst_asm new_bi_inst
      )
      (* No variables in bi-directional instantiation occur in imp instantiation: Check asm instantiation. *)
    | NONE =>  
      (case List.find (fn {redex = inst_var, residue = _} => exists (fn (_, asmv) => same_term inst_var asmv) bi_inst) inst_asm of
        (* Exists an instantiation (inst_var, inst_term) for asm that occur in bi-directional instantiation. *)
        SOME {redex = inst_var, residue = inst_term} =>
         (* Variable inst_var in asm is instantiated to inst_term: Update imp. *)
        (case update_inst true inst_imp bi_inst inst_var inst_term of
          NONE => NONE
        | SOME (merged_inst_imp, new_bi_inst) => update_insts merged_inst_imp inst_asm new_bi_inst
        )
      | NONE => (* No variables in bi-directional instantiation occur in the imp and asm instantiations. Return update. *)
        SOME (inst_imp, inst_asm, bi_inst)
      )

  (* Algorithm:
   * 1. Union bidirectional instantiations.
   * 2. Merge the two unidirectional instantiations.
   * 3. If x is instantiated, then x must be removed from bi-instantiation, and
   *    all its pair mates in the bi-instantiation shall be instantiated to the
   *    same term, if consistency is preserved, otherwise failure. This is
   *    repeated as long as there is an instantiated variable in the
   *    bi-instantiation.
   *)
  fun merge_term_insts imp_inst1 imp_inst2 asm_inst1 asm_inst2 bi_inst1 bi_inst2 =
    let fun bi_union []                             bi_inst2 = bi_inst2
          | bi_union ((imp_var, asm_var)::bi_inst1) bi_inst2 =
            let val unioned = bi_union bi_inst1 bi_inst2 in
            if exists (fn (iv, av) => same_term imp_var iv andalso same_term asm_var av) unioned then (* Avoid duplicates. *)
              unioned
            else
              (imp_var, asm_var)::unioned
            end in
      case merge_term_matchings imp_inst1 imp_inst2 of
        NONE => NONE
      | SOME inst_imp =>
      case merge_term_matchings asm_inst1 asm_inst2 of
        NONE => NONE
      | SOME inst_asm =>
      let val bi_inst = bi_union bi_inst1 bi_inst2 in
      update_insts inst_imp inst_asm bi_inst
    end end

  (* An instantiation is correct when imp and asm are instantiated such that
   * there is still opportunity to make them identical.
   * -No bi-instantiations: Check consistency of both pairs of di-instantiations.
   *
   * -Bi-instantiations, without common variables, and no variables in
   *  di-instantiations: Union them.
   *
   * -Bi-instantiations, with common variables, and no variables in
   *  di-instantiations: Union them.
   *
   *  For instance, di1 = [...(x, y)...}, di2 = [...(x, z)...} mean that x, y and
   *  z are all universally quantified. Since x cannot be instantiated to 2
   *  different terms simultanesously, y and z must be instantiated to x.
   *  Therefore, the double instantiations are unioned. Whether the end result is
   *  useful depends thus on the terms being instantiated.
   *
   * -Bi-instantiations with variables occuring in instantiations, after
   *  bi-instantiations have been unioned:
   *  *Variable x in bi-instantiation (x, y) or (y, x) is instantiated to t:
   *   Extend and check consistency of also instantiating y to t. Remove x and y
   *   from biinstantiation.
   *  *Variable x in bi-instantiation (x, y) or (y, x) is instantiated from
   *   z |-> x: This means that z is a universally quantified variable, but so is
   *   also x, since x occurs in a bi-instantiation. Hence, the instantiation
   *   z |-> x is in a bi-instantiation and not in a di-instantiation. This case
   *   cannot occur.
   *
   * This gives the following algorithm:
   * 1. Union bidirectional instantiations.
   * 2. Merge the two directional instantiations and check consistency.
   * 3. If x is instantiated, then x must be removed from bi-instantiation, and
   *    all its pair mates in the bi-instantiation shall be instantiated to the
   *    same term, if consistency is preserved, otherwise failure. This is
   *    repeated as long as there is an instantiated variable in the
   *    bi-instantiation.
   *
   * @iv_imp: List of variables that may be instantiated in the term imp.
   * @iv_asm: List of variables that may be instantiated in the term asm.
   *)
  fun find_double_inst_comb find_double_inst iv_imp iv_asm imp asm =
    let val merge_tyms = merge_type_matchings
        val (f_imp, a_imp) = dest_comb imp
        val (f_asm, a_asm) = dest_comb asm in
      case (find_double_inst iv_imp iv_asm f_imp f_asm, find_double_inst iv_imp iv_asm a_imp a_asm) of
        (_, NONE) => NONE
      | (NONE, _) => NONE
      | (SOME ((f_imp_te_i, f_imp_ty_i), (f_asm_te_i, f_asm_ty_i), (f_bi_te_i, f_bi_ty_i)),
         SOME ((a_imp_te_i, a_imp_ty_i), (a_asm_te_i, a_asm_ty_i), (a_bi_te_i, a_bi_ty_i))) =>
        case (merge_tyms f_imp_ty_i a_imp_ty_i, merge_tyms f_asm_ty_i a_asm_ty_i, merge_tyms f_bi_ty_i a_bi_ty_i) of
          (NONE, _, _) => NONE
        | (_, NONE, _) => NONE
        | (_, _, NONE) => NONE
        | (SOME imp_inst_ty, SOME asm_inst_ty, SOME bi_inst_ty) =>
          case merge_term_insts f_imp_te_i a_imp_te_i f_asm_te_i a_asm_te_i f_bi_te_i a_bi_te_i of
            NONE => NONE
          | SOME (imp_inst_te, asm_inst_te, bi_inst_te) =>
            SOME ((imp_inst_te, imp_inst_ty), (asm_inst_te, asm_inst_ty), (bi_inst_te, bi_inst_ty))
      end

  (* Either all occurrences of var_imp and var_asm match each other in bi_inst,
   * and not instantiated to any other terms, or none of them are instantiated
   * to any term. Hence, the algorithm is:
   * 1.	var_imp nor var_asm occur in imp_inst_term nor asm_inst_term,
   *	respectively.
   * 2. If var_imp or var_asm occur is in bi_inst_term, then the other component
   *	is var_asm or var_imp, respectively.
   * 3. If var_imp or var_asm occur is in bi_inst_term, then they are removed
   *	from bi_inst_term, since they are bounded variables that are not
   *    instantiatable.
   *)
  fun find_double_inst_abs find_double_inst iv_imp iv_asm imp asm =
    let val (var_imp, body_imp) = dest_abs imp
        val (var_asm, body_asm) = dest_abs asm in
      case find_double_inst (var_imp::iv_imp) (var_asm::iv_asm) body_imp body_asm of
        NONE => NONE
      | SOME ((imp_inst_term, imp_inst_type), (asm_inst_term, asm_inst_type), (bi_inst_term, bi_inst_type)) =>
        if exists (fn {redex = inst_var, residue = inst_term} => same_term var_imp inst_var) imp_inst_term then
          NONE                            (* var_imp instantiated to a term, and not var_asm. *)
        else if exists (fn {redex = inst_var, residue = inst_term} => same_term var_imp inst_var) asm_inst_term then
          NONE                            (* var_asm instantiated to a term, and not var_imp. *)
        else
          let fun inconsistent_match (vi, va) =
            (same_term var_imp vi andalso not_same_term var_asm va) orelse
            (not_same_term var_imp vi andalso same_term var_asm va)
              fun is_same_match (vi, va) = same_term var_imp vi andalso same_term var_asm va in
          let fun update_bi_instantiation [] = SOME []
                | update_bi_instantiation (vi_va::vi_vas) =
                  if inconsistent_match vi_va then (* Bounded variables are not matched only to each other: Not ok. *)
                    NONE
                  else if is_same_match vi_va then (* Bounded variables matched to each other: Shall not occur in final matching. *)
                    update_bi_instantiation vi_vas
                  else (* None of the bounded variables occur in the current vi_va: Keep vi_va in the bi-instantiation. *)
                    case update_bi_instantiation vi_vas of
                      NONE => NONE
                    | SOME updated_bi_instantiation => SOME (vi_va::updated_bi_instantiation) in
          case update_bi_instantiation bi_inst_term of
            NONE => NONE                  (* Bounded variables not matched to each other. *)
          | SOME bi_inst_without_bvars => (* Bounded variables matched to each other, or both unmatched: Removed from bi_inst_term. *)
            SOME ((imp_inst_term, imp_inst_type), (asm_inst_term, asm_inst_type), (bi_inst_without_bvars, bi_inst_type))
          end end
    end

 (* Input:
   * -Terms conjunct and asm.
   * -Terms iv_imp which are variables in conjunct that may be instantiated to
   *  terms occuring in asm.
   * -Terms iv_asm which are variables in asm that may be instantiated to terms
   *  occuring in conjunct.
   *
   * Output:
   * -Some ((term_variable_instantiation_conjunct, type_variable_instantiation_conjunct),
   *        (term_variable_instantiation_asm     , type_variable_instantiation_asm     )),
   *  if the free variables iv_imp and iv_asm in conjunct and asm, respectively,
   *  can be substituted for terms_conjunct and terms_asm such that
   *  (inst type_variable_instantiation_conjunct conjunct)[terms_conjunct/instantiatable_variables_conjunct] =
   *  (inst type_variable_instantiation_asm      asm     )[terms_asm     /instantiatable_variables_asm     ]
   * -NONE otherwise.
   *)
  fun find_double_inst iv_imp iv_asm conjunct asm =
    if is_var conjunct orelse is_var asm then
      find_double_inst_var iv_imp iv_asm conjunct asm
    else if is_const conjunct orelse is_const asm then
      find_double_inst_const iv_imp iv_asm conjunct asm
    else if is_comb conjunct andalso is_comb asm then
      find_double_inst_comb find_double_inst iv_imp iv_asm conjunct asm
    else if is_abs conjunct andalso is_abs asm then
      find_double_inst_abs find_double_inst iv_imp iv_asm conjunct asm
    else (* conjunct and asm have different syntactical structures. *)
      NONE

  (* Input:
   * -qimp: !X. a1 X /\ ... /\ am X ==> a X
   * -qasm: !Y. asm Y
   *
   * Output:
   * -SOME ((X', qimp_inst_type), (Y', qasm_inst_type), (X'', Y''))
   *  if X'' and Y'' can be instantiated to common terms such that
   *  ai X'X'' = asm Y'Y'' for some 1 <= i <= m.
   * -NONE otherwise.
   *)
  fun find_qimp_qasm_instantiation qimp qasm =
    let val (iv_imp, imp) = strip_forall qimp
        val (iv_asm, asm) = strip_forall qasm in
    let val conjuncts = (strip_conj o #1 o dest_imp) imp in
    let fun find_double_insts [] = NONE
          | find_double_insts (conjunct::conjuncts) =
            case find_double_inst iv_imp iv_asm conjunct asm of
              NONE => find_double_insts conjuncts
            | SOME ((qimp_inst_term, qimp_inst_type), (qasm_inst_term, qasm_inst_type), (univ_terms, univ_inst_type)) =>
              SOME ((qimp_inst_term, qimp_inst_type), (qasm_inst_term, qasm_inst_type), (univ_terms, univ_inst_type)) in
      find_double_insts conjuncts
    end end end

  fun find_qimp_qasm_instantiations qimp [] = NONE
    | find_qimp_qasm_instantiations qimp (qasm::qasms) =
      case find_qimp_qasm_instantiation qimp qasm of
        NONE => find_qimp_qasm_instantiations qimp qasms
      | SOME (      (qimp_inst_term, qimp_inst_type), (qasm_inst_term, qasm_inst_type), (univ_terms, univ_inst_type)) => 
        SOME (qasm, (qimp_inst_term, qimp_inst_type), (qasm_inst_term, qasm_inst_type), (univ_terms, univ_inst_type))

  fun find_qimp_qasm_instantiationss [] = NONE
    | find_qimp_qasm_instantiationss ((qimp, qasms)::qimp_qasmss) =
      case find_qimp_qasm_instantiations qimp qasms of
        NONE => find_qimp_qasm_instantiationss qimp_qasmss
      | SOME (      qasm, (qimp_inst_term, qimp_inst_type), (qasm_inst_term, qasm_inst_type), (univ_terms, univ_inst_type)) =>
        SOME (qimp, qasm, (qimp_inst_term, qimp_inst_type), (qasm_inst_term, qasm_inst_type), (univ_terms, univ_inst_type))

  (* A u {!X.  A1 X   /\ ... /\ An X   ==> A X  , !Y . Ai Y } ?- t
   * -------------------------------------------------------------
   * A u {!X'. A1 VX' /\ ... /\ An VX' ==> A VX', !Y'. Ai Y'} ?- t
   *
   * Where X' |-> V' and Y' |-> V' can be instantiated to common terms V' such
   * that Ai V'X' = Ai V'Y'.
   *)
  fun INST_QIMP_QASM_TAC (A, t) =
    let fun is_qimp term = (is_imp o #2 o strip_forall) term in
    let val qimps = filter is_qimp A in
    let val qimp_qasm_otherss = map (fn qimp => (qimp, filter (fn asm => not_same_term qimp asm (*andalso is_forall asm*)) A)) qimps in
    let val (qimp, qasm, (qimp_inst_term, qimp_inst_type), (qasm_inst_term, qasm_inst_type), (univ_terms, univ_inst_type)) =
      case find_qimp_qasm_instantiationss qimp_qasm_otherss of
        NONE => raise (mk_HOL_ERR "helper_tactics" "INST_QIMP_QASM_TAC" "Cannot find quantified formula and quantified implication among assumptions.")
     | SOME (qimp, qasm, (qimp_inst_term, qimp_inst_type), (qasm_inst_term, qasm_inst_type), (univ_terms, univ_inst_type)) =>
            (qimp, qasm, (qimp_inst_term, qimp_inst_type), (qasm_inst_term, qasm_inst_type), (univ_terms, univ_inst_type)) in
    let val (A1, t1, v1, qimp1) = INST_ASM_TAC (qimp_inst_term, qimp_inst_type) qimp (A, t) in
    let val (A2, t2, v2, qasm2) = INST_ASM_TAC (qasm_inst_term, qasm_inst_type) qasm (A1, t1) in
      (A2, t2, v1 o v2, qimp1, qasm2)
    end end end end end end

  (* A u {P, !X . Q X  , !Y . ... /\ P Y   /\ ... /\ Q Y   /\ ... ==> R Y  } ?- t
   * ----------------------------------------------------------------------------
   * A u {P, !X'. Q VX', !Y'. ... /\ P VY' /\ ... /\ Q VY' /\ ... ==> R VY'} ?- t
   *
   * That is, assumptions, quantified or not, are used to simplify implications,
   * quantified or not.
   *)
(*
  fun ASMS_SIMP_QIMP_TAC (A, t) =
    let val (subgoals1, v1) = ASM_INST_IMP_ASM_TAC (A, t) in
    let val (A2, t2, v2, qi_imp, qi_qasm) = INST_QIMP_QASM_TAC (hd subgoals1) in
    let val (subgoals3, v3) = ASM_INST_IMP_ASM_TAC (A2, t2) in
      (subgoals3, fn thms => v1 [(v2 o v3) thms])
    end end end
*)
  fun ASMS_SIMP_QIMP_TAC (A, t) =
    let val (subgoals1, v1) = ASM_INST_IMP_ASM_TAC (A, t) handle _ => ([(A, t)], hd) in (* Protects agains simplifications that cannot be done before quantified assumptions are used. *)
    let val (A2, t2, v2, qi_imp, qi_qasm) = INST_QIMP_QASM_TAC (hd subgoals1) in
    let val (subgoals3, v3) = ASM_INST_IMP_ASM_TAC (A2, t2) handle _ => ([(A2, t2)], hd) in (* Protects agains simplifications that cannot be done before quantified assumptions are used. *)
      (subgoals3, fn thms => v1 [(v2 o v3) thms])
    end end end

  (****************************************************************************)
  (*End of tactic that removes an assumption and uses it to rewrite an*********)
  (*assumption that is a universally quantified implication.*******************)
  (****************************************************************************)

  fun find_qimp_instantiation qimp other =
    let val (instantiatable_variables, imp) = strip_forall qimp in
    let val conjuncts = (strip_conj o #1 o dest_imp) imp in
    let fun find_match [] = NONE
          | find_match (conjunct::conjuncts) =
            case find_explicit_variable_instantiation instantiatable_variables conjunct other of
              NONE => find_match conjuncts
            | SOME term_type_matching => SOME term_type_matching in
      find_match conjuncts
    end end end

  (* Given:
   * -qimp: !X. a1 X /\ ... /\ ak-1 X /\ ak X /\ ak+1 X /\ ... /\ at X ==> a X
   *  which is in A.
   * -conj: ak that can be made equal to tij'.
   * -term_subst: How to instantiate X' to V', where X' is a subset of X, so that
   *  ak V is tij'.
   * -type_subst: How to type instantiate qimp.
   * -other: tij which is in A.
   * -template, mark_unrefl_refl_substitutions: How to instantiate tij to become
   *  tij', potentially by means equalities in A (considering both left to right
   *  and right to left rewrites).
   *
   * Rewrites qimp to
   * !Y. a1 V Y /\ ... /\ ak-1 V Y /\ ak+1 V Y /\ ... /\ at V Y ==> a V Y, where
   * Y is X without the instantiated variables X': Y = X - X'.
   *)
  fun REMOVE_ANT_CONJ_ASM_TAC (qimp, term_subst, type_subst, other, template, mark_unrefl_refl_subst, reflect_other) (A, t) =
    (* 1. Instantiate qimp according to term_subst and type_subst. *)
    let val (A1, t1, v1, inst_qimp) = INST_ASM_TAC (term_subst, type_subst) qimp (A, t) in
    (* 2. Add another copy of other that is rewritten according to substitutions. *)
    let val (A2, t2, v2, new_asm) = ADD_RW_ASM_REFL_TAC other reflect_other template mark_unrefl_refl_subst (A1, t1) in
    (* 3. Use rewritten assumption to simplify instantiated qimp. *)
    let val (qimp_to_new_asm_term_inst, qimp_to_new_asm_type_inst) =
    (* term_subst and type_subst shall describe how to instantiate qimp so that one of its antecedent conjuncts is new_asm. *)
      case find_qimp_instantiation qimp new_asm of
        NONE => raise (mk_HOL_ERR "helper_tactics" "REMOVE_ANT_CONJ_ASM_TAC" "Cannot instantiate quantified implication.")
      | SOME (qimp_to_new_asm_term_inst, qimp_to_new_asm_type_inst) => (qimp_to_new_asm_term_inst, qimp_to_new_asm_type_inst) in
    let val (A3, t3, v3, qimp_simp) =
      ASM_SIMP_IMP_ASM_TAC (inst_qimp, new_asm, (qimp_to_new_asm_term_inst, qimp_to_new_asm_type_inst)) (A2, t2) in
    (* 4. Remove the additional copy in 2. *)
    let val (subgoals4, validation4) = REMOVE_ASM_TAC new_asm (A3, t3) in
    let val (A4, t4) = hd subgoals4
        val v4 = fn thm => validation4 [thm] in
      (A4, t4, v1 o v2 o v3 o v4, qimp_simp)
    end end end end end end

  fun ASM_EQ_INST_ASM_IMP_ONCE_OR_REPEAT_TAC once (A : Term.term list, t : Term.term) =
    let val eqs = filter is_eq A in                                                                             (* [l1=r1...ln=rn] *)
    let fun tactic qimp__term_subst__type_subst__other__template__asm_rws__refl0 (A0, t0) =
      let val (A1, t1, v1, qimp_simp) = REMOVE_ANT_CONJ_ASM_TAC qimp__term_subst__type_subst__other__template__asm_rws__refl0 (A0, t0) in
        if once then
          ([(A1, t1)], v1 o hd)
        else if (not o is_imp o #2 o strip_forall) qimp_simp then (* The implication was simplified to the succedent. *)
          ([(A1, t1)], v1 o hd)
        else
          let val others = filter (not_same_term qimp_simp) A1 in
            (* New evaluation of eqs is not necessary since only universally
             * quantified terms and implications can change.
             *
             * Check if the simplified implication can be further simplified.
             *)
            case has_simplifiable_implication eqs [(qimp_simp, others)] of
              NONE => ([(A1, t1)], v1 o hd)
            | SOME qimp__term_subst__type_subst__other__template__asm_rws__refl1 =>
              let val (subgoals2, v2) =
                    tactic qimp__term_subst__type_subst__other__template__asm_rws__refl1 (A1, t1) in
                (subgoals2, v1 o v2)
              end
          end
      end
        val qimps = filter (is_imp o #2 o strip_forall) A in                                                    (* [p1 ==> q1, ...] *)
    let val qimp_otherss = map (fn qimp => (qimp, filter (not_same_term qimp) A)) qimps in (* [(p1==>q1,[as])] *)
      case has_simplifiable_implication eqs qimp_otherss of
        NONE => raise (mk_HOL_ERR "helper_tactics" "ASM_EQ_INST_ASM_IMP_ONCE_OR_REPEAT_TAC" "No implication to simplify.")
      | SOME qimp__term_subst__type_subst__other__template__asm_rws__refl =>
        tactic qimp__term_subst__type_subst__other__template__asm_rws__refl (A, t)
    end end end

  val ASM_EQ_INST_ASM_IMP_ONCE_TAC = ASM_EQ_INST_ASM_IMP_ONCE_OR_REPEAT_TAC true

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
  val ASM_EQ_INST_ASM_IMP_TAC = ASM_EQ_INST_ASM_IMP_ONCE_OR_REPEAT_TAC false

  (* Rewrite the theorem to:
   * a) B u {Cj V}_j |- !X'. C1 V X' /\ ... /\ Ci V' X' /\ ... /\ Ck V X'  ==> C V  X'.
   * b) B u {Cj V}_j |-      C1 V X' /\ ... /\ Ci V' X' /\ ... /\ Ck V X'  ==> C V  X'.
   * c) B u {Cj V}_j |-      C1 V' X'' /\ ... /\ Ci V' /\ ... /\ Ck V' X'' ==> C V' X''. Instantiate quantified variables in Ci.
   * d) B u {Cj V}_j u      {C1 V' X'' /\ ... /\ Ci V' /\ ... /\ Ck V' X''} |- C V' X''.
   * e) B u {Cj V}_j u      {C1 V' X'', ...,     Ci V', ...,     Ck V' X''} |- C V' X''.
   * f) B u {Cj V}_j u {Ci V'} u                {C1 V' X'', ..., Ck V' X''} |- C V' X''.
   * g) B u {Cj V}_j u {Ci V'} u            {C1 V' X'' /\ ... /\ Ck V' X''} |- C V' X''.
   * h) B u {Cj V}_j u {Ci V'} |-            C1 V' X'' /\ ... /\ Ck V' X'' ==> C V' X''.
   * i) B u {Cj V}_j u {Ci V'} |-      !X''. C1 V' X'' /\ ... /\ Ck V' X'' ==> C V' X''.
   *)
  fun INST_LEMMA_RULE term_inst type_inst asm_rw_template mark_unrefl_refl_substs reflect_asm lemma0 =
    let val lemma0 = INST_TYPE type_inst lemma0 in
    let val (original_qvars, unqimp) = (strip_forall o concl) lemma0
        val ivars = term_subst_to_froms term_inst
        fun new_qvs (qv, type_inst_qvs) = if not (is_in ivars qv) then ((*inst type_inst*) qv)::type_inst_qvs else type_inst_qvs
        val asm_inst = let val (unrefls, refls) = mark_unrefl_refl_substs in unrefls @ refls end in
    let val asm = foldl (fn ((m, {redex = _, residue = new}, _), template) => subst [m |-> new] template) asm_rw_template asm_inst
        val remaining_qvars = foldl new_qvs [] original_qvars in
    let val lemma_asm = if reflect_asm then let val (l, r) = dest_eq asm in mk_eq (r, l) end else asm
        val lemma1 = SPEC_ALL lemma0 in
    let val lemma2 = INST term_inst lemma1 in
    let val lemma3 = ANT_CONJ_TO_HYP_RULE lemma_asm lemma2 in
    let val lemma4 = GENL remaining_qvars lemma3 in
    let val lemma5 = if reflect_asm then PROVE_HYP ((SYM o ASSUME) asm) lemma4 else lemma4 in
      lemma5
    end end end end end end end end






  

  (* A u {!XY. P XY ==> t(XY)} ?- t(V)
   * --------------------------------- where Y is matched against V and X against other assumptions in A.
   *      A ?- ?X'. P X'V
   *)
  fun INST_IMP_ASM_MP_CON_TAC (A, t) =
    let val qimps = filter (fn ass => is_imp ass orelse is_forall ass andalso (is_imp o #2 o strip_forall) ass) A in
    let fun match_con asm =
      let val (instantiatable_variables, imp) = strip_forall asm in
      let val (ant, suc) = dest_imp imp in
        find_explicit_variable_instantiation instantiatable_variables suc t
      end end in
    let fun find_inst_asm [] = raise (mk_HOL_ERR "helper_tactics" "INST_IMP_ASM_GOAL" "No implication with succedent matching conclusion.")
          | find_inst_asm (asm::asms) =
              case match_con asm of
                NONE => find_inst_asm asms
              | SOME inst => (inst, asm) in
    let val (inst, asm) = find_inst_asm A in
    let val (A1, t1, v1, inst_asm) = INST_ASM_TAC inst asm (A, t) in
    let val (subgoals2, v2) = MATCH_MP_TAC (ASSUME inst_asm) (A1, t1) in
    let val (subgoals3, v3) = PAXTAC (hd subgoals2) in
      (subgoals2, fn thms => (v1 o v2) [v3 thms])
    end end end end end end end

















  fun SIMP_QIMP_ASM_ONCE_TAC (A, t) =
    let fun is_qimp term = is_forall term andalso (is_imp o #2 o strip_forall) term in
    let fun find_thm [] = raise (mk_HOL_ERR "helper_tactics" "SIMP_QIMP_ASM_ONCE_TAC" "No quantified implication among assumptions.")
          | find_thm (term::terms) =
            if is_qimp term then
              let val (ivs, body) = strip_forall term in
              let val is = find_xis [] ivs body in
                if null is then
                  find_thm terms
                else
                  let val uvs = filter (fn iv => all (fn {redex = v, residue = i} => not_same_term iv v) is) ivs in
                    (term, REWRITE_RULE [] (GENL uvs (INST is ((SPEC_ALL o ASSUME) term))))
                  end
              end end
            else
              find_thm terms in
    let val (term, thm) = find_thm A in
    let val new_asm = concl thm
        val v1 = #2 (ASSUME_TAC thm (A, t)) in
    let fun replace_assumption [] = raise (mk_HOL_ERR "helper_tactics" "SIMP_QIMP_ASM_ONCE_TAC" "Simplified assumption gone!")
          | replace_assumption (asm::asms) =
            if same_term term asm then
              new_asm::asms
            else
              asm::(replace_assumption asms) in
    let val A1 = replace_assumption A in
      ([(A1, t)], v1)
    end end end end end end

  (* A u {!x1...xn. ... /\ xi = si /\ ... ==> s} ?- t
   * ----------------------------------------------
   * A u {!x1...xn. ... @ ... ==> s} ?- t
   *
   * Instantiates xi to si and removes the corresponding conjunct being part of
   * an implication which may contain other connectives.
   *)
  val SIMP_QIMP_ASM_TAC = REPEAT SIMP_QIMP_ASM_ONCE_TAC










  (****************************************************************************)
  (*End of tactic that uses assumptions to simplify a universally quantified***)
  (*implication among the assumptions.*****************************************)
  (****************************************************************************)






  (****************************************************************************)
  (*Start of lambda abstraction application tactic*****************************)
  (****************************************************************************)

  fun is_app_scalar term = if is_comb term then (is_abs o rator) term else false

  val have_app_scalars_rw = have_terms_subterm_rw BETA_CONV is_app_scalar

  (* Rewrites terms in the assumptions and the conclusion of the form
   * '(\x. body) argument' to 'body[argument/x]'.
   *)
  val APP_SCALAR_TAC =
    let fun tactic (A, t) =
      case have_app_scalars_rw (t::A) of
        NONE => raise (mk_HOL_ERR "helper_tactics" "APP_SCALAR_TAC" "No applications of abstractions.")
      | SOME (rw_term, rw_thm) => RW_TERM_TAC rw_term rw_thm (A, t) in
      tactic THEN REPEAT tactic
    end

  (****************************************************************************)
  (*End of lambda abstraction application tactic*******************************)
  (****************************************************************************)



  (****************************************************************************)
  (*Start of paired lambda abstraction application tactic**********************)
  (****************************************************************************)

  (* Input:
   * -A term.
   *
   * Output:
   * -False: The given term is not of the form '(\p1, p2. body) (a1, a2)'.
   * -True: The given term is of the form '(\p1, p2. body) (a1, a2)'.
   *)
  fun is_app_pair term =
    if is_comb term then
      let val (abstraction, tuple_argument) = dest_comb term in
        if (not o is_abs) abstraction andalso is_comb abstraction andalso pairSyntax.is_pair tuple_argument then
          let val (UNCURRY, uncurried_abstraction) = dest_comb abstraction in
            term_to_string UNCURRY = "UNCURRY"
          end
        else
          false
      end
    else
      false

  (* Input:
   * -A list of terms.
   *
   * Output:
   * -NONE: There is no subterm in terms of the form '(\p1, p2. body) (a1, a2)'.
   * -SOME subterm: There is a subterm in terms of the form
   *  '(\p1, p2. body) (a1, a2)'.
   *)
  val has_app_pairs = has_terms_subterm_property is_app_pair

  (* Input:
   * -A term pair_app_term of the form '(\(p1, p2). body) (a1, a2)'.
   *
   * Output:
   * -A theorem of the form
   *  '|- (\(p1, p2). body) (a1, a2) = (\p1 p2. body) a1 a2'.
   *)
  fun app_pair_conv term = PairRules.CURRY_CONV term
    
  (* Rewrites terms in the assumptions and the conclusion of the form
   * '(\(p1, p2). body) (a1, a2)' to '(\p1 p2. body) a1 a2'.
   *)
  val APP_PAIR_TO_CURRY_TAC =
     SPECIFIC_REWRITE_TACTIC_TEMPLATE
     "helper_tactics" "APP_PAIR_TO_CURRY_TAC" "No pair applications in the goal." has_app_pairs app_pair_conv

  (****************************************************************************)
  (*End of lambda abstraction application tactic*******************************)
  (****************************************************************************)



  (****************************************************************************)
  (*Start of let tactic********************************************************)
  (****************************************************************************)

  val has_lets = has_terms_subterm_property (fn term => is_let_scalar term orelse is_let_pair term)

  (* Input:
   * -A term let_term of the form 'let x = e in body'.
   *
   * Output:
   * -A theorem of the form '|- (let x = e in body) = (\f x. f x) (\x. body) e'.
   *)
  fun let_conv term =
    let val (abstraction, argument) = dest_let term
        val let_function = (#2 o dest_eq o concl) LET_DEF in
    let val function = (#1 o dest_abs) let_function in
    let val substitution = match_type (type_of function) (type_of abstraction) in
    let val let_thm0 = INST_TYPE substitution LET_DEF in
    let val let_thm1 = AP_THM let_thm0 abstraction in
    let val let_thm2 = AP_THM let_thm1 argument in
      let_thm2
    end end end end end end

















  (*Start of let scalar reduction tactic.*)

  fun is_lhs_eq_var_in left_term eq = same_term left_term (boolSyntax.lhs eq) andalso (is_var o boolSyntax.rhs) eq

  fun is_var_eq_rhs_in right_term eq = (is_var o boolSyntax.lhs) eq andalso same_term right_term (boolSyntax.rhs eq)

  (*         A ?- t
   * ---------------------var is primed if var is free in A or t.
   * A u {var = term} ?- t
   *
   * Algorithm:
   * |- ?x. x = term    A u {var = term} |- t
   * ----------------------------------------CHOOSE (var)
   *                  A |- t
   *)
  fun ADD_VAR_EQ_TERM_ASM_TAC var term (A, t) =
    let val var = gen_variant is_constname "" (free_varsl (t::A)) var            (* 'var' *)
        val var_eq_term = mk_eq (var, term) in                                   (* 'var = term' *)
    let val A' = var_eq_term::A                                                  (* A u {var = term} ?- t *)
        val t' = t
        val v' = fn thm =>                                                       (* A u {var = term} |- t *)
          (* A u {var = term} |- t
           * ---------------------
           *       A |- t
           *)
          let val xthm = ISPEC term boolTheory.EXISTS_REFL in                        (* '|- ?x. x = term' *)
          let val goal_achieving_thm = CHOOSE (var, xthm) thm in                     (* 'A |- t' *)
            goal_achieving_thm
          end end in
      (A', t', v', var_eq_term)
    end end

  (*         A ?- t
   * ---------------------var is primed if var is free in A or t.
   * A u {term = var} ?- t
   *)
  fun ADD_TERM_EQ_VAR_ASM_TAC var term (A, t) =
    let val (A1, t1, v1, var_eq_term) = ADD_VAR_EQ_TERM_ASM_TAC var term (A, t) in
    let val var = boolSyntax.lhs var_eq_term (* var or a primed version. *)
        val (subgoals2, v2) = REFL_ASM_TAC var_eq_term (A1, t1) in
    let val (A2, t2) = hd subgoals2
        val term_eq_var = mk_eq (term, var) in
      (A2, t2, fn thm => (v1 o v2) [thm], term_eq_var)
    end end end

  fun SINGLE_SUBGOAL (subgoal, validation) =
    let val (A, t) = hd subgoal in
      (A, t, fn thm => validation [thm])
    end

  (*  A ?- t
   * --------
   * A' ?- t'
   *
   * subterm = 'let x = t1 in t2'
   * term = '...let x = t1 in t2...'
   * term = template[subterm/mark]
   * asm_eq = 't1 = t3'
   *
   * subterm' = 'let x = t3 in t2'
   * term' = '...let x = t3 in t2...'
   *)
  fun SUBST_LET_SCALAR_ARG_TAC mark template subterm term asm_eq (A, t) =
    let val (let_function, let_argument) = dest_let subterm in         (* \x. y, z *)
    let val let_argument_mark = genvar_term let_argument in            (* 'let_argument_mark' *)
    let val let_template = mk_let (let_function, let_argument_mark) in (* 'let x = let_argument_mark in z *)
    let val term_template = subst [mark |-> let_template] template in  (* '...let x = let_argument_mark in z...' *)
    let val (A', t', v') = SINGLE_SUBGOAL (SUBST_ASM_OR_CON_TAC asm_eq let_argument_mark term_template term (A, t))
        val r = boolSyntax.rhs asm_eq in                               (* t1, t3 *)
    let val subterm' = subst [let_argument_mark |-> r] let_template in (* let x = t3 in z *)
    let val term' = subst [mark |-> subterm'] template in              (* ...let x = t3 in z... *)
      (A', t', v', subterm', term')
    end end end end end end end

  (* Substitutes a variable for a let argument in a let subterm, if the let
   * argument is not a variable nor longer than 5 characters.
   *
   *  A u {variable = let_argument} ?- t
   * -----------------------------------
   * A' u {variable = let_argument} ?- t'
   *
   * or
   *
   *  A u {let_argument = variable} ?- t
   * -----------------------------------
   * A' u {let_argument = variable} ?- t'
   *
   * or
   *
   *            A ?- t
   * -----------------------------if let_argument = variable nor variable = let_argument occur in A for any variable.
   * A' u {let_argument = x} ?- t'
   *
   * otherwise, the goal is unchanged.
   *
   * template[subterm/mark] = term
   *
   * subterm : 'let x = let_argument in y'
   * term: '...let x = let_argument in y...'
   *
   * subterm': 'let x = variable in y'
   * term': '...let x = variable in y...'
   *
   * A' and t' reflect the rewrite of term which is t or in A.
   *
   * let let_variable = let_argument in let_body
   *)
  fun ADD_RW_LET_SCALAR_ARG_EQ_VAR_ASM_TAC mark template subterm term (A, t) =
    let val (let_function, let_argument) = dest_let subterm in
      if is_var let_argument (*orelse (String.size o term_to_string) let_argument <= 5*) then
        (* The let argument is a variable or short enough that there is no reason
         * to extract the let argument to avoid expanding the finally reduced let
         * term.
         *)
        (A, t, fn thm => thm, subterm, term)
      else
        let val eqs = filter is_eq A in
          case List.find (is_lhs_eq_var_in let_argument) eqs of
            (* let_argument = variable is in A:
             * 1. Substitute variable for let_argument in the let subterm.
             *)
            SOME let_argument_eq_var_asm =>
            SUBST_LET_SCALAR_ARG_TAC mark template subterm term let_argument_eq_var_asm (A, t)
          | NONE =>
            case List.find (is_var_eq_rhs_in let_argument) eqs of
              (* variable = let_argument is in A:
               * 1. Reflect variable = let_arg to let_argument = variable.
               * 2. Substitute variable for let_argument in the let subterm.
               * 3. Restore let_argument = variable to its original "direction":
               *    variable = let_argument.
               *)
              SOME var_eq_let_argument_asm =>
              let val (A1, t1, v1) = SINGLE_SUBGOAL (REFL_ASM_TAC var_eq_let_argument_asm (A, t))
                  val var = boolSyntax.lhs var_eq_let_argument_asm in
              let val let_argument_eq_var_asm = mk_eq (let_argument, var) in
              let val (A2, t2, v2, subterm2, term2) = (SUBST_LET_SCALAR_ARG_TAC mark template subterm term let_argument_eq_var_asm (A1, t1)) in
              let val (A3, t3, v3) = SINGLE_SUBGOAL (REFL_ASM_TAC let_argument_eq_var_asm (A2, t2))
                  val subterm3 = subterm2
                  val term3 = term2 in
                (A3, t3, v1 o v2 o v3, subterm3, term3)
              end end end end
            | NONE =>
              (* Neither let_argument = variable nor variable = let_argument is in A:
               * 1. Add let_argument = let_variable.
               * 2. Substitute let_variable for let_argument in the let subterm.
               * 3. Reflect let_argument = let_variable to let_variable = let_argument.
               *)
              let val let_variable = bvar let_function in
              (* The right hand side variable in let_argument_eq_var_asm may not be
               * the same variable as let_variable in case let_variable occurs free
               * in the goal.
               *)
              let val (A1, t1, v1, let_argument_eq_var_asm) = ADD_TERM_EQ_VAR_ASM_TAC let_variable let_argument (A, t) in
              let val (A2, t2, v2, subterm2, term2) = (SUBST_LET_SCALAR_ARG_TAC mark template subterm term let_argument_eq_var_asm (A1, t1)) in
              let val (A3, t3, v3) = SINGLE_SUBGOAL (REFL_ASM_TAC let_argument_eq_var_asm (A2, t2))
                  val subterm3 = subterm2
                  val term3 = term2 in
                (A3, t3, v1 o v2 o v3, subterm3, term3)
              end end end end
        end
      end

  (* Given 'let x = y in z'
   * returns '|- (let x = y in z) = z[y/x]'.
   *)
  fun scalar_let_conv let_term = 
    let val thm1 = let_conv let_term in
    let val (function, argument) = (dest_comb o boolSyntax.rhs o concl) thm1 in
    let val thm2 = AP_THM (BETA_CONV function) argument in
    let val thm3 = TRANS thm1 thm2 in
    let val thm4 = (BETA_CONV o boolSyntax.rhs o concl) thm3 in
    let val thm5 = TRANS thm3 thm4 in
    let val thm6 = (BETA_CONV o boolSyntax.rhs o concl) thm5 in
    let val thm = TRANS thm5 thm6 in
      thm
    end end end end end end end end

  (* Reduces a scalar let.
   *
   *   A ?- t
   * ----------A'' and t'' reflect the rewrite of term, depending on whether term is t or in A.
   * A'' ?- t''
   *
   * -term = [subterm/mark]template
   * -subterm = 'let x = y in z', where x is not a pair.
   * -term = '...let x = y in z...'
   * -subterm' = 'z[y/x]'
   * -term' = '...z[y/x]...'
   * -No assumptions are added to A if y is shorter than 5 characters or is a
   *  variable, or there is an equation variable = y or y = variable in A.
   *  Otherwise x' = y is added to A, where x is primed if x is free in the goal.
   *)
  fun REDUCE_LET_SCALAR_TAC mark template subterm term (A, t) =
    let val (A1, t1, v1, subterm1, term1) = ADD_RW_LET_SCALAR_ARG_EQ_VAR_ASM_TAC mark template subterm term (A, t) in
    let val rw_thm = scalar_let_conv subterm1 in
    let val (A2, t2, v2, subterm2, term2) = RW_SUBTERM_TAC rw_thm mark template term1 (A1, t1) in
      (A2, t2, v1 o v2, subterm2, term2)
    end end end

  (*End of let scalar reduction tactic.*)








  (*Start of let vector reduction tactic.*)

  (* Inputs:
   * -iterm = 't'
   * -left = 'p1'
   * -right = 'p2'
   *
   * Output: |- ?p1 p2. iterm = (p1, p2)
   *
   * Implements the following proof tree:
   *
   *                                                                                  ---------------------------------ASSUME
   *                                                                                  x = (l, r) |- x = (l, r) thm0
   *                                                                                  ---------------------------------EXISTS 'r'
   *                                                                                  x = (l, r) |- ?r. x = (l, r) thm1
   *                                          ---------------------------ASSUME       ---------------------------------EXISTS 'l'
   *                                          ?b. x = (l, b) |- ?b. x = (l, b) thm2a  x = (l, r) |- ?l r. x = (l, r) thm2b
   * --------------------SPEC 'x' pair_CASES  ----------------------------------------------------------------------------CHOOSE r
   * |- ?a b. x = (a, b) thm3a                ?b. x = (l, b) |- ?l r. x = (l, r) thm3b
   * ---------------------------------------------------------------------------------CHOOSE l
   *                                |- ?l r. x = (l, r) thm4
   *                              ----------------------------GEN 'x'
   *                              |- !x. ?l r. x = (l, r) thm5
   *)
  fun instantiate_named_pair_CASES iterm left right =
    let val l = mk_var ("x", “: 'a # 'b”)
        val component1 = mk_var (term_to_string left, “: 'a”)
        val component2 = mk_var (term_to_string right, “: 'b”) in
    let val r = pairSyntax.mk_pair (component1, component2) in
    let val eq = mk_eq (l, r)
        val (x1, x2) = (pairSyntax.dest_pair o boolSyntax.rhs o #2 o strip_exists o concl o SPEC_ALL) pairTheory.pair_CASES in
    let val xterm2a = mk_exists (x2, mk_eq (l, pairSyntax.mk_pair (component1, x2)))
        val thm0 = ASSUME eq in
    let val thm1 = EXISTS (mk_exists (component2, eq), component2) thm0 in
    let val thm2a = ASSUME xterm2a
        val thm2b = EXISTS (mk_exists (component1, concl thm1), component1) thm1 in
    let val thm3a = SPEC_ALL pairTheory.pair_CASES
        val thm3b = CHOOSE (component2, thm2a) thm2b in
    let val thm4 = CHOOSE (component1, thm3a) thm3b in
    let val thm5 = GEN l thm4 in
      ISPEC iterm thm5
    end end end end end end end end end

  (* Given let_pair = 'let (x1, ..., xn) = (y1, ..., ym) in z'
   * adds the assumption ym = (ym', ym+1), which is also returned.
   *)
  fun ADD_RHS_COMPONENT_LET_PAIR_TAC let_pair (A, t) =
    let val (function, argument) = dest_let let_pair in                             (* '\(x1, x2, x3, x4, x5). t', '(u, v, w)' *)
    let val lhs_components = (pairSyntax.strip_pair o #1 o pairSyntax.dest_pabs) function
        val rhs_components = pairSyntax.strip_pair argument in                      (* '(u, v, w)' *)
    let val component_to_expand = last rhs_components in                            (* 'w' *)
    let fun is_component_eq_expansion eq = same_term (boolSyntax.lhs eq) component_to_expand andalso pairSyntax.is_pair (boolSyntax.rhs eq)
        fun is_expansion_eq_component eq = pairSyntax.is_pair (boolSyntax.lhs eq) andalso same_term (boolSyntax.rhs eq) component_to_expand
        val eqs = filter is_eq A in
      case List.find is_component_eq_expansion eqs of
        SOME expansion => (A, t, fn thm => thm, expansion) (* Expansion already exists among assumption: 'w = (a, b)' *)
      | NONE =>
      case List.find is_expansion_eq_component eqs of
        SOME expansion => (* Expansion already exists among assumption but in opposite direction: '(a, b) = w' *)
        let val (subgoals, validation) = REFL_ASM_TAC expansion (A, t) in
        let val (A', t') = hd subgoals in
          (A', t', fn thm => validation [thm], mk_eq (component_to_expand, boolSyntax.lhs expansion))
        end end
      | NONE =>           (* Expansion does not exist among assumption: Expansion is added. *)
        let val remaining_components_to_expand = List.drop (lhs_components, (length rhs_components) - 1)
            val second_component_name = (last o #1 o strip_exists o #2 o dest_forall o concl) pairTheory.pair_CASES in
        let val l = hd remaining_components_to_expand
            (* r = xn, or r = q, where q will be expanded later. *)
            val r = if length remaining_components_to_expand = 2 then (hd o tl) remaining_components_to_expand else second_component_name in
        let val expansion_thm = instantiate_named_pair_CASES component_to_expand l r in (* '|- ∃q r. w = (q, r)' *)
        let val xterm = concl expansion_thm in                                          (* '?q r. w = (q, r) *)
        let val (iterm, substitution) = instantiate_exists xterm (t::A) in
        let fun prove_x [] iterm thm = thm
              | prove_x ((ivar, xvar)::imap) iterm thm =
                let val xbody = subst [ivar |-> xvar] iterm in
                let val xterm = mk_exists (xvar, xbody) in
                let val lemma = ASSUME xterm in
                let val thm = CHOOSE (ivar, lemma) thm in
                  prove_x imap xterm thm
                end end end end in
        let val validation = fn thm => PROVE_HYP expansion_thm (prove_x substitution iterm thm) in (* One theorem is input. *)
          (iterm::A, t, validation, iterm)
        end end end end end end end
    end end end end

  (* Merges expansions. Instead of
   * A = {..., v = (q, r), r = (q', r'), ...},
   * A = {..., v = (q, q', r'), ...}
   * Returns SOME v = (q, q', r')
   *
   * A = A' u {expansion, new_expansion}.
   *
   * expansion = NONE
   * ----------------
   *   (A, t, id)
   *
   * expansion = SOME (r = (q', ..., r'))
   * new_expansion = r' = (q'', r'')
   * -----------------------------------------------
   * (A' u {r = (q', ..., q'', r'')}, t, validation)
   *)
  fun MERGE_PAIR_EXPANSIONS_TAC NONE             new_expansion (A, t) = (A, t, fn thm => thm, new_expansion)
    | MERGE_PAIR_EXPANSIONS_TAC (SOME expansion) new_expansion (A, t) =
      let val (l, r) = dest_eq expansion
          val (old, new) = dest_eq new_expansion 
          val (subgoals, validation) = RM_ASM_RW_ASM_TAC new_expansion expansion (A, t) in
      let val (A', t') = hd subgoals
          val expansion = mk_eq (l, subst [old |-> new] r) in (* Update current expansion. *)
        (A', t', fn thm => validation [thm], expansion)
      end end

  (*     A u {...let (x1...xn) = (t1...tm) in s...} ?- t              A u {l = r} ?- ...let (x1...xn) = (t1...tm) in s...
   * -------------------------------------------------------- or ------------------------------------------------------------
   * A' u {...let (x1...xn) = (t1...xm', xm+1') in s...} ?- t    A' u {l = r} ?- ...let (x1...xn) = (t1...xm', xm+1') in s...
   *
   * A' = A u {tm = (xm', xm+1')} if tm is a function application (in contrast to
   * a variable; tm cannot be a constant nor an abstraction). Otherwise A' = A.
   *
   * Priority is given to rewriting the conclusion in case let expression exist
   * among assumption and in the conclusion.
   *
   * The occurrence of subterm = 'let (x1...xn) = (t1...tm) in s' in term is
   * denoted by template and mark:
   * template[subterm/mark] = term = '...let (x1...xn) = (t1...tm) in s....'.
   *
   * current_expansion: 
   *
   * Returns:
   * -The rewritten subterm: 'let (x1...xn) = (t1...xm', xm+1') in s'.
   * -The 
   *)
  fun EXPAND_LET_PAIR_TAC mark template subterm term current_expansion (A, t) =
    let val (A1, t1, v1, additional_expansion) = ADD_RHS_COMPONENT_LET_PAIR_TAC subterm (A, t) in
    let val (A2, t2, v2, subterm2, term2) = SUBST_SUBTERM_TAC additional_expansion mark template subterm term (A1, t1) in
    let val (A3, t3, v3, merged_expansion) = MERGE_PAIR_EXPANSIONS_TAC current_expansion additional_expansion (A2, t2) in
      (A3, t3, v1 o v2 o v3, subterm2, term2, merged_expansion)
    end end end

  (*     A u {...let (x1...xn) = (t1...tm) in s...} ?- t
   * -------------------------------------------------------
   * A' u {...let (x1...xn) = (t1...xm'...xn') in s...} ?- t
   *
   * or    
   *
   *     A u {l = r} ?- ...let (x1...xn) = (t1...tm) in s...
   * -----------------------------------------------------------
   * A' u {l = r} ?- ...let (x1...xn) = (t1...xm'...xn') in s...
   *
   * Returns expanded subterm and term:
   * -'let (x1...xn) = (t1...xm'...xn') in s'.
   * -'...let (x1...xn) = (t1...xm'...xn') in s...'.
   *)
(* OLD BUGGY CODE WHICH TREATS ALREADY EXPANDED PAIRS INCORRECTLY.
  fun EXPAND_LET_VECTOR_TAC mark template subterm term (A, t) =
    let fun EXPAND_LET_VECTOR_REC_TAC mark template subterm term current_expansion number_of_expansions (A, t) = 
      if number_of_expansions = 0 then   (* No expansion to make: Terminate recursion. *)
        (A, t, fn thm => thm, subterm, term)
      else
        let val (A1, t1, v1, subterm1, term1, current_expansion) =
              EXPAND_LET_PAIR_TAC mark template subterm term current_expansion (A, t) in
        let val (A2, t2, v2, subterm2, term2) =
              EXPAND_LET_VECTOR_REC_TAC mark template subterm1 term1 (SOME current_expansion) (number_of_expansions - 1) (A1, t1) in
          (A2, t2, v1 o v2, subterm2, term2)
       end end
        val (let_function, let_argument) = dest_let subterm in
    let val number_of_lhs_components = (length o pairSyntax.strip_pair o hd o #1 o pairSyntax.strip_pabs) let_function
        val number_of_rhs_components = (length o pairSyntax.strip_pair) let_argument in
    let val number_of_expansions = number_of_lhs_components - number_of_rhs_components in
      EXPAND_LET_VECTOR_REC_TAC mark template subterm term NONE number_of_expansions (A, t)
    end end end
*)
  fun has_expansion let_pair (A, t) =
    let val (function, argument) = dest_let let_pair in                             (* '\(x1, x2, x3, x4, x5). t', '(u, v, w)' *)
    let val lhs_components = (pairSyntax.strip_pair o #1 o pairSyntax.dest_pabs) function
        val rhs_components = pairSyntax.strip_pair argument in                      (* '(u, v, w)' *)
    let val component_to_expand = last rhs_components in                            (* 'w' *)
    let fun is_component_eq_expansion eq = same_term (boolSyntax.lhs eq) component_to_expand andalso pairSyntax.is_pair (boolSyntax.rhs eq)
        fun is_expansion_eq_component eq = pairSyntax.is_pair (boolSyntax.lhs eq) andalso same_term (boolSyntax.rhs eq) component_to_expand
        val eqs = filter is_eq A in
      case List.find is_component_eq_expansion eqs of
        SOME expansion => SOME (A, t, fn thm => thm, expansion) (* Expansion already exists among assumption: 'w = (a, b)' *)
      | NONE => (
        case List.find is_expansion_eq_component eqs of
          SOME expansion => (* Expansion already exists among assumption but in opposite direction: '(a, b) = w' *)
          let val (subgoals, validation) = REFL_ASM_TAC expansion (A, t)
              val expansion = mk_eq (component_to_expand, boolSyntax.lhs expansion) in
          let val (A, t) = hd subgoals in
            SOME (A, t, fn thm => validation [thm], expansion)
          end end
        | NONE => NONE
        )
    end end end end

  fun EXPAND_LET_VECTOR_TAC mark template subterm term (A, t) =
    let fun EXPAND_LET_VECTOR_REC_TAC mark template subterm term current_expansion number_of_expansions (A, t) = 
      if number_of_expansions = 0 then   (* No expansion to make: Terminate recursion. *)
        (A, t, fn thm => thm, subterm, term)
      else
        let val (A1, t1, v1, subterm1, term1, current_expansion) = EXPAND_LET_PAIR_TAC mark template subterm term current_expansion (A, t) in
        let val current_expansion = SOME current_expansion
            val number_of_expansions = number_of_expansions - 1 in
        let val (A2, t2, v2, subterm2, term2) = EXPAND_LET_VECTOR_REC_TAC mark template subterm1 term1 current_expansion number_of_expansions (A1, t1) in
          (A2, t2, v1 o v2, subterm2, term2)
        end end end
        val (let_function, let_argument) = dest_let subterm in
    let val number_of_lhs_components = (length o pairSyntax.strip_pair o hd o #1 o pairSyntax.strip_pabs) let_function
        val number_of_rhs_components = (length o pairSyntax.strip_pair) let_argument in
    let val number_of_expansions = number_of_lhs_components - number_of_rhs_components
        val current_expansion = NONE in
    let val existing_expansion = has_expansion subterm (A, t) in
      if isSome existing_expansion then (* Expansion already exists among assumption: 'w = (a, b)' or '(a, b) = w' *)
        let val (A1, t1, v1, expansion) = valOf existing_expansion in (* has_expansion reflects (a, b) = w to w = (a, b) *)
        let val (A2, t2, v2, subterm, term) = SUBST_SUBTERM_TAC expansion mark template subterm term (A1, t1) in
          (A2, t2, v1 o v2, subterm, term) (* Nothing to expand. Return input. *)
        end end
      else
        EXPAND_LET_VECTOR_REC_TAC mark template subterm term current_expansion number_of_expansions (A, t)
    end end end end

  (*       A ?- t 
   * ------------------let (x1, ..., xi, ..., xn) = (v1, ..., ti, ..., tn) in e
   * A u {xi = ti} ?- t
   *
   * That is, the leftmost component ti of the right hand side that is not a variable is
   * replaced by a new variable that is xi if xi is not free in A or t, and
   * xi = ti is added as a new assumption.
   *
   * RAISES EXCEPTION IF THERE IS NO RIGHT HAND SIDE COMPONENT THAT IS NOT A
   * VARIABLE NOR A CONSTANT!
   *)
  fun ADD_LET_VAR_EQ_COMPONENT_ASM_TAC let_vector_term (A, t) =
    let val (function, argument) = dest_let let_vector_term in
    let val components_rhs = pairSyntax.strip_pair argument in
    let val components_lhs = (pairSyntax.strip_pair o #1 o pairSyntax.dest_pabs) function in
    let val components_lhs_rhs = zip components_lhs components_rhs in
    let val (xi, ti) = #2 (take_first (not_var_nor_const o #2) components_lhs_rhs) in
    let val selected_variable = gen_variant is_constname "" (free_varsl (t::A)) xi in
    let val xi_eq_ti = mk_eq (selected_variable, ti) in
    let val A' = xi_eq_ti::A
        val validation = fn subgoal_achieving_thm =>
          let val xthm = ISPEC ti boolTheory.EXISTS_REFL in
          let val goal_achieving_thm = CHOOSE (selected_variable, xthm) subgoal_achieving_thm in
            goal_achieving_thm
          end end in
            (A', t, validation, xi_eq_ti)
    end end end end end end end end

  (* A u {l = r, ...let (x1...xn) = (x1...xi-1, r, ..., tn) in y...} ?- t
   * ---------------------------------------------------------------------
   * A u {l = r, ...let (x1...xn) = (x1...xi-1, l, ..., tn) in y...} ?- t
   *
   * or
   *
   * A u {l = r} ?- ...let (x1...xn) = (x1...xi-1, r, ..., tn) in y...
   * -----------------------------------------------------------------
   * A u {l = r} ?- ...let (x1...xn) = (x1...xi-1, l, ..., tn) in y...
   *
   * where:
   * -asm_eq = 'l = r' and r is not a variable nor a constant.
   * -term = '...let (x1...xn) = (x1...xi-1, r, ..., tn) in y...'
   * -subterm = 'let (x1...xn) = (x1...xi-1, r, ..., tn) in y'
   * -template and mark denotes the occurrence of subterm in term:
   *  template[subterm/mark] = term
   *)
  fun SUBST_RHS_LET_COMPONENT_TAC mark template subterm term asm_eq (A, t) =
    let val (l, r) = dest_eq asm_eq
        val (function, argument) = dest_let subterm in
    let val components_rhs = pairSyntax.strip_pair argument in
    let val (preceding_components, component_to_replace, following_components) = take_first not_var_nor_const components_rhs
        val component_mark = genvar_term r in
    let val components_rhs_template = preceding_components @ [component_mark] @ following_components
        val rw_eq_thm = (SYM o ASSUME) asm_eq in
    let val subterm_template = mk_let (function, pairSyntax.list_mk_pair components_rhs_template) in
    let val rw_template = subst [mark |-> subterm_template] template
        val (subgoals1, v1) = ASSUME_TAC rw_eq_thm (A, t) in
    let val (A1, t1) = hd subgoals1
        val rw_eq = concl rw_eq_thm in
    let val (subgoals2, v2) = SUBST_ASM_OR_CON_TAC rw_eq component_mark rw_template term (A1, t1) in
    let val (A2, t2) = hd subgoals2 in
    let val (subgoals3, v3) = REMOVE_ASM_TAC rw_eq (A2, t2) in
    let val (A3, t3) = hd subgoals3
        val subterm3 = subst [component_mark |-> boolSyntax.rhs rw_eq] subterm_template in
    let val term3 = subst [mark |-> subterm3] template in
      (A3, t3, fn thm => v1 [v2 [v3 [thm]]], subterm3, term3)
    end end end end end end end end end end end end

  (*     A u {...let (x1...xn) = (x1...xi-1, ti, ..., tn) in y...} ?- t
   * -----------------------------------------------------------------------
   * A u {...let (x1...xn) = (x1...xi-1, xi, ..., tn) in y..., xi = ti} ?- t
   *
   * or
   *
   *       A ?- ...let (x1...xn) = (x1...xi-1, ti, ..., tn) in y...
   * --------------------------------------------------------------------
   * A u {xi = ti} ?- ...let (x1...xn) = (x1...xi-1, xi, ..., tn) in y...
   *
   * where:
   * -ti is the left most component not being a variable nor a constant.
   * -term = '...let (x1...xn) = (x1...xi-1, ti, ..., tn) in y...'
   * -subterm = 'let (x1...xn) = (x1...xi-1, ti, ..., tn) in y'
   * -template and mark denotes the occurrence of subterm in term:
   *  template[subterm/mark] = term
   *)
(*
  fun ADD_LET_COMPONENT_ABBREV_TAC mark template subterm term (A, t) =
    let val components_rhs = (pairSyntax.strip_pair o #2 o dest_let) subterm in
      if all (not o not_var_nor_const) components_rhs then (* No right hand side is neither a variable nor a constant: Terminate. *)
        (A, t, fn thm => thm, subterm, term)
      else
        let val (A1, t1, v1, var_eq_term) = ADD_LET_VAR_EQ_COMPONENT_ASM_TAC subterm (A, t) in 
        let val (A2, t2, v2, subterm2, term2) = SUBST_RHS_LET_COMPONENT_TAC mark template subterm term var_eq_term (A1, t1) in
          ADD_LET_COMPONENT_ABBREV_TAC mark template subterm2 term2 (A2, t2)
        end end
    end
*)
  fun ADD_LET_COMPONENT_ABBREV_TAC mark template subterm term (A, t) =
    let val components_rhs = (pairSyntax.strip_pair o #2 o dest_let) subterm in
      if all (not o not_var_nor_const) components_rhs then (* No right hand side is neither a variable nor a constant: Terminate. *)
        (A, t, fn thm => thm, subterm, term)
      else
        let val (A1, t1, v1, var_eq_term) = ADD_LET_VAR_EQ_COMPONENT_ASM_TAC subterm (A, t) in 
        let val (A2, t2, v2, subterm2, term2) = SUBST_RHS_LET_COMPONENT_TAC mark template subterm term var_eq_term (A1, t1) in
        let val (A3, t3, v3, subterm3, term3) = ADD_LET_COMPONENT_ABBREV_TAC mark template subterm2 term2 (A2, t2) in
          (A3, t3, v1 o v2 o v3, subterm3, term3)
        end end end
    end

  (* Given a term 'let (x1, ..., xn) = (t1, ..., tn) in t'
   * returns the theorem
   * '|- (let (x1, ..., xn) = (t1, ..., tn) in t) = t[t1, ..., tn/x1, ..., xn]
   *)
  fun paired_let_conv let_term =
    let val eq1_thm = let_conv let_term in
    let val r1 = (boolSyntax.rhs o concl) eq1_thm in
    let val (f1, a1) = dest_comb r1 in
    let val eq2_thm = AP_THM (BETA_CONV f1) a1 in
    let val r2 = (boolSyntax.rhs o concl) eq2_thm in
    let val eq3_thm = BETA_CONV r2 in
    let val eq4_thm = TRANS (TRANS eq1_thm eq2_thm) eq3_thm in
    let val eq5_thm = PairedLambda.PAIRED_BETA_CONV ((boolSyntax.rhs o concl) eq4_thm) in
    let val thm = TRANS eq4_thm eq5_thm in
      thm
    end end end end end end end end end

  (* A u {...let (x1, ..., xn) = (t1, ..., tn) in y...} ?- t
   * -------------------------------------------------------
   *       A u {...y[t1, ..., tn/x1, ..., xn]...} ?- t
   *
   * or
   *
   * A ?- ...let (x1, ..., xn) = (t1, ..., tn) in y...
   * -------------------------------------------------
   * A u {xi = ti} ?- ...y[t1, ..., tn/x1, ..., xn]...
   *
   * where:
   * -term = '...let (x1, ..., xn) = (t1, ..., tn) in y...'
   * -subterm = 'let (x1, ..., xn) = (t1, ..., tn) in y'
   * -template and mark denotes the occurrence of subterm in term:
   *  template[subterm/mark] = term
   *)
  fun REDUCE_EXPANDED_LET_VECTOR_TAC mark template subterm term (A, t) =
    let val rw_eq_thm = paired_let_conv subterm in
      RW_SUBTERM_TAC rw_eq_thm mark template term (A, t)
    end

  (* A u {...let (x1, ..., xn) = (t1, ..., tm) in y...} ?- t
   * -------------------------------------------------------
   *    A u {...vi = ti...} u {...y[...vi/xi...]...} ?- t
   *
   * or
   *
   * A ?- ...let (x1, ..., xn) = (t1, ..., tm) in y...
   * -------------------------------------------------
   *    A u {...vi = ti...} ?- ...y[...vi/xi...]...
   *
   * where:
   * -vi = ti are added assumption in case ti is not a variable nor a constant.
   * -term = '...let (x1, ..., xn) = (t1, ..., tm) in y...'
   * -subterm = 'let (x1, ..., xn) = (t1, ..., tm) in y'
   * -template and mark denotes the occurrence of subterm in term:
   *  template[subterm/mark] = term
   *)
(*
  fun REDUCE_LET_VECTOR_TAC mark template subterm term (A, t) =
    let val (A1, t1, v1, subterm1, term1) = EXPAND_LET_VECTOR_TAC mark template subterm term (A, t) in
    (* This second step is used to prevent the resulting term after let
     * reduction to become uncomprehensible, by keeping the let body intact and
     * add the let equation as assumptions.
     *)
    let val (A2, t2, v2, subterm2, term2) = ADD_LET_COMPONENT_ABBREV_TAC mark template subterm1 term1 (A1, t1) in
    let val (A3, t3, v3, subterm3, term3) = REDUCE_EXPANDED_LET_VECTOR_TAC mark template subterm2 term2 (A2, t2) in
      (A3, t3, v1 o v2 o v3, subterm3, term3)
    end end end
*)
  fun REDUCE_LET_VECTOR_TAC mark template subterm term (A, t) =
    let val (A, t, v1, subterm, term) = EXPAND_LET_VECTOR_TAC mark template subterm term (A, t) in
    let val (A, t, v2, subterm, term) = ADD_LET_COMPONENT_ABBREV_TAC mark template subterm term (A, t) in
    let val (A, t, v3, subterm, term) = REDUCE_EXPANDED_LET_VECTOR_TAC mark template subterm term (A, t) in
      (A, t, v1 o v2 o v3, subterm, term)
    end end end


  (*End of let vector reduction tactic.*)



  (* Reduces let expressions. *)
  val ONCE_LETS_TAC =
    let fun tactic (A, t) =
      case has_lets (t::A) of
        NONE => raise (mk_HOL_ERR "helper_tactics" "ONCE_LETS_TAC" "No let in the goal.")
      | SOME (mark, template, subterm, term) =>
        if is_let_scalar subterm then
          let val (A', t', v', subterm', term') = REDUCE_LET_SCALAR_TAC mark template subterm term (A, t) in
            ([(A', t')], fn thms => (v' o hd) thms)
          end
        else if is_let_pair subterm then
          let val (A', t', v', subterm', term') = REDUCE_LET_VECTOR_TAC mark template subterm term (A, t) in
            ([(A', t')], fn thms => (v' o hd) thms)
          end
        else
          raise (mk_HOL_ERR "helper_tactics" "LETS_TAC" "Has let expression but neither is of scalar or pair form.")
    in
      tactic
    end

  val ONCE_LETS_ASM_TAC =
    let fun tactic (A, t) =
      case has_lets A of
        NONE => raise (mk_HOL_ERR "helper_tactics" "ONCE_LETS_ASM_TAC" "No let in among the assumptions.")
      | SOME (mark, template, subterm, term) =>
        if is_let_scalar subterm then
          let val (A', t', v', subterm', term') = REDUCE_LET_SCALAR_TAC mark template subterm term (A, t) in
            ([(A', t')], fn thms => (v' o hd) thms)
          end
        else if is_let_pair subterm then
          let val (A', t', v', subterm', term') = REDUCE_LET_VECTOR_TAC mark template subterm term (A, t) in
            ([(A', t')], fn thms => (v' o hd) thms)
          end
        else
          raise (mk_HOL_ERR "helper_tactics" "ONCE_LETS_ASM_TAC" "Has let expression but neither is of scalar or pair form.")
    in
      tactic
    end

  val BSIM_ONCE_LETS_TAC =
    let fun tactic (A, t) =
      case has_lets (t::A) of
        NONE => raise (mk_HOL_ERR "helper_tactics" "BSIM_ONCE_LETS_TAC" "No let in the goal.")
      | SOME (mark1, template1, subterm1, term1) =>
      case has_lets (filter (fn term2 => Term.compare (term1, term2) <> EQUAL) (t::A)) of
        NONE => raise (mk_HOL_ERR "helper_tactics" "BSIM_ONCE_LETS_TAC" "Only one let in the goal.")
      | SOME (mark2, template2, subterm2, term2) =>
        if is_let_scalar subterm1 andalso is_let_scalar subterm2 then
          let val (A, t, v1, _, _) = REDUCE_LET_SCALAR_TAC mark1 template1 subterm1 term1 (A, t) in
          let val (A, t, v2, _, _) = REDUCE_LET_SCALAR_TAC mark2 template2 subterm2 term2 (A, t) in
            ([(A, t)], fn thms => (v1 o v2 o hd) thms)
          end end
        else if is_let_pair subterm1 andalso is_let_pair subterm2 then
          let val (A, t, v1, _, _) = REDUCE_LET_VECTOR_TAC mark1 template1 subterm1 term1 (A, t) in
          let val (A, t, v2, _, _) = REDUCE_LET_VECTOR_TAC mark2 template2 subterm2 term2 (A, t) in
            ([(A, t)], fn thms => (v1 o v2 o hd) thms)
          end end
        else
          raise (mk_HOL_ERR "helper_tactics" "BSIM_ONCE_LETS_TAC" "Two lets of different kind: One scalar and once vector.")
    in
      tactic
    end

  val LETS_TAC =
    let fun tactic (A, t) =
      case has_lets (t::A) of
        NONE => raise (mk_HOL_ERR "helper_tactics" "LETS_TAC" "No let in the goal.")
      | SOME (mark, template, subterm, term) =>
        if is_let_scalar subterm then
          let val (A', t', v', subterm', term') = REDUCE_LET_SCALAR_TAC mark template subterm term (A, t) in
            ([(A', t')], fn thms => (v' o hd) thms)
          end
        else if is_let_pair subterm then
          let val (A', t', v', subterm', term') = REDUCE_LET_VECTOR_TAC mark template subterm term (A, t) in
            ([(A', t')], fn thms => (v' o hd) thms)
          end
        else
          raise (mk_HOL_ERR "helper_tactics" "LETS_TAC" "Has let expression but neither is of scalar or pair form.")
    in
      tactic THEN (REPEAT tactic)
    end

  (****************************************************************************)
  (*End of let tactic**********************************************************)
  (****************************************************************************)







  (****************************************************************************)
  (*Start of case pattern tactic***********************************************)
  (****************************************************************************)

  (* Input: A term.
   *
   * Output:
   * -False: term is not of the form 'case pattern x1...xn of t'.
   * -True: term is of the form 'case pattern x1...xn of t'.
   *)
  fun is_case_pattern term =
    if TypeBase.is_case term then
      let val bodies = (#2 o strip_comb) term in
      let val pattern = hd bodies in
      let val function = (#1 o strip_comb) pattern in
        TypeBase.is_constructor function
      end end end
    else
      false

  (* Input:
   * -A term term.
   *
   * Output:
   * -NONE: No subterm of the form 'case pattern x1...xn of t'.
   * -SOME term: There is a subterm of the form 'case pattern x1...xn of t'.
   *)
  val has_case_pattern = has_terms_subterm_property is_case_pattern

  (* Input:
   * -A term of the form 'case pattern x1...xn of t.
   *
   * Output:
   * -A theorem of the form '|- case pattern x1...xn of t1 = f x1...xn'.
   *)
  fun case_pattern_conv term =
    let val (case_function, case_term_bodies) = strip_comb term in
    let val case_def_thm = (TypeBase.case_def_of o type_of o hd) case_term_bodies
        fun find_matching thm = match_term ((boolSyntax.lhs o #2 o strip_forall o concl) thm) term in
    let fun is_definition thm = let val _ = find_matching thm in true end handle _ => false in
    let val case_thm =
      case List.find is_definition (CONJUNCTS case_def_thm) of
        NONE => raise (mk_HOL_ERR "helper_tactics" "case_pattern_conv" "Could not find relevant case theorem in database.")
      | SOME thm => thm in
    let val instantiated_thm = INST_TY_TERM (find_matching case_thm) (SPEC_ALL case_thm) in
      instantiated_thm
    end end end end end

  (* Rewrites terms in the assumptions and the conclusion of the form
   * 'case pattern x1..xn of p1 -> f1 x1...xn | ... | pm -> fm x1...xn' to
   * 'fi x1...xn' if pattern x1...xn matches pattern pi.
   *)
  val CASE_PATTERN_TO_APP_TAC =
    let fun tactic (A, t) =
          case has_case_pattern (t::A) of
            NONE => raise (mk_HOL_ERR "helper_tactics" "CASE_PATTERN_TO_APP_TAC" "No subterm of the form: case pattern x1..xn of t.")
          | SOME (mark, template, subterm_with_property, term) =>
              let val rewrite_thm = GEN_ALL (case_pattern_conv subterm_with_property) in
                ETAC rewrite_thm (A, t)
              end
    in
      tactic THEN (REPEAT tactic)
    end

  (* Reduces case expressions when matching a pattern (data constructor).
   * The last CASE_PATTERN_TO_APP_TAC is necessary if there is no application due
   * to the case pattern having no variables.
   *)
  val CASE_PATTERN_TAC = REPEAT (CASE_PATTERN_TO_APP_TAC THEN APP_SCALAR_TAC) THEN REPEAT CASE_PATTERN_TO_APP_TAC

  (****************************************************************************)
  (*End of case pattern tactic*************************************************)
  (****************************************************************************)



  (****************************************************************************)
  (*Start of If-then-else tactic***********************************************)
  (****************************************************************************)

  (* Input:
   * -A list of terms assumptions.
   * -A term term.
   *
   * Output:
   * -False: term is not of the form 'if t0 then t1 else t2'.
   * -True: term is of the form 'if t0 then t1 else t2' and there is a term in
   *  assumptions of the form 't0' or '~t0'.
   *)
  fun is_if_then_else assumptions term =
    if is_cond term then
      let val cond = (#1 o dest_cond) term in
        if (not o is_neg) cond then
          exists (same_term cond) assumptions orelse
          exists (same_term (mk_neg cond)) assumptions
        else
          exists (same_term cond) assumptions orelse
          exists (same_term (dest_neg cond)) assumptions
      end
    else
      false

  (* Input:
   * -A list of terms assumptions.
   * -A list of terms.
   *
   * Output:
   * -NONE: There is no subterm in terms of the form 'if t0 then t1 else t2' with
   *  a term in the assumptions of the form 't0' or '~t0'.
   * -SOME subterm: There is a subterm in terms of the form
   *  'if t0 then t1 else t2' and a term in the assumptions of the form 't0' or
   *  '~t0'.
   *)
  fun has_if_then_else assumptions = has_terms_subterm_property (is_if_then_else assumptions)

  (* True branch: a |- if a then t1 else t2 = t1 *)
  fun assumption_eq_condition_branch_thm condition = 
    let val EQ_thm = case
      List.find
        (fn thm => Term.compare ((#2 o dest_eq o #2 o dest_eq o concl) thm, “T”) = EQUAL)
        (map SYM (CONJUNCTS (SPEC condition EQ_CLAUSES)))
    of
      NONE => fail (print "Could not find relevant equality clause")
    | SOME thm => thm
        val place_holder_variable = gen_variant is_constname "" (free_varsl [condition]) “x: bool”
        val condition_thm = ASSUME condition in
    let val condition_eq_T_thm = SUBST [place_holder_variable |-> EQ_thm] place_holder_variable condition_thm in
      condition_eq_T_thm
    end end

  (* False branch:  a |- if ~a then t1 else t2 = t2 *)
  fun neg_assumption_eq_condition condition =
    let val EQ_thm = case           (* [a] | a = (a = T) *)
      List.find
        (fn thm => Term.compare ((#2 o dest_eq o #2 o dest_eq o concl) thm, “T”) = EQUAL)
        (map SYM (CONJUNCTS (SPEC (dest_neg condition) EQ_CLAUSES)))
      of
        NONE => fail (print "Could not find relevant equality clause")
      | SOME thm => thm
        val place_holder_variable = gen_variant is_constname "" (free_varsl [condition]) “x: bool”
        val assumption_thm = ASSUME (dest_neg condition) in
    let val assumption_eq_T_thm = SUBST [place_holder_variable |-> EQ_thm] place_holder_variable assumption_thm in (* [a] |- a = T *)
    let val neg_assumption_eq_neg_T_thm = MK_COMB (REFL “$~”, assumption_eq_T_thm) (* [a] | ~a = ~T *)
        val neg_T_eq_F_thm =
          case List.find (fn thm => Term.compare (concl thm, “~T = F”) = EQUAL) (CONJUNCTS NOT_CLAUSES) of
            NONE => fail (print "Could not find the theorem ~T = F")
          | SOME thm => thm in
    let val assumption_implies_condition_eq_F_thm = TRANS neg_assumption_eq_neg_T_thm neg_T_eq_F_thm in
      assumption_implies_condition_eq_F_thm
    end end end end

  (* False branch: ~a |- if a then t1 else t2 = t2 *)
  fun assumption_eq_neg_condition condition =
    let val EQ_thm = case        (* [~a] | ~a = (a = F) *)
          List.find
            (fn thm => Term.compare ((#2 o dest_eq o #2 o dest_eq o concl) thm, “F”) = EQUAL)
            (map SYM (CONJUNCTS (SPEC condition EQ_CLAUSES)))
          of
            NONE => fail (print "Could not find relevant equality clause")
          | SOME thm => thm
        val place_holder_variable = gen_variant is_constname "" (free_varsl [condition]) “x: bool”
        val assumption_thm = ASSUME (mk_neg condition) in
    let val assumption_implies_condition_eq_F_thm =
          SUBST [place_holder_variable |-> EQ_thm] place_holder_variable assumption_thm in (* [~a] |- a = F *)
      assumption_implies_condition_eq_F_thm
    end end

  (* Input:
   * -A term assumption of the form 'a' or '~a'.
   * -A term if_then_else of the form 'if c then t1 else t2'.
   *
   * Output:
   * -A theorem of the form 'a |- if c then t1 else t2 = t', where
   *  *if a = c: t = t1.
   *  *if a = ~c or ~a = c: t = t2.
   *)
  fun if_then_else_equality_thm assumption if_then_else =
    let val (condition, then_branch, else_branch) = dest_cond if_then_else in
    let val (if_then_else_eq_bool_thm, conjunct) =
      if (not o is_neg) assumption andalso is_neg condition then      (* False branch:  a |- if ~a then t1 else t2 = t2 *)
        (neg_assumption_eq_condition condition, CONJUNCT2)
      else if is_neg assumption andalso (not o is_neg) condition then (* False branch: ~a |- if  a then t1 else t2 = t2 *)
        (assumption_eq_neg_condition condition, CONJUNCT2)
      else                                                            (* True branch:   a |- if  a then t1 else t2 = t1 *)
        (assumption_eq_condition_branch_thm condition, CONJUNCT1)
        val conditional_id_thm = REFL if_then_else
        val place_holder_variable = gen_variant is_constname "" (free_varsl [if_then_else]) “x: bool”
        val type_instantiated_cond = inst [alpha |-> type_of if_then_else] “COND” in
    let val subst_template_term =
      mk_eq (if_then_else, list_mk_comb (type_instantiated_cond, [place_holder_variable, then_branch, else_branch])) in
    let val conditional_eq_thm = SUBST [place_holder_variable |-> if_then_else_eq_bool_thm] subst_template_term conditional_id_thm in
    let val conditional_eq_branch_thm = TRANS conditional_eq_thm (conjunct (ISPECL [then_branch, else_branch] COND_CLAUSES)) in
      conditional_eq_branch_thm
    end end end end end

  (* Input:
   * -A list of terms assumptions
   * -A term if_then_else_term of the form 'if t0 then t1 else t2'.
   *
   * Output:
   * -A theorem of the form
   *  *' t0 |- if  t0 then t1 else t2 = t1',
   *  *'~t0 |- if  t0 then t1 else t2 = t2',
   *  *'~t0 |- if ~t0 then t1 else t2 = t1', or
   *  *' t0 |- if ~t0 then t1 else t2 = t2',
   *  depending on whether there is a term in assumptions of the form 't0', or
   *  '~t0', and whether 't0' is of the form '~t' or 't' respectively.
   *)
  fun if_then_else_conv assumptions if_then_else =
    let val (cond, then_branch, else_branch) = dest_cond if_then_else in
    let val assumption =
      if (not o is_neg) cond then
        case List.find (fn assumption => Term.compare (assumption, cond) = EQUAL) assumptions of
          NONE => (case List.find (fn assumption => Term.compare (assumption, mk_neg cond) = EQUAL) assumptions of
                     NONE => fail (print "No assumption matches condition in if-then-else term.\n")
                   | SOME assumption => assumption
                  )
        | SOME assumption => assumption
      else
        case List.find (fn assumption => Term.compare (assumption, cond) = EQUAL) assumptions of
          NONE => (case List.find (fn assumption => Term.compare (assumption, dest_neg cond) = EQUAL) assumptions of
                     NONE => fail (print "No assumption matches condition in if-then-else term.\n")
                   | SOME assumption => assumption
                  )
        | SOME assumption => assumption in
    let val if_then_else_thm = if_then_else_equality_thm assumption if_then_else in
      if_then_else_thm
    end end end

  (* Rewrites terms in the assumptions and the conclusion of the form
   * 'if t0 then t1 else t2' to 't1' or 't2', depending on whether there is an
   * assumption of the form 't0' or '~t0'.
   *)
  fun COND_TAC (asl, con) =
    SPECIFIC_REWRITE_TACTIC_TEMPLATE
      "helper_tactics"
      "COND_TAC"
      "No if-then-else in the assumptions or the goal, with the condition or its negation among the assumptions."
      (has_if_then_else asl) (if_then_else_conv asl) (asl, con)







  fun is_cond_id term =
    if is_cond term then
      let val cond = (#1 o dest_cond) term in
        if is_eq cond then same_term (boolSyntax.lhs cond) (boolSyntax.rhs cond) else false
      end
    else
      false

  fun has_id_cond terms = has_terms_subterm_property is_cond_id terms

  (* Input: 'if x = x then t1 else t2'
   * Output: '|- (if x = x then t1 else t2) = t1'
   *)
  fun cond_id_conv if_then_else =
    let val (cond, then_branch, else_branch) = dest_cond if_then_else in
    let val x = boolSyntax.lhs cond
        val if_eq_if_thm = REFL if_then_else in
    let val x_eq_x_equiv_T_thm = ISPEC x boolTheory.REFL_CLAUSE
        val mark = genvar_term cond in
    let val template = mk_eq (if_then_else, mk_cond (mark, then_branch, else_branch)) in
    let val thm1 = SUBST [mark |-> x_eq_x_equiv_T_thm] template if_eq_if_thm
        fun is_true_if_then_else thm = same_term T ((#1 o dest_cond o boolSyntax.lhs o concl o SPEC_ALL) thm) in
    let val thm2 = 
      case List.find is_true_if_then_else (CONJUNCTS boolTheory.bool_case_thm) of
        NONE => raise (mk_HOL_ERR "helper_tactics" "" "Cannot happen")
      | SOME thm => ISPECL [then_branch, else_branch] thm in
    let val thm = TRANS thm1 thm2 in
      thm
    end end end end end end end

  (* subterm:  'if x = x then t1 else t2'
   * subterm': 't1'
   *)
  fun COND_ID_TAC (A, t) = 
    case has_id_cond (t::A) of
      NONE => raise (mk_HOL_ERR "helper_tactics" "COND_ID_TAC" "NO if-then-else term if identity condition.")
    | SOME (mark, template, subterm, term) => (* subterm: 'if x = x then t1 else t2' *)
      let val subterm_eq_thm = cond_id_conv subterm in
      let val (A', t', v', subterm', term') = RW_SUBTERM_TAC subterm_eq_thm mark template term (A, t) in
        ([(A', t')], v' o hd)
      end end


  val CONDS_TAC = COND_TAC ORELSE COND_ID_TAC

  (****************************************************************************)
  (*End of If-then-else tactic*************************************************)
  (****************************************************************************)



  (****************************************************************************)
  (*Start of If-then-else tactic that splits the goal based on the condition.**)
  (****************************************************************************)

  (* Transforms a goal of the form 'A u {... if x then y else z ...} |- t' to
   * two subgoal of the form 'A u {y} | t' and 'A u {z} |- t', and similarly if
   * the conditional is in the conclusion t.
   *)
  val IF_SPLIT_TAC =
    let fun split_if_then_else_tactic (A, t) =
      case has_terms_subterm_property is_cond (t::A) of
        NONE => fail (print "No if-then-else statement in the assumptions nor the goal.\n")
      | SOME (mark, template, subterm_with_property, term) =>
        let val condition_term = (#1 o dest_cond) subterm_with_property in
        let val (unnegated_condition_term, negated_condition_term) =
          if is_neg condition_term then
            (dest_neg condition_term, condition_term)
          else
            (condition_term, mk_neg condition_term) in
        let val A1' = unnegated_condition_term::A
            val A2' = negated_condition_term::A in
        let val subgoals = [(A1', t), (A2', t)]
            val validation_function =
          (fn thms =>
             let val thm0 = ISPEC unnegated_condition_term EXCLUDED_MIDDLE
                 val thm1 = hd thms                 (* A u { t} |- g *)
                 val thm2 = (hd o tl) thms in       (* A u {~t} |- g *)
             let val achieving_thm = DISJ_CASES thm0 thm1 thm2 in
               achieving_thm
             end end
          ) in
          (subgoals, validation_function)
        end end end end in
      split_if_then_else_tactic THEN COND_TAC
    end

  (****************************************************************************)
  (*End of If-then-else tactic that splits the goal based on the condition.****)
  (****************************************************************************)



  (****************************************************************************)
  (*State of tactic that splits the goal based on new equality.****************)
  (****************************************************************************)

  (*                                  A ?- t
   * -------------------------------------------------------------------
   * A[r_name/l_name] ?- t[r_name/l_name]    A u {l_name <> r_name} ?- t
   *)
  fun CASE_EQ_TAC l_name r_name (A, t) =
    let val l =
      case has_terms_subterm_property (fn t => term_to_string t = l_name) (t::A) of
        NONE => raise (mk_HOL_ERR "helper_tactics" "CASE_EQ_TAC" "Left hand side term does not exist.")
      | SOME (_, _, l, _) => l
        val r =
      case has_terms_subterm_property (fn t => term_to_string t = r_name) (t::A) of
        NONE => raise (mk_HOL_ERR "helper_tactics" "CASE_EQ_TAC" "Right hand side term does not exist.")
      | SOME (_, _, r, _) => r in
    let val l_eq_r = mk_eq (l, r) in
    let val l_neq_r = mk_neg l_eq_r in
    let val (subgoals1, v1) = ASM_RW_OTHERS_TAC false l_eq_r (l_eq_r::A, t) in
    let val (A1, t1) = hd subgoals1
        val (A2, t2) = (l_neq_r::A, t)
        val validation = fn thms => 
          let val thm1 = v1 [hd thms]
              val thm2 = last thms
              val thm1_or_thm2 = ISPEC l_eq_r boolTheory.EXCLUDED_MIDDLE in
          let val thm = DISJ_CASES thm1_or_thm2 thm1 thm2 in
            thm
          end end in
      ([(A1, t1),(A2, t2)], validation)
    end end end end end

  (****************************************************************************)
  (*End of tactic that splits the goal based on new equality.******************)
  (****************************************************************************)



  (****************************************************************************)
  (*Start of tuple expansion tactic********************************************)
  (****************************************************************************)

  (* Input: A term of the form '\(c1, ..., cn). e'.
   * Output: A list of the form [c1, ..., cn].
   *)
  fun extract_let_components term =
    if is_abs term then
      [(#1 o dest_abs) term]
    else
      let val (component, term) = (dest_abs o #2 o dest_comb) term in
        component::(extract_let_components term)
      end

  (* Input: A term.
   * Output:
   * -False: Term is not of the form '(c1, ..., cn) = x', where x is a variable,
   *  nor of the form '(c1, ..., cn) = function a1...an'.
   * -True: Term is of the form '(c1, ..., cn) = x', where x is a variable, or of
   *  the form '(c1, ..., cn) = function a1...an'.
   *)
  fun is_eq_folded_term term =
    if is_eq term then
      let val (lhs, rhs) = dest_eq term in
      let val more_components_on_lhs = (length o pairSyntax.strip_pair) lhs > (length o pairSyntax.strip_pair) rhs in
      let val not_case_on_rhs = (not o TypeBase.is_case) rhs
          val not_if_on_rhs = (not o is_cond) rhs
          val not_let_on_rhs = (not o is_let) rhs in
        more_components_on_lhs andalso not_case_on_rhs andalso not_if_on_rhs andalso not_let_on_rhs
      end end end
    else
      false

  (* Input: A list of terms.
   * Output: SOME subterm if there is a subterm of a term in terms of the form
   * '(c1, ..., cn) = t', where t is a variable or function application but not a
   * let, case or if term. Otherwise NONE.
   *)
  val has_eq_folded_terms = has_terms_subterm_property is_eq_folded_term

  (* Input: A term.
   * Output: True if and only if term is of the form
   * 'let (x1, ..., xn) = (c1, ..., cm)', where n > m and it is possible that
   * m = 1.
   *)
  fun is_let_folded_term let_exp =
    if is_let let_exp then
      let val (term, argument) = dest_let let_exp in
        if is_comb term then
          if (term_to_string o #1 o dest_comb) term = "UNCURRY" then
            let val components_lhs = extract_let_components term
                val components_rhs = pairSyntax.strip_pair argument in
              length components_lhs > length components_rhs
            end
          else
            false
        else
          false
      end
    else
      false

  (* Input: A list of terms.
   * Output: SOME subterm if there is a subterm of a term in terms of the form
   * 'let (c1, ..., cn) = t', and if t is a tuple then its number of components
   * is less than n. Otherwise NONE.
   *)
  val has_let_folded_terms = has_terms_subterm_property is_let_folded_term

  (* Input: “(c1, ..., cn) = (v1, ..., vm)”
   * Output: vm.
   *)
  fun eq_unfolded_tuple term =
    let val rhs = (#2 o dest_eq) term in
    let val components_rhs = pairSyntax.strip_pair rhs in
      last components_rhs
    end end

  (* Input: “let (c1, ..., cn) = (v1, ..., vm) in e”.
   * Output: vm.
   *)
  fun let_unfolded_tuple term =
   let val rhs = (#2 o dest_let) term in
   let val components_rhs = pairSyntax.strip_pair rhs in
     last components_rhs
   end end

  (* Input:
   * -lhs = '[c1, ..., cn]’
   * -rhs = '[v1, ..., vm]',
   * where it is possible that m = 1, and necessary that m < n.
   *
   * Output:
   * -'[cm, cm+1]': if n = m + 1.
   * -'[cm]': if n > m + 1.
   *)
  fun instantiation_terms lhs rhs =
    if length lhs = length rhs + 1 then
      List.drop (lhs, length lhs - 2)
    else
      [List.nth (lhs, length rhs - 1)]

  (* Input:
   * -A term term_to_unfold: A term on the right-hand side of a let-expression or
   *  equality with a left-hand side being a tuple.
   * -A list term_subsitutions: The term t to unfold is replaced by the pair
   *  whose first component is the head of term_substitutions, and if
   *  term_substitutions contains one element, the second component is the
   *  quantified variable of the existential theorem stating that t is equal to
   *  some pair of variables, and otherwise the second component is the second
   *  element of term_substitutions.
   * -A goal (A, t).
   *
   * Output:
   * -(A', t'): Subgoal with term_to_unfold replaced by its pair expansion.
   * -validation_function: Given a theorem achieving (A', t'), returns a theorem
   *  achieving (A, t).
   *
   * Summary: Transforms a goal of the form '(c1, ..., cn) = (v1, ..., vm)' to
   * '(c1, ..., cn) = (v1, ..., vm, vm+1)'
   *)
  fun unfold_term term_to_unfold term_substitutions (A, t) =
    (* subgoal *)
    let val xthm = ISPEC term_to_unfold pairTheory.ABS_PAIR_THM in
    let val xterm0 = concl xthm in
    let val instantiation_left = hd term_substitutions in
    let val (component_left, variable_left, xterm1) = case instantiate_specified_exist xterm0 instantiation_left (t::A) of
        NONE => fail (print "Cannot happen!\n")
      | SOME instantiation => instantiation in
    let val specified_instantiation_right =
      if length term_substitutions = 1 then
        instantiate_exist xterm1 (free_varsl (t::A))
      else
        instantiate_specified_exist xterm1 (last term_substitutions) (t::A) in
    let val (component_right, variable_right, xterm2) = case specified_instantiation_right of
        NONE => fail (print "Cannot happen!\n")
      | SOME instantiation => instantiation in
    let val instantiation_pair = pairSyntax.mk_pair (component_left, component_right)
        val term_to_unfold_eq_instantiation_pair = mk_eq (term_to_unfold, instantiation_pair) in
    let val A' = term_to_unfold_eq_instantiation_pair::(substitute_terms A term_to_unfold instantiation_pair)
        val t' = substitute_term t term_to_unfold instantiation_pair in
    (* validation:
     * -Input: achieving_thm = 'A[(v1, v2)/x] u {x = (v1, v2)} |- t[(v1, v2)/x]'
     * -Output: A |- t
     *)
    let val validation_function =
      (fn achieving_thms =>
         let val B_thm = hd achieving_thms (* One subgoal gives one theorem. *)
             val term_to_unfold_eq_instantiation_pair = mk_eq (term_to_unfold, instantiation_pair) in
         let val new_term_eq_old_term_thm = SYM (ASSUME term_to_unfold_eq_instantiation_pair) in
         let val back_substituted_thm = reverse_substitute (term_to_unfold_eq_instantiation_pair::A, t) B_thm new_term_eq_old_term_thm
             val inst_var_map = [(component_right, variable_right), (component_left, variable_left)] in
         let val xthm_thm = choose_applications inst_var_map term_to_unfold_eq_instantiation_pair back_substituted_thm in
         let val achieving_thm = PROVE_HYP xthm xthm_thm in
           achieving_thm
         end end end end end) in
      ([(A', t')], validation_function)
    end end end end end end end end end

  (* Transforms terms of the form (c1, ..., cn) = (v1, ..., vm) to
   * (c1, ..., cn) = (v1, ..., vm, ..., vn), including let expression.
   *)
  val UNFOLD_TUPLE_VARS_TAC =
    let fun tactic (A, t) =
          case has_eq_folded_terms (t::A) of
            NONE => (
              case has_let_folded_terms (t::A) of
                NONE => raise (mk_HOL_ERR "helper_tactics" "UNFOLD_TERM_TAC" "No equality with right hand side to unfold.")
              | SOME (mark, template, subterm_with_property, term) =>
                let val term_to_unfold = let_unfolded_tuple subterm_with_property in
                let val lhs_components = (extract_let_components o #1 o dest_let) subterm_with_property in
                let val term_substitutions =
                      instantiation_terms lhs_components ((pairSyntax.strip_pair o #2 o dest_let) subterm_with_property) in
                  unfold_term term_to_unfold term_substitutions (A, t)
                end end end
            )
          | SOME (mark, template, subterm_with_property, term) =>
            let val term_to_unfold = eq_unfolded_tuple subterm_with_property in
            let val lhs_components = (pairSyntax.strip_pair o #1 o dest_eq) subterm_with_property in
            let val term_substitutions =
                  instantiation_terms lhs_components ((pairSyntax.strip_pair o #2 o dest_eq) subterm_with_property) in
              unfold_term term_to_unfold term_substitutions (A, t)
            end end end in
    let fun remove_equalities_tactic (A, t) =
      let fun is_redundant_equality term =
        if is_eq term then
          let val (lhs, rhs) = dest_eq term in
          let val lhs_is_variable = is_var lhs
              val rhs_is_tuple = pairSyntax.is_pair rhs in
            if lhs_is_variable andalso rhs_is_tuple then
              let val free_variables = free_varsl (t::A)
                  fun equal_terms term1 term2 = Term.compare (term1, term2) = EQUAL in
              let val lhs_occurrences = foldl (fn (variable, n) => if equal_terms variable lhs then n + 1 else n) 0 free_variables in
                lhs_occurrences = 1
              end end
            else
              false
          end end
        else
          false in
      let val A' = List.filter (not o is_redundant_equality) A in
        ([(A', t)], (fn thms => hd thms))
      end end in
      tactic THEN (REPEAT tactic) THEN remove_equalities_tactic
    end end

  (****************************************************************************)
  (*End of tuple expansion tactic**********************************************)
  (****************************************************************************)



  (****************************************************************************)
  (*Start of case splitting tactic*********************************************)
  (****************************************************************************)

  (* 'A u {?x1...xn. l = r} |- t' + '?x1...xn. l = r' (n may be 0: n = 0)
   * ==>
   * 'A u {l = r}[v1...vn/x1...xn] |- t' + (l = r)[v1...vn/x1...xn]
   *)
  fun ELIM_EXISTS_ASM_TAC xterm (A, t) =
    if (not o is_exists) xterm then
      ([(A, t)], fn thms => hd thms, xterm)
    else
      let val (ibody, imap) = instantiate_exists xterm (t::A) in
      let val subgoals = [(ibody::filter (fn ass => Term.compare (ass, xterm) <> EQUAL) A, t)]
          val validation = fn thms =>
            let val ibodyA_t_thm = hd thms
                fun prove_xgoal [] iterm thm = thm
                  | prove_xgoal ((ivar, xvar)::imap) iterm thm =
                      let val xbody = subst [ivar |-> xvar] iterm in
                      let val xterm = mk_exists (xvar, xbody) in
                      let val lemma = ASSUME xterm in
                      let val thm = CHOOSE (ivar, lemma) thm in
                        prove_xgoal imap xterm thm
                      end end end end in
            let val xtermA_t_thm = prove_xgoal imap ibody ibodyA_t_thm in
              xtermA_t_thm
            end end in
        (subgoals, validation, ibody)
      end end

  (* 'A u {...(f1 ...l...)..., ..., ...(fn ...l...)..., l = r} |- t' + 'l = r'
   * ==>
   * 'A u {...(f1 ...r...)..., ..., ...(fn ...r...)..., l = r} |- t'
   *)
  fun KEEP_ASM_RW_ASMS_TAC asm_eq : tactic =
    let fun tactic (A, t) =
      let val other_assumptions = filter (fn assumption => Term.compare (assumption, asm_eq) <> EQUAL) A
          val (l, r) = dest_eq asm_eq in
            case List.find (fn other_assumption => is_subterm l other_assumption) other_assumptions of
              NONE =>
                raise (mk_HOL_ERR "helper_tactics" "KEEP_ASM_RW_ASMS_TAC" "No other assumption has the left hand side as a subterm.")
            | SOME asm_to_rw => ASM_RW_ASM_TAC true asm_eq asm_to_rw (A, t)
      end in
      tactic THEN REPEAT tactic
    end

  (* 'A u {l = r} |- t' + 'l = r'
   * ==>
   * 'A |- t[r/l]'
   *)
  fun RM_ASM_RW_GOAL_TAC asm_eq : tactic =
    let fun tactic (A, t) = ([(filter (fn assumption => Term.compare (assumption, asm_eq) <> EQUAL) A, t)], fn thms => hd thms) in
      SUBST_TAC [ASSUME asm_eq] THEN tactic
    end

  (* 'A u {l = r} |- t' + 'l = r'
   * ==>
   * 'A u {l = r} |- t[r/l]'
   *)
  fun KEEP_ASM_RW_GOAL_TAC asm_eq : tactic = SUBST_TAC [ASSUME asm_eq]

  (* 'A u B |- t'
   * ==>
   * 'A u C1 |- s1' + ... + 'A u Cm |- sm'
   *
   * where B = {... (case x of p1 => t1 | ... | pn => tn) ...} or
   * t = '... (case x of p1 => t1 | ... | pn => tn) ...' and
   * Ci = {...ti...} or si = '...ti...'
   *)
  fun SPLIT_SCALAR_CASE_PATTERN_TAC rm_asms (A, t) =
    let val (a_or_t, scalar_case_subterm) =
      case has_terms_subterm_property (fn term => TypeBase.is_case term andalso not (pairSyntax.is_pair_case term)) (t::A) of
        NONE => raise (mk_HOL_ERR "helper_tactics" "SPLIT_SCALAR_CASE" "No scalar case among assumptions nor conclusion.")
      | SOME (mark, template, subterm_with_property, term) => (term, subterm_with_property) in
    let val case_expression = (#2 o TypeBase.dest_case) scalar_case_subterm in
    let val case_type_name = (#1 o dest_type o type_of) case_expression in
    let val nchotomy_thm_name = concat [case_type_name, "_nchotomy"] in
    let val nchotomy_thm = (#1 o #2 o hd o find) nchotomy_thm_name in
    let val inst_case_thm = ISPEC case_expression nchotomy_thm in
    let val case_terms = (strip_disj o concl) inst_case_thm in
    (* Adds existential equality as assumption to each case. *)
    let val case_term_subgoals = map (fn case_term => (case_term, (case_term::A, t))) case_terms in
    (* Adds instantiated equalities as assumption for each case.*)
    let val inst_eq_subgoal_validation_eqs =
      map (fn (case_term, subgoal) => ELIM_EXISTS_ASM_TAC case_term subgoal) case_term_subgoals in
    (* Rewrites assumptions and the conclusion with the instantiated equality and removes the instantiated equality for each case.*)
    let val elim_eq_subgoal_validations =
      if rm_asms then (* Remove new equalities x = pi due to pattern expansion in 'case x of ...' *)
        (*TRY is used for the situation in which the expanded term in the case condition does not occur among the assumptions. *)
        map (fn (subgoals, _, eq) => (TRY (KEEP_ASM_RW_ASMS_TAC eq) THEN (  RM_ASM_RW_GOAL_TAC eq)) (hd subgoals)) inst_eq_subgoal_validation_eqs
      else
        map (fn (subgoals, _, eq) => (TRY (KEEP_ASM_RW_ASMS_TAC eq) THEN (KEEP_ASM_RW_GOAL_TAC eq)) (hd subgoals)) inst_eq_subgoal_validation_eqs
    in
    let val subgoals = flatten (map #1 elim_eq_subgoal_validations)
        val validation = fn thms =>
          let val inst_elim_eq_validations = zip (map #2 inst_eq_subgoal_validation_eqs) (map #2 elim_eq_subgoal_validations) in
          let val inst_elim_eq_merged_validations =
            map (fn (inst_validation, elim_validation) => fn thms => inst_validation [elim_validation thms])
                inst_elim_eq_validations in
          let val validation_thms = zip inst_elim_eq_merged_validations thms in
          let val case_thms = map (fn (validation, thm) => validation [thm]) validation_thms in
          let val thm = DISJ_CASESL inst_case_thm case_thms in
            thm
          end end end end end in
      (subgoals, validation)
    end end end end end end end end end end end

  val SPLIT_SCALAR_CASE_KEEP_EQ_TAC = (SPLIT_SCALAR_CASE_PATTERN_TAC false) THEN CASE_PATTERN_TAC

  val SPLIT_SCALAR_CASE_TAC = (SPLIT_SCALAR_CASE_PATTERN_TAC true) THEN CASE_PATTERN_TAC

  val SPLIT_VECTOR_CASE_TAC =              CASE_PATTERN_TAC THEN SPLIT_SCALAR_CASE_TAC

  (****************************************************************************)
  (*End of case splitting tactic***********************************************)
  (****************************************************************************)






  (****************************************************************************)
  (*Start of function path expansions******************************************)
  (****************************************************************************)

  (* Given arguments from right to left of a function definition and argument
   * from right to left of a function application, returns:
   * -NONE: The definition is not applicable with respect to the given
   *  arguments (the patterns of some corresponding arguments do not match).
   * -SOME NONE: The definition is directly applicable with respect to the given
   *  arguments, where only the variables of the arguments in the definition
   *  need to be mapped to the corresponding arguments.
   * -SOME (SOME variable): The definition can only be made applicable if
   *  variable in some argument is expanded to a certain pattern. This means
   *  that variable must be expanded to all possible patterns, and one of those
   *  patterns can be made to match (possibly with further expansions for nested
   *  patterns like SOME (hd::tl) the corresponding arguments of definition.
   *)
  fun pars_args_matching [] [] = SOME NONE               (* No arguments is a correct definition to choose, but nothing to expand. *)
    | pars_args_matching (_::_) [] = raise (mk_HOL_ERR "helper_tactics" "pars_args_matching" "More parameters than arguments.")
    | pars_args_matching [] (_::_) = raise (mk_HOL_ERR "helper_tactics" "pars_args_matching" "More arguments than parameters.")
    | pars_args_matching (par::pars) (arg::args) =
      let val type_of_matching = find_type_of_par_arg_matching par arg in
      case type_of_matching of
        NONE => NONE                          (* Wrong definition. *)
      | SOME NONE => (                        (* Correct definition, no variable to expand. *)
          case pars_args_matching pars args of        (* Check that following arguments match. *)
            NONE => NONE                      (* Wrong definition. *)
          | SOME expansion => SOME expansion) (* Correct definition, with an expansion if expansion is SOME term. *)
      | SOME (SOME expansion) => (            (* Useful definition, but a term in arg must be expanded to match par. *)
          case pars_args_matching pars args of        (* Check that following arguments match. *)
            NONE => NONE                      (* Wrong definition. *)
          | SOME _ => SOME (SOME expansion))  (* Correct definition, but with additional expansions. Leftmost expansion chosen. *)
      end
  (* Given two terms from and to, decides whether it is possible to create a
   * mapping from from to to, possibly by expanding terms in to such that the
   * resulting pattern matches the corresponding pattern of from.
   *
   * matchable_variables are variables of from that can be matched, initially the
   * free variables of from, used solely to handle abstractions when computing
   * which arguments to expand and is not used by the function invoking this
   * function, where bounded variables must be mapped to corresponding bounded
   * variables in to.
   *
   * -(NONE, NONE): No matching possible. Means failure.
   * -(SOME matching, NONE): Matching exists according to matching, and no
   *  variables need to be expanded.
   * -(NONE, SOME variable): variable is a variable that must be expanded to
   *  create a matching.
   * -(SOME matching, SOME variable): Never returned.
   *
   * ABSTRACTIONS CANNOT OCCUR IN PARAMETER PATTERNS.
   *)
  and find_type_of_par_arg_matching par arg =
    let fun is_match par arg = let val _ = match_term par arg in true end handle _ => false in
      if is_var arg then
        if is_var par then
          SOME NONE                     (* Nothing to expand. *)
        else                            (* par is constant or constructor application. *)
          SOME (SOME arg)               (* arg must be expanded to constant or constructor application. *)
      else if is_const arg then
        if is_match par arg then
          SOME NONE                     (* Constants cannot be expanded. *)
        else
          NONE                          (* Parameter cannot be instantiated to constant. *)
      else if is_comb arg then
        if is_var par then
          SOME NONE                     (* Nothing to expand since parameter is a variable. *)
        else                            (* Parameter is constant or constructor application. *)
          let val (arg_function, arg_arguments) = strip_comb arg in
            if TypeBase.is_constructor arg_function then
              let val (par_function, par_arguments) = strip_comb par in
                if is_match par_function arg_function then
                  if null par_arguments then
                    NONE                (* Parameter is a constant, which cannot match a constructor application. *)
                  else
                    pars_args_matching par_arguments arg_arguments (* Check arguments. *)
                else
                  NONE                  (* Parameter constant/constructor does not match argument constructor. *)
              end
            else
              SOME (SOME arg)           (* Argument is an ordinary function application that must be expanded. *)
          end
      else (*is_abs arg then*)
        NONE                            (* Abstractions can, by type restrictions, only be matched from functions, which occur only as type constructors in parameters, and thus cannot be matched. *)
    end

  (* Inputs:
   * -A term term_to_expand.
   * -A list of terms assumptions.
   *
   * Output:
   * SOME a, a in assumptions, if a is of the form
   * 'term_to_expand = pattern t1...tn', where terms of the type of
   * term_to_expand can be of the form 'pattern v1...vn' (vi variable) according
   * to the nchotomy theorem of the type of term_to_expand.
   *)
  fun find_expansion_eq term_to_expand assumptions =
    let val eqs = filter is_eq assumptions in
    let val potential_expansion_eqs = filter (fn eq => Term.compare (boolSyntax.lhs eq, term_to_expand) = EQUAL) eqs in

    let val type_of_term_to_expand = type_of term_to_expand in
    let val nchotomy_thm = TypeBase.nchotomy_of type_of_term_to_expand in
    let val inst_nchotomy_thm = ISPEC term_to_expand nchotomy_thm in
    (* [([v1...vn], term_to_expand = p v1...vn), ...] *)
    let val matchable_variables_expansion_eqs = map strip_exists ((strip_disj o concl) inst_nchotomy_thm) in

    (* true if and only if potential_expansion_pattern can be matched to from expansion via variables in expansion. *)
    let fun is_expansion potential_expansion_pattern (matchable_variables, expansion) =
      let val expansion_pattern = boolSyntax.rhs expansion in
        case find_matching expansion_pattern potential_expansion_pattern of
          NONE => false
        | SOME matching =>
          let val matched_variables = map (fn {redex = from, residue = to} => from) matching  (* Each matched variable is in matchable_variables. *)
              fun is_same t1 t2 = Term.compare (t1, t2) = EQUAL in
            all (fn matched => exists (is_same matched) matchable_variables) matched_variables
          end
      end in

    (* see if some rhs in potential_expansion_eqs matches some rhs in matchable_variables_expansion_eqs *)
    case List.find (fn eq => exists (is_expansion (boolSyntax.rhs eq)) matchable_variables_expansion_eqs) potential_expansion_eqs of
      NONE => NONE
    | SOME assumption_expansion_eq => SOME assumption_expansion_eq
  end end end end end end end

  (* Given a function application and a list of definitions of that function
   * (due to pattern matching in the definition), returns:
   * -exception if no definition can be used to unfold the function application
   *  with the given arguments.
   * -(SOME thm, NONE, NONE, [(thm, pars)]): thm is a theorem of the form
   *  '|- function arguments = body', where 'function arguments' is the function
   *  application in question.
   * -(NONE, SOME eq, NONE, thms): Some definition can be matched with the given
   *  arguments, if eq (of form 'argi = pattern t1...tn') is used to rewrite
   *  argi, thms is the last argument but with invalid definition theorems
   *  removed.
   * -(NONE, NONE, SOME expansion, thms): Some definition can be matched with
   *  the given arguments, if expansion (variable or function application) is
   *  expanded to a pattern, and thms is the last argument but with invalid
   *  definition theorems removed.
   *)
  fun find_def function_application assumptions [] =
      raise (mk_HOL_ERR "helper_tactics" "find_def" "The function application cannot be unfolded since no definition has matching arguments.")
    | find_def function_application assumptions ((def_thm, def_pars)::def_thm_parss) =
      let val (app_fun, app_args) = strip_comb function_application in
      let val def_pars_length = length def_pars
          val app_args_length = length app_args in
        if def_pars_length > app_args_length then
          (* Given theorem is not a definition of the applied function since the
           * definition requires ADDITIONAL arguments, try next theorem.
           *)
          find_def function_application assumptions def_thm_parss
        else
          (* Due to check above: length def_args < length app_args. Drop redundant arguments. *)
          let val (app_args, dropped_args) = split_list def_pars_length app_args in
          let val pars_args_matching = pars_args_matching def_pars app_args in
            case pars_args_matching of
              NONE => find_def function_application assumptions def_thm_parss (* Current definition does not match given function application, try next definition. *)
            | SOME NONE =>                                                    (* Current definition works, and can be instantiated. *)
              let val unquantified_def_thm = SPEC_ALL def_thm in
              let val unquantified_def_lhs_conclusion = (boolSyntax.lhs o concl) unquantified_def_thm in
              let val args_matched_function_application = list_mk_comb (app_fun, app_args) in
              let val matching = match_term unquantified_def_lhs_conclusion args_matched_function_application in
              let val thm = INST_TY_TERM matching unquantified_def_thm in
              let val thm_apps = foldl (fn (dropped_arg, thm) => AP_THM thm dropped_arg) thm dropped_args in
                (SOME thm_apps, NONE, NONE, [(def_thm, def_pars)])
              end end end end end end
            | SOME (SOME term_to_expand) =>                                                    (* Current definition works, but expansion necessary. *)
              let val expansion_eq = find_expansion_eq term_to_expand assumptions in
              case expansion_eq of
                NONE =>
                (NONE, NONE, SOME term_to_expand, (def_thm, def_pars)::def_thm_parss)          (* Expansion equation not among assumptions. *)
              | SOME assumption_expansion_eq =>
                (NONE, SOME assumption_expansion_eq, NONE, (def_thm, def_pars)::def_thm_parss) (* Expansion equation among assumptions. *)
              end
          end end
      end end
(*
  fun find_def pars_length function_application assumptions [] =
      raise (mk_HOL_ERR "helper_tactics" "find_def" "The function application cannot be unfolded since no definition has matching arguments.")
    | find_def pars_length function_application assumptions ((def_thm, def_pars)::def_thm_parss) =
      let val (app_fun, app_args) = strip_comb function_application in
      let val def_pars_length = length def_pars
          val app_args_length = length app_args in
        if def_pars_length > app_args_length orelse def_pars_length <> pars_length orelse app_args_length <> pars_length then
          (* Given theorem is not a definition of the applied function since the
           * definition requires ADDITIONAL arguments, try next theorem.
           *)
          find_def pars_length function_application assumptions def_thm_parss
        else
          (* Due to check above: length def_args < length app_args. Drop redundant arguments. *)
          let val (app_args, dropped_args) = split_list def_pars_length app_args in
          let val pars_args_matching = pars_args_matching def_pars app_args in
            case pars_args_matching of
              NONE => find_def pars_length function_application assumptions def_thm_parss (* Current definition does not match given function application, try next definition. *)
            | SOME NONE =>                                                    (* Current definition works, and can be instantiated. *)
              let val unquantified_def_thm = SPEC_ALL def_thm in
              let val unquantified_def_lhs_conclusion = (boolSyntax.lhs o concl) unquantified_def_thm in
              let val args_matched_function_application = list_mk_comb (app_fun, app_args) in
              let val matching = match_term unquantified_def_lhs_conclusion args_matched_function_application in
              let val thm = INST_TY_TERM matching unquantified_def_thm in
              let val thm_apps = foldl (fn (dropped_arg, thm) => AP_THM thm dropped_arg) thm dropped_args in
                (SOME thm_apps, NONE, NONE, [(def_thm, def_pars)])
              end end end end end end
            | SOME (SOME term_to_expand) =>                                                    (* Current definition works, but expansion necessary. *)
              let val expansion_eq = find_expansion_eq term_to_expand assumptions in
              case expansion_eq of
                NONE =>
                (NONE, NONE, SOME term_to_expand, (def_thm, def_pars)::def_thm_parss)          (* Expansion equation not among assumptions. *)
              | SOME assumption_expansion_eq =>
                (NONE, SOME assumption_expansion_eq, NONE, (def_thm, def_pars)::def_thm_parss) (* Expansion equation among assumptions. *)
              end
          end end
      end end
*)

  (* The operation of adding equations of the form e = pattern v1...vn is
   * performed as follows:
   * 1. Obtain the type of the expression e.
   * 2. From the type, obtain the theorem
   *    |- !e.
   *       (?x11...x1n. e = patternm x11...x1n) \/
   *       ... \/
   *       (?xm1...xmn. e = patternm xm1...xmn)
   * 3. Instantiate the theorem with e and associated types to obtain
   *    |- (?x11...x1n. e = patternm x11...x1n) \/
   *       ... \/
   *       (?xm1...xmn. e = patternm xm1...xmn)
   * 4. Each disjunct is to be instantiated:
   *    a) Given disjunct ?xi1...xin. e = patterni xi1...xin
   *    b) Create instantiation of xij [(vin,xin), ..., (vi1, xi1)] such that
   *       each vij does not occur free in:
   *       •Any assumption.
   *       •The conclusion.
   *       •?xi1...xin. e = patterni xi1...xin.
   *    c) Create subgoal A u {e = patterni vi1...vin} |- t.
   *    d) Create validation function which iterates CHOOSE on the instantiation.
   *)
  fun ADD_VAR_EQ_PATTERNS_TAC variable_to_expand (A, t) =
    let val type_of_variable_to_expand = type_of variable_to_expand in
    let val nchotomy_thm = TypeBase.nchotomy_of type_of_variable_to_expand in
    let val inst_nchotomy_thm = ISPEC variable_to_expand nchotomy_thm in
    let val xeqs = (strip_disj o concl) inst_nchotomy_thm in
    let val ieqs = map (fn xeq => instantiate_exists xeq (t::A)) xeqs
        val subgoals = map (fn (iterm, vxs) => (iterm::A, t)) ieqs
        fun chooses thm iterm [] = thm
          | chooses thm iterm ((vi, xi)::vxs) =                         (* iterm = s[vi/xi] *)
             let val xterm = mk_exists (xi, subst [vi |-> xi] iterm) in (* xterm = ?xi. s, since vi is fresh. *)
               chooses (CHOOSE (vi, ASSUME xterm) thm) xterm vxs
             end in
    let val validation = fn thms =>
      let val thms_ieq_vxss = zip thms ieqs in
      let val thm_xeqs = map (fn (thm, (iterm, vxs)) => chooses thm iterm vxs) thms_ieq_vxss in (* A u {?x1...xn. l = ri} |- t *)
      let val thm = DISJ_CASESL inst_nchotomy_thm thm_xeqs in (* A |- t *)
        thm
      end end end
    in
      (subgoals, validation)
    end end end end end end

  (* Given a type, returns the number of arguments it expects. If the type is
   * a -> b -> c -> d, then the return value is 3.
   *)
  fun number_of_parameters ty =
    if is_vartype ty then
      0
    else
      let val (fun_name, tys) = dest_type ty in
        if fun_name = "fun" then
          1 + (number_of_parameters ((hd o tl) tys))
        else
          0
      end

  (*       A u {l = f pv1...ai...pvn} ?- t
   * --------------------------------------------if paramter i of f must be a pattern.
   * A u {l = f pv1...ai...pvn} u {ai = pvi} ?- t
   *
   * Algorithm:
   * The left hand side of the equation is a function application of a function
   * defined in terms of pattern matching on its parameters.
   * i  There exists an equation among the assumptions with one side being the
   *    the argument and the other side the pattern:
   *    Substitute the pattern for the argument and return.
   * ii Otherwise, add new equations of the form argument = pattern v1...vn and
   *    return.
   *)
  fun SUBST_ARG_OR_ADD_ARG_PAT_SUBTERM_TAC def_parss mark template subterm term (A, t) =
    let val function_application = subterm in
    let val pars_length = number_of_parameters ((type_of o #1 o strip_comb) function_application) in
    let val (subterm_eq_thm, asm_eq_expansion, term_to_expand, def_parss) = find_def (*pars_length*) function_application A def_parss in
      case (subterm_eq_thm, asm_eq_expansion, term_to_expand) of
        (SOME subterm_eq_thm, NONE, NONE) => (* Expand function. *)
          ([(A, t, mark, template, subterm, term)], hd)
      | (NONE, SOME asm_eq_expansion, NONE) => (* Expand term by means of the assumption 'asm_eq_expansion'. *)
        let val (A1, t1, v1, subterm1, term1) = SUBST_SUBTERM_TAC asm_eq_expansion mark template subterm term (A, t) in
          COMPOSE_SUBGOALS_GOAL_TAC [SUBST_ARG_OR_ADD_ARG_PAT_SUBTERM_TAC def_parss mark template subterm1 term1 (A1, t1)] (v1 o hd)
        end
      | (NONE, NONE, SOME term_to_expand) => (* Add assumptions of the form 'term_to_expand = pi v1...vn'. *)
        let val (subgoals, validation) = ADD_VAR_EQ_PATTERNS_TAC term_to_expand (A, t) in
          COMPOSE_SUBGOALS_GOAL_TAC (map (fn (a, t) => SUBST_ARG_OR_ADD_ARG_PAT_SUBTERM_TAC def_parss mark template subterm term (a, t)) subgoals) validation
        end
      | _ =>
        let val error_message = concat ["No theorem useful for identifying whether/which argument to expand of the function: ", (term_to_string o #1 o strip_comb) function_application, "."] in
          raise (mk_HOL_ERR "helper_tactics" "SUBST_ARG_OR_ADD_ARG_PAT_SUBTERM_TAC" error_message)
        end
    end end end

   (* Input: '(\x1...xn. t) a1...an)'
   * Output: '|- t[a1...an/x1...xn]'
   *)
  fun BETA_CONVS function_application =
    if (not o is_comb) function_application then
      raise (mk_HOL_ERR "helper_tactics" "BETA_CONVS" "No arguments in function application.")
    else
      let val (function, argument) = dest_comb function_application in
        if is_abs function then (* Base case. *)
          BETA_CONV function_application
        else if is_comb function then
          let val thm1 = BETA_CONV function
              val thm2 = REFL argument in
          let val thm3 = MK_COMB (thm1, thm2) in
          let val function_application = (boolSyntax.rhs o concl) thm3 in
          let val thm4 = BETA_CONVS function_application in
          let val thm5 = TRANS thm3 thm4 in
            thm5
          end end end end end
        else
          raise (mk_HOL_ERR "helper_tactics" "BETA_CONVS" "Function in function application is neither abstraction nor application.")
      end

  (* Input:
   * 'case pi v1...vn of p1 => tn | ... | pi t1...tn => ti | ... | pn => tn'
   *
   * Output:
   * '|- case pi v1...vn of p1 => tn | ... | pi t1...tn => ti | ... | pn => tn = ti'
   *)
  fun case_conv case_term =
    let val case_condition = (#2 o TypeBase.dest_case) case_term in
    let val case_reduction_thms = (CONJUNCTS o TypeBase.case_def_of o type_of) case_condition
        fun find_reduction_thm [] =
            raise (mk_HOL_ERR "helper_tactics" "find_reduction_matching_thm" "No matching theorem")
          | find_reduction_thm (thm::thms) =
            let val pattern_thm = (hd o #2 o strip_comb o boolSyntax.lhs o #2 o strip_forall o concl) thm in
            let val matching = match_term pattern_thm case_condition in
              thm
            end
            handle _ => find_reduction_thm thms
            end in
    let val reduction_thm = SPEC_ALL (find_reduction_thm case_reduction_thms) in
    let val instantiation = match_term ((boolSyntax.lhs o concl) reduction_thm) case_term in
    let val rewrite_thm1 = INST_TY_TERM instantiation reduction_thm in
    let val case_reduct = (boolSyntax.rhs o concl) rewrite_thm1 in
      if is_comb case_reduct then
        if (is_abs o #1 o strip_comb) case_reduct then (* Simplify '(\x1...xn. t) a1...an' to t[a1...an/x1..xn] *)
          let val rewrite_thm2 = BETA_CONVS case_reduct in
          let val rewrite_thm = TRANS rewrite_thm1 rewrite_thm2 in
            rewrite_thm
          end end
        else
          rewrite_thm1
      else
        rewrite_thm1
    end end end end end end

  (* subterm: ' case pi v1...vn of p1 => t1 | ... | pn => tn'
   * ----------------------------------------------------------------
   * subterm': 'ti'
   *)
  fun REDUCE_CASE_TERM_TAC mark template subterm term (A, t) =
    let val subterm_eq_thm = case_conv subterm in
      RW_SUBTERM_TAC subterm_eq_thm mark template term (A, t)
    end

  (*        A u {old = new}  ?- t
   * --------------------------------------
   * A[new/old] u {old = new} ?- t[new/old]
   *
   * asm_eq: 'old = new'.
   *
   * old must not be mark.
   *
   * Assumes that term is not asm_eq.
   *)
  fun ASM_RW_TAC asm_eq mark template subterm term (A, t) =
    let fun RW_OTHERS_TAC [] (A, t) =
            let val (subgoals, v1) = ALL_TAC (A, t) in
            let val (A1, t1) = hd subgoals in
              (A1, t1, fn thm => v1 [thm])
            end end
          | RW_OTHERS_TAC (asm_to_rw::asm_to_rws) (A, t) =
            let val (subgoals1, v1) = KEEP_ASM_RW_ASM_TAC asm_eq asm_to_rw (A, t) in
            let val (A1, t1) = hd subgoals1 in
            let val (A2, t2, v2) = RW_OTHERS_TAC asm_to_rws (A1, t1) in
              (A2, t2, fn thm => v1 [v2 thm])
            end end end in
    (* Rewrite all assumptions except asm_eq. *)
    let val asm_to_rws = filter (fn a => not (same_term asm_eq a)) A in
    let val (A1, t1, v1) = RW_OTHERS_TAC asm_to_rws (A, t) in
    (* Rewrite conclusion. *)
    let val (subgoals2, v2) = SUBST_TAC [ASSUME asm_eq] (A1, t1) in
    let val (A2, t2) = hd subgoals2
        val (old, new) = dest_eq asm_eq in
    let val mark2 = if same_term mark new then genvar_term mark else mark in
    let val template2 = subst [old |-> new] (subst [mark |-> mark2] template)
        val subterm2 = subst [old |-> new] subterm
        val term2 = subst [old |-> new] term in
      (A2, t2, fn thm => (v1 o v2) [thm], mark2, template2, subterm2, term2)
    end end end end end end end

  (*              A ?- t
   * --------------------------------
   * A u {fresh_variable = term} ?- t
   *
   * fresh_variable is not free in A, t nor additional_invalid_variable_names.
   *)
  fun ADD_VAR_EQ_TERM_TAC term additional_invalid_variable_names (A, t) =
    let val xeq_thm = ISPEC term boolTheory.EXISTS_REFL in
    let val (subgoals1, v1) = ASSUME_TAC xeq_thm (A, t) in
    let val (A1, t1) = hd subgoals1
        val xeq = concl xeq_thm in
    let val (A2, t2, v2, asm_eq) = REMOVE_XEQ_TAC xeq additional_invalid_variable_names (A1, t1) in
      (A2, t2, fn thm => v1 [v2 thm], asm_eq)
    end end end end

  (* xeq = '?x1...xn. variable = pattern x1...xn'
   * eq_to_rewrite = 'l = case variable of ...'
   * --------------------------------------------, where xi' are fresh within the goal (A, t).
   * eq_to_rewrite = 'l = case pattern x1'...xn''
   *
   * A u {?x1...xn. variable = pattern x1...xn}  ?- t
   * --------------------------------------------------------------
   * A[pattern x1'...xn'/variable] ?- t[pattern x1'...xn'/variable]
   *
   * eq_to_rewrite = 'l = case pattern x1'...xn' of ...', where xi' do not occur
   * in A, t and ?x1...xn. variable = pattern x1...xn.
   *)
  fun ADD_REDUCE_XEQ_TAC xeq mark template subterm term (A, t) =
    let val (A1, t1, v1, asm_eq) = REMOVE_XEQ_TAC xeq [mark] (A, t) in (* mark must not occur in instantiated variables. *)
    let val (A2, t2, v2, mark2, template2, subterm2, term2) = ASM_RW_TAC asm_eq mark template subterm term (A1, t1) in
    let val (subgoals3, v3) = REMOVE_ASM_TAC asm_eq (A2, t2) in
    let val (A3, t3) = hd subgoals3
        val mark3 = mark2
        val template3 = template2
        val subterm3 = subterm2
        val term3 = term2 in
      (A3, t3, fn thm => (v1 o v2 o v3) [thm], mark3, template3, subterm3, term3)
    end end end end

  (* subterm:  'l = case variable of ...'
   * --------------------------------------, where xi' are fresh within the goal (A, t).
   * subterm': 'l = case pattern x1'...xn''
   *
   *                             A ?- t
   * --------------------------------------------------------------
   * A[pattern x1'...xn'/variable] ?- t[pattern x1'...xn'/variable]
   *
   * Intention of when to apply this tactic:
   * The variable to expand occurs either:
   * -At most twice among the assumptions, where the equation to rewrite is an
   *  assumption.
   * -At most once among the assumptions, and once in the conclusion, where the
   *  equation to rewrite is the conclusion.
   *
   * Algorithm:
   * 1. Expand the variable.
   * 2. Substitute the expansion for all occurrences of the variable in the goal.
   * 3. Performs a recursive application on all subgoals (with
   *    variable_new = false, and
   *    eq_to_rewrite = 'l = case pattern x1'...xn' of ...'
   *)
  fun SUBST_VAR_EXP_TAC mark template subterm term (A, t) =
    let val variable = (#2 o TypeBase.dest_case) subterm in
    let val nchotomy_thm = (TypeBase.nchotomy_of o type_of) variable in
    let val case_thm = ISPEC variable nchotomy_thm in
    let val xeqs = (strip_disj o concl) case_thm in
    let val acvmtsts = map (fn xeq => ADD_REDUCE_XEQ_TAC xeq mark template subterm term (xeq::A, t)) xeqs in
    let val (acmtsts, vs) = foldl (fn ((a, c, v, m, template, s, term), (acmtsts, vs)) => ((a, c, m, template, s, term)::acmtsts, v::vs)) ([], []) acvmtsts in
    let val validation = fn thms =>
      let val v_thms = zip vs thms in
      let val intermediate_thms = map (fn (v, thm) => v thm) v_thms in
      let val goal_achieving_thm = DISJ_CASESL case_thm intermediate_thms in
        goal_achieving_thm
      end end end in
      (acmtsts, validation)
    end end end end end end end

  fun is_pattern term =
    if is_const term then
      true
    else if is_comb term then
      (TypeBase.is_constructor o #1 o strip_comb) term
    else
      false

  (* NOTE: variable does not have to be a variable but this tactic is used in
   * such a context.
   *
   * subterm:  'case variable of ...'
   * subterm': 'case patterni t1...tn of ...' ...
   *
   *                                   A ?- t
   * -----------------------------------------------------------------------------------------
   * A' u {variable = pattern1 v11...v1n} ?- t' ... A' u {variable = patternm vm1...vmp} ?- t'
   *
   * where A'/t' reflects the rewrite of the equation to rewrite depending on
   * whether the equation to rewrite is the conclusion or an assumption:
   * {l = r[pattern1 v11...v1n/variable]}
   *
   * Then applies REC_TAC on each subgoal.
   *
   * Intention of when to apply this tactic:
   * The variable to expand occurs either:
   * -At least three times among the assumptions, where the equation to rewrite
   *  is an assumption.
   * -At least twice among the assumptions, and at least once in the conclusion,
   *  where the equation to rewrite is the conclusion.
   *
   * Algorithm (the variable occurs an arbitrary number of times among the other
   * assumptions):
   * 1. Expand the variable.
   * 2. Add the assumption variable = expansion.
   * 3. Substitute expansion for variable in subterm.
   * 4. Recursive application with REC_TAC on each subgoal, with unique_variable = false.
   *    The following tactic does not perform the recursive call internally.
   *)
(* BUGGY CODE SINE RW_SUBTERM IS GIVEN WRONG THEOREM, TEMPLATE AND MARK.
  fun EXPAND_CASE_VARIABLE_TAC mark template subterm term (A, t) =
    let val variable = (#2 o TypeBase.dest_case) subterm in
    let val nchotomy_thm = (TypeBase.nchotomy_of o type_of) variable in
    let val case_thm = ISPEC variable nchotomy_thm in
    let val xeqs = (strip_disj o concl) case_thm
        fun REMOVE_XEQ_SUBST_RHS_REC_TAC xeq (A0, t0) =
          let val (A1, t1, v1, asm_eq) = REMOVE_XEQ_TAC xeq [mark] (A0, t0) in
          let val (A2, t2, v2, subterm2, term2) = RW_SUBTERM_TAC ((SYM o ASSUME) asm_eq) mark template term (A1, t1) in
            (A2, t2, v1 o v2, subterm2, term2)
          end end in
    let val acvsts = map (fn xeq => REMOVE_XEQ_SUBST_RHS_REC_TAC xeq (A, t)) xeqs in (* [(a, c, v, subterm, term)] *)
    let val (acmtsts, validations) = foldl (fn ((a, c, v, s, t), (acmtsts, vs)) => ((a, c, mark, template, s, t)::acmtsts, v::vs)) ([], []) acvsts in
    let val validation = fn thms =>
      let val validation_thms = zip validations thms in
      let val subgoal_case_thms = map (fn (validation, thm) => validation thm) validation_thms in
      let val goal_thm = DISJ_CASESL case_thm subgoal_case_thms in
        goal_thm
      end end end in
      (acmtsts, validation)
    end end end end end end end
*)
(* OLD CODE WHICH EXPANDS VARIABLE IRRESPECTIVELY OF WHETHER IT HAS BEEN EXPANDED OR NOT.*)
  fun EXPAND_CASE_VARIABLE_TAC mark template subterm term (A, t) =
    let val (case_function, variable, bodies) = TypeBase.dest_case subterm in
    let val case_variable_rw_thm = REFL subterm
        val case_cond_mark = genvar_term variable
        val case_variable_rw_template = mk_eq (subterm, TypeBase.mk_case (case_cond_mark, bodies)) in
    let val nchotomy_thm = (TypeBase.nchotomy_of o type_of) variable in
    let val case_thm = ISPEC variable nchotomy_thm in
    let val xeqs = (strip_disj o concl) case_thm
        fun REMOVE_XEQ_SUBST_RHS_REC_TAC xeq (A0, t0) =
          let val (A1, t1, v1, asm_eq) = REMOVE_XEQ_TAC xeq [mark] (A0, t0) in
          let val subterm_eq_thm = SUBST [case_cond_mark |-> ASSUME asm_eq] case_variable_rw_template case_variable_rw_thm in
          let val (A2, t2, v2, subterm2, term2) = RW_SUBTERM_TAC subterm_eq_thm mark template term (A1, t1) in
            (A2, t2, v1 o v2, subterm2, term2)
          end end end in
    let val acvsts = map (fn xeq => REMOVE_XEQ_SUBST_RHS_REC_TAC xeq (A, t)) xeqs in (* [(a, c, v, subterm, term)] *)
    let val (acmtsts, validations) = foldl (fn ((a, c, v, s, t), (acmtsts, vs)) => ((a, c, mark, template, s, t)::acmtsts, v::vs)) ([], []) acvsts in
    let val validation = fn thms =>
      let val validation_thms = zip validations thms in
      let val subgoal_case_thms = map (fn (validation, thm) => validation thm) validation_thms in
      let val goal_thm = DISJ_CASESL case_thm subgoal_case_thms in
        goal_thm
      end end end in
      (acmtsts, validation)
    end end end end end end end end
(*
  fun has_expanded mark template subterm term (A, t) variable bodies [] = NONE
    | has_expanded mark template subterm term (A, t) variable bodies (eq::eqs) =

      let val (l, r) = dest_eq eq in

        if same_term variable l andalso is_pattern r then (* variable = pattern. *)
          let val case_variable_rw_thm = REFL subterm
              val case_cond_mark = genvar_term variable
              val case_variable_rw_template = mk_eq (subterm, TypeBase.mk_case (case_cond_mark, bodies)) in
          let val subterm_eq_thm = SUBST [case_cond_mark |-> ASSUME eq] case_variable_rw_template case_variable_rw_thm in
          let val (A, t, v, subterm, term) = RW_SUBTERM_TAC subterm_eq_thm mark template term (A, t) in
            SOME ([(A, t, mark, template, subterm, term)], fn thms => (v o hd) thms)
          end end end
        else if same_term r variable andalso is_pattern l then (* pattern = variable. *)
          let val case_variable_rw_thm = REFL subterm
              val case_cond_mark = genvar_term variable
              val case_variable_rw_template = mk_eq (subterm, TypeBase.mk_case (case_cond_mark, bodies)) in
          let val subterm_eq_thm = SUBST [case_cond_mark |-> ASSUME eq] case_variable_rw_template case_variable_rw_thm in
          let val (A, t, v, subterm, term) = RW_SUBTERM_REFL_TAC subterm_eq_thm mark template term (A, t) in
            SOME ([(A, t, mark, template, subterm, term)], fn thms => (v o hd) thms)
          end end end
        else
          has_expanded mark template subterm term (A, t) variable bodies eqs
      end
*)

  (* variable_to_expand = term comes from an earlier let expansion.
   * pattern = term comes from an earlier case expansion.
   *
   * pattern = term
   * variable_to_expand = term
   *)
  fun has_previous_let_expansion variable l1 r1 eq2 =
    let val (l2, r2) = dest_eq eq2 in
      if same_term r1 r2 then
        if      same_term l1 variable andalso is_pattern l2 then
          SOME (eq2, mk_eq (l1, r1))
        else if same_term l2 variable andalso is_pattern l1 then
          SOME (mk_eq (l1, r1), eq2)
        else
          NONE
      else
        NONE
    end

  fun find_previous_let_expansion variable (l1, r1) [] = NONE
    | find_previous_let_expansion variable (l1, r1) (eq::eqs) =
      case has_previous_let_expansion variable l1 r1 eq of
        NONE => find_previous_let_expansion variable (l1, r1) eqs
      | SOME (pattern_eq_term, variable_to_expand_eq_term) =>
        SOME (pattern_eq_term, variable_to_expand_eq_term)

  fun find_previous_let_expansions variable all_eqs [] = NONE
    | find_previous_let_expansions variable all_eqs (eq::eqs) =
      case find_previous_let_expansion variable (dest_eq eq) all_eqs of
        NONE => find_previous_let_expansions variable all_eqs eqs
      | SOME (pattern_eq_term, variable_to_expand_eq_term) =>
        SOME (pattern_eq_term, variable_to_expand_eq_term)

  fun find_previous_let_expansionss subterm A =
    let val variable = (#2 o TypeBase.dest_case) subterm in
    let val eqs = filter is_eq A in
      find_previous_let_expansions variable eqs eqs
    end end

  (* Reuses pattern from previous let and case expansions. *)
  fun ALREADY_CASE_VARIABLE_EXPANDED_TAC pattern_eq_term variable_to_expand_eq_term mark template subterm term (A, t) =
    let val (case_function, variable, bodies) = TypeBase.dest_case subterm in
    let val pattern_eq_term_thm = ASSUME pattern_eq_term
        val variable_to_expand_eq_term_thm = ASSUME variable_to_expand_eq_term in
    let val variable_to_expand_eq_pattern_thm = TRANS variable_to_expand_eq_term_thm (SYM pattern_eq_term_thm) in
    let val case_variable_rw_thm = REFL subterm
        val case_cond_mark = genvar_term variable
        val case_variable_rw_template = mk_eq (subterm, TypeBase.mk_case (case_cond_mark, bodies)) in
    let val subterm_eq_thm = SUBST [case_cond_mark |-> variable_to_expand_eq_pattern_thm] case_variable_rw_template case_variable_rw_thm in
    let val (A, t, v, subterm, term) = RW_SUBTERM_TAC subterm_eq_thm mark template term (A, t) in
      ([(A, t, mark, template, subterm, term)], v o hd)
    end end end end end end





(* NEW CODE TRYING TO FIND already existing expansions but did not work well.
  (* Algorithm:
   * i)   Expand the variable to expansion and add variable = expansion to the
   *      assumptions, if variable = expansion or expansion = variable is not
   *      among the assumptions.
   * ii)  Substitute expansion for variable in eq_to_rewrite.
   * iii) Recursive application with REC_TAC on each subgoal, with
   *      variable_new = false, and
   *      eq_to_rewrite = 'l = case pi v1...vn of p1 => t1 | ... | pn => tn'
   *)
  fun EXPAND_CASE_VARIABLE_TAC mark template subterm term (A, t) =
    let val (case_function, variable, bodies) = TypeBase.dest_case subterm in
let val _ = print "has_expanded1\n" in
    let val expanded = has_expanded mark template subterm term (A, t) variable bodies (filter is_eq A) in
let val _ = print "has_expanded2\n" in
      if isSome expanded then
        valOf expanded
      else
        let val case_variable_rw_thm = REFL subterm
            val case_cond_mark = genvar_term variable
            val case_variable_rw_template = mk_eq (subterm, TypeBase.mk_case (case_cond_mark, bodies)) in
        let val nchotomy_thm = (TypeBase.nchotomy_of o type_of) variable in
        let val case_thm = ISPEC variable nchotomy_thm in
        let val xeqs = (strip_disj o concl) case_thm
            fun REMOVE_XEQ_SUBST_RHS_REC_TAC xeq (A0, t0) =
              let val (A1, t1, v1, asm_eq) = REMOVE_XEQ_TAC xeq [mark] (A0, t0) in
              let val subterm_eq_thm = SUBST [case_cond_mark |-> ASSUME asm_eq] case_variable_rw_template case_variable_rw_thm in
              let val (A2, t2, v2, subterm2, term2) = RW_SUBTERM_TAC subterm_eq_thm mark template term (A1, t1) in
                (A2, t2, v1 o v2, subterm2, term2)
              end end end in
        let val acvsts = map (fn xeq => REMOVE_XEQ_SUBST_RHS_REC_TAC xeq (A, t)) xeqs in (* [(a, c, v, subterm, term)] *)
        let val (acmtsts, validations) = foldl (fn ((a, c, v, s, t), (acmtsts, vs)) => ((a, c, mark, template, s, t)::acmtsts, v::vs)) ([], []) acvsts in
        let val validation = fn thms =>
          let val validation_thms = zip validations thms in
          let val subgoal_case_thms = map (fn (validation, thm) => validation thm) validation_thms in
          let val goal_thm = DISJ_CASESL case_thm subgoal_case_thms in
            goal_thm
          end end end in
          (acmtsts, validation)
        end end end end end end end
    end end
end end
*)

  (*           A ?- t
   * ---------------------------
   * A' u {variable = case_cond} ?- t'
   *
   * where variable does not occur in A nor t.
   *
   * subterm  = 'case case_cond of ...'
   * subterm' = '(case case_cond of ...)[variable/case_cond]'
   *)
  fun ADD_SUBST_VAR_EQ_CASE_COND_TAC mark template subterm term (A, t) =
    let val case_cond = (#2 o TypeBase.dest_case) subterm in
    let val (A1, t1, v1, var_eq_case_cond) = ADD_VAR_EQ_TERM_TAC case_cond [mark] (A, t) in
    let val (A2, t2, v2, subterm2, term2) = SUBST_SUBTERM_REFL_TAC var_eq_case_cond mark template subterm term (A1, t1) in
      (A2, t2, v1 o v2, subterm2, term2)
    end end end

  (* Returns the number of occurrences of search_term in searched_term.
   * number_of_occurrences 'x' 'x y x' = 2
   *)
  fun number_of_occurrences search_term searched_term =
    let fun number_of_occurrences_rec bound_variables search_term searched_term =
      let fun is_not_bound variable = all (fn bv => Term.compare (variable, bv) <> EQUAL) bound_variables in
        if Term.compare (search_term, searched_term) = EQUAL andalso is_not_bound search_term then
          1
        else if is_const searched_term orelse is_var searched_term then
          0
        else if is_comb searched_term then
          let val (function, argument) = dest_comb searched_term in
            (number_of_occurrences_rec bound_variables search_term function) +
            (number_of_occurrences_rec bound_variables search_term argument)
          end
        else (* search_term is a comb. *)
          let val (bv, body) = dest_abs searched_term in
            number_of_occurrences_rec (bv::bound_variables) search_term body
          end 
      end in
      number_of_occurrences_rec [] search_term searched_term
    end

  (* Returns the number of occurrences of search_term in
   * searched_terms = [searched_term1, ..., searched_termn].
   *)
  fun number_of_occurrences_in_terms search_term [] = 0
    | number_of_occurrences_in_terms search_term (searched_term::searched_terms) =
      (number_of_occurrences search_term searched_term) +
      (number_of_occurrences_in_terms search_term searched_terms)

  (*        A ?- t
   * ---------------------
   * A1 ?- t1 ... An ?- tn
   *
   * where Ai and ti reflect the simplifications of the case expression of the
   * right hand side of eq_to_rewrite.
   *
   * eq_to_rewrite = 'l = case t of ...'
   * eq_to_rewrite' = 'l = ti', where ti is not a case term.
   *
   * This tactic reduces the case term to all possible bodies, depending on the
   * case condition term.
   *
   * Algoritm:
   * 0. Not a case term:
   *    -If first call: Print error.
   *    -Otherwise: Terminate.
   * 1. Case condition is constant or a term constructor:
   *    i)  Reduce the case term 'case pi v1...vn of p1 => t1 | ... | pn => tn' to ti
   *    ii) Perform a recursive call with:
   *        *variable_new = false
   *        *eq_to_rewrite = 'l = ti'
   * 2. Case condition is a variable:
   *    a) The variable to expand occurs either (variable_new = true):
   *       *At most twice among the assumptions, where the equation to rewrite is
   *        an assumption, or
   *       *At most once among the assumptions, and once in the conclusion, where
   *        the equation to rewrite is the conclusion.
   *       i)   Expand the variable.
   *       ii)  Substitute the expansion for all occurrences of the variable in the
   *            goal.
   *       iii) Perform a recursive application with variable_new = false, and
   *            eq_to_rewrite = 'l = case pattern x1'...xn' of ...'
   *
   *    b) The variable to expand occurs either:
   *       *At least three times among the assumptions, where the equation to
   *        rewrite is an assumption, or
   *       *At least twice among the assumptions, and at least once in the
   *        conclusion, where the equation to rewrite is the conclusion.
   *       i)   Expand the variable.
   *       ii)  Add variable = expansion to the assumptions.
   *       iii) Substitute expansion for variable in eq_to_rewrite.
   *       iv)  Recursive application with REC_TAC on each subgoal, with
   *            variable_new = false, and
   *            eq_to_rewrite = 'l = case pi v1...vn of p1 => t1 | ... | pn => tn'
   * 3. Case condition is a function application 'f a':
   *    i)   Add the assumption 'variable = f a'.
   *    ii)  Substitute variable for f a in eq_to_rewrite in A or t.
   *    iii) Recursive application, with variable_new = true, and
   *         eq_to_rewrite = 'l = case new_variable of p1 => t1 | ... | pn => tn'
   *
   * variable_new is only for optimization, avoiding unnecessary invocations of
   * var_occurs_at_most_twice_in_goal.
   *)
  fun REDUCE_CASE_SUBTERM_REC_TAC first_invocation variable_new mark template subterm term (A, t) =
    let fun is_not_case term = (not o TypeBase.is_case) term
        fun var_occurs_at_most_twice_in_goal var = number_of_occurrences_in_terms var (t::A) <= 2
        val eqs = filter is_eq A in
    let val l_rs = map dest_eq eqs in
    let fun is_condition_eq_pattern case_condition = exists (fn (l, r) => Term.compare (l, case_condition) = EQUAL andalso is_pattern r) l_rs
        fun is_pattern_eq_condition case_condition = exists (fn (l, r) => is_pattern l andalso Term.compare (r, case_condition) = EQUAL) l_rs
    in
      if is_not_case subterm then (* 0. *)
        if first_invocation then
          raise (mk_HOL_ERR "helper_tactics" "REDUCE_CASE_SUBTERM_REC_TAC" "Subterm is not a case term.")
        else
          ([(A, t, mark, template, subterm, term)], hd)
      else if is_cond subterm then
        (* If this tactic has reduced the case to an if (some cases are encoded
         * via if terms), then its time to stop and let the if tactic do the
         * rest, since otherwise this tactic will add assumptions of the form
         * 'T <==> c' and 'F <==> c', where c is the if condition:
         * 'if c then t1 else t2'.
         *)
        ([(A, t, mark, template, subterm, term)], hd)
      else
        let val case_condition = (#2 o TypeBase.dest_case) subterm in
          if is_pattern case_condition then  (* 1. *)
            COMPOSE_ACSTS_TAC REDUCE_CASE_TERM_TAC (REDUCE_CASE_SUBTERM_REC_TAC false false) mark template subterm term (A, t)
          else if is_condition_eq_pattern case_condition then
          (* Equality among assumptions exist where the case condition is the
           * left hand side and a pattern on the right hand side:
           * case_condition = pattern
           *)
            case List.find (fn (l, r) => Term.compare (l, case_condition) = EQUAL andalso is_pattern r) l_rs of
              NONE => raise (mk_HOL_ERR "helper_tactics" "REDUCE_CASE_SUBTERM_REC_TAC" "Cannot happen.")
            | SOME (_, pattern) =>
              let val case_cond_eq_pat_asm = mk_eq (case_condition, pattern) in
                COMPOSE_ACSTS_TAC (SUBST_SUBTERM_TAC case_cond_eq_pat_asm) (REDUCE_CASE_SUBTERM_REC_TAC false false) mark template subterm term (A, t)
              end
          else if is_pattern_eq_condition case_condition then
          (* Equality among assumptions exist where the case condition is the
           * right hand side and a pattern on the left hand side:
           * pattern = case_condition
           *)
            case List.find (fn (l, r) => is_pattern l andalso Term.compare (r, case_condition) = EQUAL) l_rs of
              NONE => raise (mk_HOL_ERR "helper_tactics" "REDUCE_CASE_SUBTERM_REC_TAC" "Cannot happen.")
            | SOME (pattern, _) =>
              let val pat_eq_case_cond_asm = mk_eq (pattern, case_condition) in
                COMPOSE_ACSTS_TAC (SUBST_SUBTERM_REFL_TAC pat_eq_case_cond_asm) (REDUCE_CASE_SUBTERM_REC_TAC false false) mark template subterm term (A, t)
              end
          else if is_var case_condition then (* 2. *)
            let val expansion = find_previous_let_expansionss subterm A in
              if isSome expansion then (* Reuse previous expansion due to previous let and case reductions. *)
                let val (pattern_eq_term, variable_to_expand_eq_term) = valOf expansion in       
                  COMPOSE_ACMTST_TAC (ALREADY_CASE_VARIABLE_EXPANDED_TAC pattern_eq_term variable_to_expand_eq_term) (REDUCE_CASE_SUBTERM_REC_TAC false false) mark template subterm term (A, t)
                end
              else if var_occurs_at_most_twice_in_goal case_condition orelse variable_new then (* 2.a) *)
                COMPOSE_ACMTST_TAC SUBST_VAR_EXP_TAC (REDUCE_CASE_SUBTERM_REC_TAC false false) mark template subterm term (A, t)
              else                                                                             (* 2.b) *)
                COMPOSE_ACMTST_TAC EXPAND_CASE_VARIABLE_TAC (REDUCE_CASE_SUBTERM_REC_TAC false false) mark template subterm term (A, t)
            end
          else if is_comb case_condition then (* 3. *)
            COMPOSE_ACSTS_TAC ADD_SUBST_VAR_EQ_CASE_COND_TAC (REDUCE_CASE_SUBTERM_REC_TAC false true) mark template subterm term (A, t)
          else                                (* Error. *)
            raise (mk_HOL_ERR "helper_tactics" "REDUCE_CASE_SUBTERM_REC_TAC"
                              "Case condittion is not a pattern, variable or function application.")
        end
    end end end

  (* Transforms a goal to a the subgoals corresponding to each possible pattern
   * of the case condition of the case term (subterm). *)
  fun REDUCE_CASE_SUBTERM_TAC mark template subterm term (A, t) = REDUCE_CASE_SUBTERM_REC_TAC true false mark template subterm term (A, t)

  (* Input: 'if c then t1 else t2'
   * Output: 'c |- (if c then t1 else t2) = t1'
   *
   * Algorithm:
   * ----------SYM o EQT_INTRO o ASSUME 'c'   ----------------------------bool_case_thm
   * c |- T = c                               |- if T then t1 else t2 = t1
   * ---------------------------------------------------------------------SUBST
   *          c |- if c then t1 else t2 = t1
   *)
  fun condition_hyp_cond_eq_true_branch_thm if_then_else_term =
    let val (condition, true_branch, false_branch) = dest_cond if_then_else_term in
    let val rw_thm = (SYM o EQT_INTRO o ASSUME) condition
        fun true_case_thm thm = Term.compare ((#1 o dest_cond o boolSyntax.lhs o #2 o strip_forall o concl) thm, T) = EQUAL in
    let val true_cond_thm = hd (filter true_case_thm (CONJUNCTS boolTheory.bool_case_thm)) in
    let val if_thm = ISPECL [true_branch, false_branch] true_cond_thm
        val preferred_mark = mk_var ("mark", type_of condition) in
    let val mark = gen_variant is_constname "" (free_varsl [if_then_else_term]) preferred_mark in
    let val template = mk_eq (mk_cond (mark, true_branch, false_branch), true_branch) in
    let val if_eq_then_branch_thm = SUBST [mark |-> rw_thm] template if_thm in
      if_eq_then_branch_thm
    end end end end end end end

  (* Input: 'if c then t1 else t2'
   * Output: '~c |- (if c then t1 else t2) = t2'
   *
   * Algorithm:
   * -----------SYM o EQF_INTRO o ASSUME '~c'   ----------------------------bool_case_thm
   * ~c |- F = c                                |- if F then t1 else t2 = t2
   * -----------------------------------------------------------------------SUBST
   *          ~c |- if c then t1 else t2 = t2
   *)
  fun condition_hyp_cond_eq_false_branch_thm if_then_else_term =
    let val (condition, true_branch, false_branch) = dest_cond if_then_else_term in
    let val rw_thm = (SYM o EQF_INTRO o ASSUME o mk_neg) condition
        fun false_case_thm thm = Term.compare ((#1 o dest_cond o boolSyntax.lhs o #2 o strip_forall o concl) thm, F) = EQUAL in
    let val false_cond_thm = hd (filter false_case_thm (CONJUNCTS boolTheory.bool_case_thm)) in
    let val if_thm = ISPECL [true_branch, false_branch] false_cond_thm
        val preferred_mark = mk_var ("mark", type_of condition) in
    let val mark = gen_variant is_constname "" (free_varsl [if_then_else_term]) preferred_mark in
    let val template = mk_eq (mk_cond (mark, true_branch, false_branch), false_branch) in
    let val if_eq_false_branch_thm = SUBST [mark |-> rw_thm] template if_thm in
      if_eq_false_branch_thm
    end end end end end end end

  (* Input: 'if ~c then t1 else t2'
   * Output: 'c |- (if ~c then t1 else t2) = t2'
   *
   * Algorithm:
   * ----------EQT_INTRO o ASSUME 'c'    --------REFL '~'
   * c |- c = T                          |- ~ = ~
   * --------------------------------------------MK_COMB    ---------boolTheory.NOT_CLAUSES
   *                c |- ~c = ~T                            |- ~T = F
   * ----------------------------------------------------------------SYM o TRANS    ------------------------------bool_case_thm
   *                        c |- F = ~c                                             |- (if F then t1 else t2) = t2
   * -------------------------------------------------------------------------------------------------------------SUBST
   *                                   c |- (if ~c then t1 else t2) = t2
   *)
  fun condition_hyp_neg_cond_eq_false_branch_thm if_then_else_term =
    let val (condition, true_branch, false_branch) = dest_cond if_then_else_term in
    let val condition_eq_true_thm = (EQT_INTRO o ASSUME o dest_neg) condition in
    let val neg_condition_eq_neg_true_thm = MK_COMB (REFL “$~ : bool -> bool”, condition_eq_true_thm)
        fun is_not_true_eq_f_thm thm = Term.compare (concl thm, “~T = F”) = EQUAL in
    let val neg_true_eq_false_thm = hd (filter is_not_true_eq_f_thm (CONJUNCTS boolTheory.NOT_CLAUSES)) in
    let val rw_thm = SYM (TRANS neg_condition_eq_neg_true_thm neg_true_eq_false_thm)
        fun false_case_thm thm = Term.compare ((#1 o dest_cond o boolSyntax.lhs o #2 o strip_forall o concl) thm, F) = EQUAL in
    let val false_cond_thm = hd (filter false_case_thm (CONJUNCTS boolTheory.bool_case_thm)) in
    let val if_thm = ISPECL [true_branch, false_branch] false_cond_thm
        val preferred_mark = mk_var ("mark", type_of condition) in
    let val mark = gen_variant is_constname "" (free_varsl [if_then_else_term]) preferred_mark in
    let val template = mk_eq (mk_cond (mark, true_branch, false_branch), false_branch) in
    let val if_eq_false_branch_thm = SUBST [mark |-> rw_thm] template if_thm in
      if_eq_false_branch_thm
    end end end end end end end end end end

  (*  A u {c} ?- t
   * --------------
   * A' u {c} ?- t'
   *
   * subterm:  'if c then t1 else t2'.
   * subterm': 't1'
   *)
  fun REDUCE_TRUE_COND_TAC mark template subterm term (A, t) =
    let val subterm_eq_thm = condition_hyp_cond_eq_true_branch_thm subterm in
      RW_SUBTERM_TAC subterm_eq_thm mark template term (A, t)
    end

  (*  A u {c} ?- t
   * --------------
   * A' u {c} ?- t'
   *
   * subterm:  'if ~c then t1 else t2'.
   * subterm': 't2'.
   *)
  fun REDUCE_FALSE_TRUE_COND_TAC mark template subterm term (A, t) =
    let val subterm_eq_thm = condition_hyp_neg_cond_eq_false_branch_thm subterm in
      RW_SUBTERM_TAC subterm_eq_thm mark template term (A, t)
    end

  (*  A u {~c} ?- t
   * ---------------
   * A' u {~c} ?- t'
   *
   * subterm:  'if c then t1 else t2'.
   * subterm': 't2'.
   *)
  fun REDUCE_FALSE_FALSE_COND_TAC mark template subterm term (A, t) =
    let val subterm_eq_thm = condition_hyp_cond_eq_false_branch_thm subterm in
      RW_SUBTERM_TAC subterm_eq_thm mark template term (A, t)
    end

  (*               A |- t
   * -----------------------------------
   * A1 u {c'} |- t1    A2 u {~c'} |- t2
   *
   * where
   * -subterm: 'if c then t1 else t2'
   * -if c is unnegated: c' = c
   * -if c is negated: ~c' = c
   *
   * A1, t1, A2 and t2 reflect the rewrite of subterm depending on whether
   * subterm is in A or t.
   *)
  fun REDUCE_BRANCH_COND_TAC mark template subterm term (A, t) =
    let val c = (#1 o dest_cond) subterm in
    let val (At, tt, vt, subtermt, termt) = REDUCE_TRUE_COND_TAC mark template subterm term (c::A, t) (* A u {} |- if c' ... *)
        val (Af, tf, vf, subtermf, termf) = 
          if (not o is_neg) c then (* if  c then t1 else t2 *)
            REDUCE_FALSE_FALSE_COND_TAC mark template subterm term ((mk_neg c)::A, t)         (* A u {~c} |- if  c ... *)
          else                     (* if ~c then t1 else t2 *)
            REDUCE_FALSE_TRUE_COND_TAC mark template subterm term ((dest_neg c)::A, t) in     (* A u { c} |- if ~c ... *)
        (* [(asms, conclutions, subterm, term, new assumptions from if conditions), ...] *)
    let val acstas = [(At, tt, subtermt, termt, SOME (hd At)), (Af, tf, subtermf, termf, SOME (hd Af))]
        val validation = fn thms =>
          let val subgoal_achieving_thmt = hd thms                               (* At |- tt *)
              val subgoal_achieving_thmf = (hd o tl) thms in                     (* Af |- tf *)
          let val intermediate_goalt = vt subgoal_achieving_thmt                 (* A u { c} |- if ~c ...*)
              val intermediate_goalf = vf subgoal_achieving_thmf                 (* A u {~c} |- if ~c ...*)
              val instantiated_lem_thm = ISPEC (if is_neg c then dest_neg c else c) boolTheory.EXCLUDED_MIDDLE in (* |- c \/ ~c *)
          let val unnegated_hyp_thm = if is_neg c then intermediate_goalf else intermediate_goalt
              val negated_hyp_thm = if is_neg c then intermediate_goalt else intermediate_goalf in
          let val goal_achieving_thm = DISJ_CASES instantiated_lem_thm unnegated_hyp_thm negated_hyp_thm in
            goal_achieving_thm
          end end end end in
      (acstas, validation)
    end end end

  (*  A ?- t
   * --------, if eq_to_rewrite = 'l = if c then t1 else t2', and c or ~c is in
   * A' ?- t'  A. A' and t' reflects the rewrite of eq_to_rewrite to t1 or t2.
   *
   *         A ?- t
   * ---------------------, if eq_to_rewrite = 'l = if c then t1 else t2'
   * A1 ?- t1     A2 ?- t2
   *
   * Double negations are not considered. For instance, it is not checked whether
   * ~~c is in A, but merely ~c and c.
   *)
  fun REDUCE_COND_TAC mark template subterm term (A, t) =
    let val c = (#1 o dest_cond) subterm in
    let val is_true = exists (fn a => same_term c a) A                                                             (* { c} |- if  c *)
        val is_pos_condition_false = if (not o is_neg) c then exists (fn a => same_term (mk_neg c) a) A else false (* {~c} |- if  c *)
        val is_neg_condition_false = if is_neg c then exists (fn a => same_term (dest_neg c) a) A else false in    (* { c} |- if ~c *)
    let val (acstas, validation) =
          if is_true then                                                     (* Condition is true due to another assumption. *)
            let val (a, c, v, s, t) = REDUCE_TRUE_COND_TAC mark template subterm term (A, t) in
              ([(a, c, s, t, NONE)], v o hd)
            end
          else if is_neg_condition_false then                                 (* Positive condition is false due to negative assumption. *)
            let val (a, c, v, s, t) = REDUCE_FALSE_TRUE_COND_TAC mark template subterm term (A, t) in
              ([(a, c, s, t, NONE)], v o hd)
            end
          else if is_pos_condition_false then                                 (* Negative condition is false due to positive assumption. *)
            let val (a, c, v, s, t) = REDUCE_FALSE_FALSE_COND_TAC mark template subterm term (A, t) in
              ([(a, c, s, t, NONE)], v o hd)
            end
          else                                                                (* Must consider both cases. *)
            REDUCE_BRANCH_COND_TAC mark template subterm term (A, t)
    in
      (acstas, validation)
    end end end

  (* 4. Identify the top-most construct on the right hand side of the given
   *	equation:
   *	•Let scalar. The left hand side the let equality is a single variable:
   *	 Reduce the let expression, go to step 4 with the resulting equation.
   *	•Let pair. The left hand side the let equality is a pair of variables:
   *	 ⬩If right hand side is a pair:
   *	  Reduce the let expression and go to step 4 with the resulting equation.
   *	 ⬩If right hand side is not a pair, and there exists and equality among
   *	  the assumptions with one side being the right hand side of the let
   *	  expression and the other side a pair:
   *	  Rewrite the right hand side of the let expression with the equation,
   *	  and go to step 4 with the resulting equation.
   *	 ⬩Otherwise:
   *	  i  Add an equation of the form r = (x, y).
   *	  ii Go to step 4 with the same equation but new assumption.
   *	•Case scalar:
   *	 ⬩Case expression is a pattern:
   *	  Reduce the case expression and go to step 4 with the resulting
   *	  equation.
   *	 ⬩Case expression is not a pattern, and there exists an equality among
   *	  the assumptions with one side being the case expression and the other
   *	  side a pattern:
   *	  Rewrite the case expression in the case construct with the pattern and
   *	  go to step 4 with the resulting equation.
   *	 ⬩Otherwise:
   *	  Add new equations of the form case_expression = patterni for each
   *	  pattern to the assumptions and go to step 4 with the new assumptions
   *	  (subgoals).
   *	•Case pair: Covered by case scalar!
   *	•If:
   *	 ⬩There exists an assumption which is the if condition or its negation:
   *	  Use the assumption to reduce the if construct.
   *	 ⬩Otherwise:
   *	  Create two new assumptions, one with the if condition and the other
   *	  with its negation, and go to step 4 with the new assumptions.
   *	•None of the above cases: Remove redundant new assumptions and terminate.
   *)
  fun REDUCE_BODY_TAC original_assumptions added_conditions mark template subterm term (A, t) =
    if is_let_scalar subterm then                       (* subterm: 'let x = t1 in t2' *)
      (* Reduces let to t2[t1/x] *)
      COMPOSE_ACST_TAC REDUCE_LET_SCALAR_TAC (REDUCE_BODY_TAC original_assumptions added_conditions) mark template subterm term (A, t)
    else if is_let_pair subterm then                    (* subterm: 'let (x, y) = t1 in t2' *)
      (* Reduces let to t2, where (x, y) = t1 is an assumption. *)
      COMPOSE_ACST_TAC REDUCE_LET_VECTOR_TAC (REDUCE_BODY_TAC original_assumptions added_conditions) mark template subterm term (A, t)
    else if is_cond subterm then                        (* subterm: 'if t1 then t2 else t3' *)
      (* IF-THEN-ELSE IS CONSIDERED BEFORE CASE SINCE IF-THEN-ELSE IS A SPECIAL
       * CASE OF CASE, AND CASE TREATMENT LEADS TO DIFFERENT RESULT.
       *)
      (* Reduce if to t1 and t2, where t1 and ~t2 are added assumptions. *)
      let val update_added_conditions = fn NONE => added_conditions | SOME new_condition => new_condition::added_conditions in
        COMPOSE_ACSTO_TAC REDUCE_COND_TAC (REDUCE_BODY_TAC original_assumptions) update_added_conditions mark template subterm term (A, t)
      end
    else if TypeBase.is_case subterm then               (* subterm: 'case t of p1 => t1 | ... | pn => tn' *)
      (* Reduce case to tis, where fresh_variable = f a and variable = pi
       * (variable is not fresh_variable in case t is an already a variable)
       * are added assumptions.
       *)
        COMPOSE_ACMTST_TAC REDUCE_CASE_SUBTERM_TAC (REDUCE_BODY_TAC original_assumptions added_conditions) mark template subterm term (A, t)
    else
      (* End of path reached. Remove new equations among the assumptions,
       * whose left hand side is a variable and that does not occur in any
       * other assumption nor the conclusion. Then terminate.
       *)
      let fun not_same t1 t2 = Term.compare (t1, t2) <> EQUAL in
      let fun not_original asm = all (not_same asm) original_assumptions
          fun not_added asm = all (fn added => not_same asm added) added_conditions in
      let val new_eqs = filter (fn a => not_original a andalso not_added a andalso is_eq a) A
          fun occurrences variable = number_of_occurrences_in_terms variable (t::A) in
      let val eqs_to_remove = filter (fn eq => let val v = boolSyntax.lhs eq in is_var v andalso occurrences v = 1 end) new_eqs in
      let fun not_eq_to_remove assumption = all (fn eq => not_same assumption eq) eqs_to_remove in
      let val A' = filter not_eq_to_remove A in
        ([(A', t, mark, template, subterm, term)], hd)
      end end end end end end

  fun is_function_application function_name term =
    if is_comb term then
      (term_to_string o #1 o strip_comb) term = function_name
    else
      false

  fun has_function_application function_name =
    has_terms_subterm_property (is_function_application function_name)

  (*         A ?- t
   * -------------------------
   * A1 ?- t1 ... Am ?- tm
   *
   * where t or an assumption in A is of the form 'lhs = function_name a1...an',
   * and each Ai ?- ti represents one unfolding path of function_name a1...an
   * without containing any let, if or case constructs, with Ai containing
   * additional assumptions resulting from if reductions, except if the
   * if-condition or its negation already occurs in A.
   *
   * Algorithm:
   * 1. Given a function name.
   * 2. Find an equation among the assumptions and the conclusion whose right hand
   *    side is an application of a function of the given name. Fix that equation,
   *    which will be rewritten in the following steps.
   * 3. Given an equation:
   *    a) Expand the function, if possible, and pass the resulting equation to
   *       step 4.
   *    b) Otherwise, the function is defined in terms of pattern matching on its
   *       parameters.
   *       i  There exists an equation among the assumptions with one side being
   *          the argument and the other side the pattern:
   *          Substitute the pattern for the argument. Go to step 3 with the
   *          resulting equation.
   *       ii Otherwise:
   *          A Add new equations of the form argument = pattern v1...vn.
   *          B Go to step 3 with the same equation and the new assumptions
   *            (subgoals).
   * 4. Identify the top-most construct on the right hand side of the given
   *    equation:
   *    •Let scalar. The left hand side the let equality is a single variable:
   *     Reduce the let expression, go to step 4 with the resulting equation.
   *    •Let pair. The left hand side the let equality is a pair of variables:
   *     ⬩If right hand side is a pair:
   *      Reduce the let expression and go to step 4 with the resulting equation.
   *     ⬩If right hand side is not a pair, and there exists and equality among
   *      the assumptions with one side being the right hand side of the let
   *      expression and the other side a pair:
   *      Rewrite the right hand side of the let expression with the equation,
   *      and go to step 4 with the resulting equation.
   *     ⬩Otherwise:
   *      i  dd an equation of the form r = (x, y).
   *      ii Go to step 4 with the same equation but new assumption.
   *    •Case scalar:
   *     ⬩Case expression is a pattern:
   *      Reduce the case expression and go to step 4 with the resulting
   *      equation.
   *     ⬩Case expression is not a pattern, and there exists an equality among
   *      the assumptions with one side being the case expression and the other
   *      side a pattern:
   *      Rewrite the case expression in the case construct with the pattern and
   *      go to step 4 with the resulting equation.
   *     ⬩Otherwise:
   *      Add new equations of the form case_expression = patterni for each
   *      pattern to the assumptions and go to step 4 with the new assumptions
   *      (subgoals).
   *    •Case pair: Covered by case scalar!
   *    •If:
   *     ⬩There exists an assumption which is the if condition or its negation:
   *      Use the assumption to reduce the if construct.
   *     ⬩Otherwise:
   *      Create two new assumptions, one with the if condition and the other
   *      with its negation, and go to step 4 with the new assumptions.
   *    •None of the above cases: Go to step 5.
   * 5. Remove, all new equations added to the assumptions whose left hand side
   *    are singleton variables not existing anywhere else within the goal.
   *)
  (* Given: 'function'
   * Returns:
   * [(|- !X. function (par11 X)...(par1n X), [par11 X, ..., par1n X]),
   *  ...
   *  (|- !X. function (parm1 X)...(parmn X), [parm1 X, ..., parmn X])]
   *)
  fun find_applicable_defs_rec function [] = []
    | find_applicable_defs_rec function (name_def::name_defs) =
      let fun is_match from = let val _ = match_term from function in true end handle _ => false in
      let fun is_applicable def =
        let val def_body = (#2 o strip_forall o concl) def in
          if is_eq def_body then
            let val (def_fun, def_pars) = (strip_comb o boolSyntax.lhs) def_body in
              if is_match def_fun then
                SOME (def, def_pars)
              else
                NONE
            end
          else
            NONE
        end in
      let fun find_applicable_subdefs (def, def_parss) =
        case is_applicable def of
          NONE => def_parss
        | SOME def_pars => def_pars::def_parss in
      let val subdefs = (CONJUNCTS o #2) name_def in
      let val applicable_def_parss = foldl find_applicable_subdefs [] subdefs in
      let val applicable_def_parsss = find_applicable_defs_rec function name_defs in
        applicable_def_parss @ applicable_def_parsss
      end end end end end end

  fun find_applicable_defs function =
    let val theory_name = #Thy (dest_thy_const function) in
    let val relevant_defs = find_applicable_defs_rec function (DB.definitions theory_name) (* Check DB.definitions. *)
        val relevant_thms = find_applicable_defs_rec function (DB.theorems theory_name) in (* Check DB.theorems in case DB.definitions did not give any useful theorems. *)
    let val applicable_defs = relevant_defs @ relevant_thms in
(*    let val applicable_defs = if null relevant_defs then find_applicable_defs_rec function (DB.theorems theory_name) else relevant_defs in (* DB.definitions did not give any useful theorems, test DB.theorems. *)*)
      applicable_defs
    end end end

  (*        A u {...f a1...an...} ?- t
   * ----------------------------------------(x1...xn denote the parameters of f.)
   * A u {...f_body[a1...an/x1...xn]...} ?- t
   *
   * or
   *
   *     A ?- ...f a1...an...
   * ----------------------------(x1...xn denote the parameters of f.)
   * A ?- f_body[a1...an/x1...xn]
   *)
  fun UNFOLD_DEF_TAC def_parss mark template subterm term (A, t) =
    let val function_application = subterm in
    let val pars_length = number_of_parameters ((type_of o #1 o strip_comb) function_application) in
    let val subterm_eq_thm = #1 (find_def (*pars_length*) function_application [] def_parss) in
      case subterm_eq_thm of
        NONE => raise (mk_HOL_ERR "helper_tactics" "UNFOLD_DEF_TAC" "Function application cannot be unfolded with respect to given list of definition theorems.")
      | (SOME subterm_eq_thm) => (* Expand function. *)
        let val (A1, t1, v1, subterm1, term1) = RW_SUBTERM_TAC subterm_eq_thm mark template term (A, t) in
          ([(A1, t1, mark, template, subterm1, term1)], v1 o hd)
        end
    end end end

  (* Unfolds a function application of the function with name @function_name.
   * Returns the subgoals and validation function, together with the new
   * equations to rewrite for each returned subgoal, for all computation paths
   * of the function.
   *
   *               'A u {a} ?- t'                                 'A u {a} ?- t'
   * ------------------------------------------ ... ------------------------------------------
   * 'A u {r} u {ai = pvi1 ... aj = pvj1} ?- s'     'A u {r} u {ai = pvin ... aj = pvjn} ?- s'
   *
   * where a or t is of form 'l = f args', and r or s are of the form
   * 'l = f_body [patterns/arguments]' and ai = pvi... are added equalities to
   * unfold f in the particular subgoal.
   *)
  fun FUN_PATHS_TAC function_name (A, t) =
    let val (mark, template, subterm, term) =
      case has_string_specified_function_application function_name (t::A) of (* Optimized version checking substring before traversing term. *)
        NONE =>
        let val error_message = concat ["No application of  ", function_name, "."] in
          raise (mk_HOL_ERR "helper_tactics" "FUN_PATHS_TAC" error_message)
        end
      | SOME (mark, template, subterm, term) => (mark, template, subterm, term) in
    let val function_application = subterm in
    let val def_parss = find_applicable_defs ((#1 o strip_comb) function_application)
        val original_assumptions = A
        val added_conditions = [] in
    let val tactic1 = SUBST_ARG_OR_ADD_ARG_PAT_SUBTERM_TAC def_parss
        val tactic2 = UNFOLD_DEF_TAC def_parss
        val tactic3 = REDUCE_BODY_TAC original_assumptions added_conditions in
    let val (acmtsts, v) = COMPOSE_ACMTSTS_TAC [tactic1, tactic2, tactic3] mark template subterm term (A, t) in
    let val subgoals = map (fn (a, c, m, tem, s, ter) => (a, c)) acmtsts in
      (subgoals, v)
    end end end end end end

  (* As FUN_PATHS_TAC but takes a function definition
   * 'function_name a1...an = function_body' instead.
   *)
  fun PTAC_CONJ definition (A, t) =
    let val definitions = CONJUNCTS definition in
    let val def_parss = map (fn thm => (thm, (#2 o strip_comb o lhs o #2 o strip_forall o concl) thm)) definitions in
    let val function_name = term_to_string ((#1 o strip_comb o lhs o #2 o strip_forall o concl o hd) definitions) in
    let val function_application_position = has_string_specified_function_application function_name (t::A) in
      if isSome function_application_position then
        let val (mark, template, subterm, term) = valOf function_application_position in
        let val function_application = subterm in
        let val original_assumptions = A
            val added_conditions = [] in
        let val tactic1 = SUBST_ARG_OR_ADD_ARG_PAT_SUBTERM_TAC def_parss
            val tactic2 = UNFOLD_DEF_TAC def_parss
            val tactic3 = REDUCE_BODY_TAC original_assumptions added_conditions in
        let val (acmtsts, v) = COMPOSE_ACMTSTS_TAC [tactic1, tactic2, tactic3] mark template subterm term (A, t) in
        let val subgoals = map (fn (a, c, m, tem, s, ter) => (a, c)) acmtsts in
          (subgoals, v)
        end end end end end end
      else
        let val error_message = concat ["No application of ", function_name, "."] in
          raise (mk_HOL_ERR "helper_tactics" "PTAC" error_message)
        end
    end end end end

  fun PTAC definition = (PTAC_CONJ definition) THEN SPLIT_ASM_TAC
    

  (****************************************************************************)
  (*End of function path expansions********************************************)
  (****************************************************************************)




  (****************************************************************************)
  (*Start of expanding argument and unfolding function definition tactic*******)
  (****************************************************************************)

  fun UNFOLD_ARGS_TAC function_name (A, t) =
    let val (mark, template, subterm, term) =
      case has_string_specified_function_application function_name (t::A) of (* Optimized version checking substring before traversing term. *)
        NONE =>
        let val error_message = concat ["No application of  ", function_name, "."] in
          raise (mk_HOL_ERR "helper_tactics" "UNFOLD_ARGS_TAC" error_message)
        end
      | SOME (mark, template, subterm, term) => (mark, template, subterm, term) in
    let val function_application = subterm in
    let val def_parss = find_applicable_defs ((#1 o strip_comb) function_application) in
    let val (acmtsts, v) = SUBST_ARG_OR_ADD_ARG_PAT_SUBTERM_TAC def_parss mark template subterm term (A, t) in
    let val subgoals = map (fn (a, c, m, tem, s, ter) => (a, c)) acmtsts in
      (subgoals, v)
    end end end end end

  (****************************************************************************)
  (*End of expanding argument and unfolding function definition tactic*********)
  (****************************************************************************)



  (****************************************************************************)
  (*Start of expanding argument and unfolding function definition tactic*******)
  (****************************************************************************)

  (* Algorithm:
   * 1. As long as there is a function application 'function_name a1...an' in the goal:
   * 2  If possible to unfold, unfold function application and terminate.
   * 3. If not possible to unfold, find argument expansion.
   * 4. Take head of expansion and find the expansion theorem.
   * 5. Produce one subgoal for each disjunct and give the disjunct as an argument.
   * 6. For each subgoal:
   *    a) Remove existentials from the disjunction equality.
   *    b) Substitute the right hand side of the disjunction for each occurrence of the left hand side in the goal.
   *    c) Goto 1.
   *
   * This tactic performs step 1 and 6.c), and invokes tactics performing steps 2 and 3-6.
   *)
  fun UNFOLD_FUN_ARGS_TAC function_name =
    (UNFOLD_FUN_TAC function_name) ORELSE
    (UNFOLD_ARGS_TAC function_name THEN UNFOLD_FUN_TAC function_name)

  (****************************************************************************)
  (*End of expanding argument and unfolding function definition tactic*********)
  (****************************************************************************)





  fun term_name_property term_name term = term_to_string term = term_name

  fun ADD_TERM_EQ_PATTERNS_TAC term_to_expand (A, t) =
    let val type_of_term_to_expand = type_of term_to_expand in
    let val nchotomy_thm = TypeBase.nchotomy_of type_of_term_to_expand in
    let val inst_nchotomy_thm = ISPEC term_to_expand nchotomy_thm in
    let val xeqs = (strip_disj o concl) inst_nchotomy_thm in
    let val ieqs = map (fn xeq => instantiate_exists xeq (t::A)) xeqs
        val subgoals = map (fn (iterm, vxs) => ((iterm::A, t), iterm)) ieqs
        fun chooses thm iterm [] = thm
          | chooses thm iterm ((vi, xi)::vxs) =                         (* iterm = s[vi/xi] *)
             let val xterm = mk_exists (xi, subst [vi |-> xi] iterm) in (* xterm = ?xi. s, since vi is fresh. *)
               chooses (CHOOSE (vi, ASSUME xterm) thm) xterm vxs
             end in
    let val validation = fn thms =>
      let val thms_ieq_vxss = zip thms ieqs in
      let val thm_xeqs = map (fn (thm, (iterm, vxs)) => chooses thm iterm vxs) thms_ieq_vxss in (* A u {?x1...xn. l = ri} |- t *)
      let val thm = DISJ_CASESL inst_nchotomy_thm thm_xeqs in (* A |- t *)
        thm
      end end end
    in
      (subgoals, validation)
    end end end end end end

  (*         A ?- t
   * ---------------------Where term whose string is equal to term_name is expanded according to its nchotomy theorem.
   * A1 ?- t1 ... An ?- tn
   *)
  fun EXPAND_TERM_TAC term_name (A, t) =
    case has_terms_subterm_property (term_name_property term_name) (t::A) of
      NONE => raise (mk_HOL_ERR "" "" "")
    | SOME (_, _, term_to_expand, _) =>
      let val (ac_eqs, v) = ADD_TERM_EQ_PATTERNS_TAC term_to_expand (A, t) in
      let val sgvs = map (fn (ac, eq) => let val (sg, v) = ASM_RW_OTHERS_TAC false eq ac in (hd sg, fn thm => v [thm]) end) ac_eqs in
      let val (subgoals, vs) = foldl (fn ((sg, v), (sgs, vs)) => (sgs @ [sg], vs @ [v])) ([], []) sgvs in (* Append gives expected order. *)
      let val validation = fn thms =>
        let fun validate_thms [] [] = []
              | validate_thms [] (thm::thms) = raise (mk_HOL_ERR "helper_tactics" "EXPAND_TERM_TAC" "More theorems than validations.")
              | validate_thms (v::vs) [] = raise (mk_HOL_ERR "helper_tactics" "EXPAND_TERM_TAC" "More validations than theorems.")
              | validate_thms (v::vs) (thm::thms) = (v thm)::(validate_thms vs thms) in
        let val subgoal_achieving_thms = validate_thms vs thms in
        let val goal_achieving_thm = v subgoal_achieving_thms in
          goal_achieving_thm
        end end end in
        (subgoals, validation)
      end end end end


  fun EXPAND_CASE_VECTOR_TAC (A, t) =
    let val vector_case_subterm_name =
      case has_terms_subterm_property pairSyntax.is_pair_case (t::A) of
        NONE => raise (mk_HOL_ERR "helper_tactics" "EXPAND_CASE_VECTOR_TAC" "No case split on vector among assumptions nor conclusion.")
      | SOME (mark, template, subterm_with_property, term) => (term_to_string o hd o #2 o strip_comb) subterm_with_property in
      (EXPAND_TERM_TAC vector_case_subterm_name THEN CASE_PATTERN_TAC) (A, t)
    end

  val CASE_VECTOR_TAC = REPEAT EXPAND_CASE_VECTOR_TAC

  (****************************************************************************)
  (*Start of equation contradiction********************************************)
  (****************************************************************************)

  (* A u {l = s, s = r} ?- t
   * -----------------------lemma: !x1...xn. l[x1...xn] <> r[x1...xn]
   *      Goal solved
   *)
  fun DISTINCT_CONTR_TAC asm_l_eq_s asm_s_eq_r l_neq_r_thm (A, t) =
    let val (subgoals1, validation1) = RM_ASM_RW_ASM_TAC asm_s_eq_r asm_l_eq_s (A, t)
        val (s, r) = dest_eq asm_s_eq_r
        val (l, s) = dest_eq asm_l_eq_s in
    let val unquantified_l_neq_r_thm = SPEC_ALL l_neq_r_thm
        val asm_l_eq_r = mk_eq (l, r) in
    let val matching = match_term ((#1 o dest_imp o concl) unquantified_l_neq_r_thm) asm_l_eq_r in
    let val l_eq_r_hyp_false_lemma = UNDISCH (INST_TY_TERM matching unquantified_l_neq_r_thm) in
    let val (subgoals2, validation2) = ASSUME_TAC l_eq_r_hyp_false_lemma (hd subgoals1) in
    let val (subgoals3, validation3) = SOLVE_F_ASM_TAC (hd subgoals2) in
      (subgoals3, fn thms => validation1 [validation2 [validation3 thms]])
    end end end end end end

  (* Inputs:
   * -eq1: l1 = r1
   * -eq2: l2 = r1
   * -neq_thm: l <> r
   * -(A, t): goal
   *
   * Output:
   * -NONE: if eq1 and eq2 do not contradict each other implied by thm.
   * -SOME (subgoals, validation): if eq1 and eq2 contradict each other implied
   *  by thm, where subgoals is empty, meaning that the goal is solved.
   *)
  fun is_contradiction_eqs eq1 eq2 neq_thm (A, t) =
    let val (l1, r1) = dest_eq eq1
        val (l2, r2) = dest_eq eq2
        val (l, r) = (dest_eq o dest_neg o concl o SPEC_ALL) neq_thm
        fun is_same t1 t2 = Term.compare (t1, t2) = EQUAL
        fun is_match from to = let val _ = match_term from to in true end handle _ => false in
      if is_same l1 l2 then                                                (* eq1: s = l, eq2: s = r *)
        let val (subgoals1, validation1) = REFL_ASM_TAC eq1 (A, t)
            val eq1' = mk_eq (r1, l1) in                                   (* eq1': l = s *)
          if is_match l r1 andalso is_match r r2 then                      (* thm: l <> r *)
            let val (subgoals2, validation2) = DISTINCT_CONTR_TAC eq1' eq2 neq_thm (hd subgoals1) in
              SOME (subgoals2, fn thms => validation1 [validation2 thms])
            end
          else if is_match r r1 andalso is_match l r2 then                 (* thm: r <> l *)
            let val (subgoals2, validation2) = DISTINCT_CONTR_TAC eq1' eq2 (GSYM neq_thm) (hd subgoals1) in
              SOME (subgoals2, fn thms => validation1 [validation2 thms])
            end
          else
            NONE
        end
      else if is_same l1 r2 then                                           (* eq1: s = l, eq2: r = s *)
        let val (subgoals1, validation1) = REFL_ASM_TAC eq1 (A, t) in      (* l = s, r = s *)
        let val (subgoals2, validation2) = REFL_ASM_TAC eq2 (hd subgoals1) (* l = s, s = r *)
            val eq1' = mk_eq (r1, l1)                                      (* eq1': l = s *)
            val eq2' = mk_eq (r2, l2) in                                   (* eq2': s = r *)
          if is_match l r1 andalso is_match r l2 then                      (* thm: l <> r *)
            let val (subgoals3, validation3) = DISTINCT_CONTR_TAC eq1' eq2' neq_thm (hd subgoals2) in
              SOME (subgoals3, fn thms => validation1 [validation2 [validation3 thms]])
            end
          else if is_match r r1 andalso is_match l l2 then                 (* thm: r <> l *)
            let val (subgoals3, validation3) = DISTINCT_CONTR_TAC eq1' eq2' (GSYM neq_thm) (hd subgoals2) in
              SOME (subgoals3, fn thms => validation1 [validation2 [validation3 thms]])
            end
          else
            NONE
        end end
      else if is_same r1 l2 then                                           (* eq1: l = s, eq2: s = r *)
        if is_match l l1 andalso is_match r r2 then                        (* thm: l <> r *)
          SOME (DISTINCT_CONTR_TAC eq1 eq2 neq_thm (A, t))
        else if is_match r l1 andalso is_match l r2 then                   (* thm: r <> l *)
          SOME (DISTINCT_CONTR_TAC eq1 eq2 (GSYM neq_thm) (A, t))
        else
          NONE
      else if is_same r1 r2 then                                           (* eq1: l = s, eq2: r = s *)
        let val (subgoals1, validation1) = REFL_ASM_TAC eq2 (A, t)
            val eq2' = mk_eq (r2, l2) in                                   (* eq2': s = r *)
          if is_match l l1 andalso is_match r l2 then                      (* thm: l <> r *)
            let val (subgoals2, validation2) = DISTINCT_CONTR_TAC eq1 eq2' neq_thm (hd subgoals1) in
              SOME (subgoals2, fn thms => validation1 [validation2 thms])
            end
          else if is_match r l1 andalso is_match l l2 then                 (* thm: r <> l *)
            let val (subgoals2, validation2) = DISTINCT_CONTR_TAC eq1 eq2' (GSYM neq_thm) (hd subgoals1) in
              SOME (subgoals2, fn thms => validation1 [validation2 thms])
            end
          else
            NONE
        end        
      else
        NONE
    end

  (* A u {l1 = r1, l2 = r2} ?- t
   * ---------------------------
   *            -
   *
   * Solves goal if l1 = l2, l1 = r2, r1 = l2, or r1 = r2, and
   * lemma states r1 <> r2, r2 <> r1, or ...
   *)
  fun CONTR_EQ_ASMS_TAC neq_thm (A, t) =
    let fun is_same t1 t2 = Term.compare (t1, t2) = EQUAL in
    let fun distinct_eq eq1 eq2 = not (is_same eq1 eq2 orelse let val (l, r) = dest_eq eq2 in is_same eq1 (mk_eq (r, l)) end)
        val eqs = filter is_eq A in
    let fun pair_equation equation = map (fn eq => (equation, eq)) (filter (distinct_eq equation) eqs) in
    let val paired_equations = flatten (map pair_equation eqs)
        fun is_distinct_eq_pair (eq1, eq2) (eq1', eq2') =
          (distinct_eq eq1 eq1' orelse distinct_eq eq2 eq2') andalso (distinct_eq eq2 eq1' andalso distinct_eq eq1 eq2') in
    let fun remove_duplicate_eq_pairs [] = []
          | remove_duplicate_eq_pairs (eq_pair::eq_pairs) =
            let val no_duplicate_eq_pairs = remove_duplicate_eq_pairs eq_pairs in
              if all (is_distinct_eq_pair eq_pair) no_duplicate_eq_pairs then
                eq_pair::no_duplicate_eq_pairs
              else
                no_duplicate_eq_pairs
            end in
    let val distinct_eq_pairs = remove_duplicate_eq_pairs paired_equations
        fun find_contr_eq [] = raise (mk_HOL_ERR "helper_tactics" "CONTR_EQ_ASMS_TAC" "No contradicting equalities.")
          | find_contr_eq ((eq1, eq2)::eqs) =
            case is_contradiction_eqs eq1 eq2 neq_thm (A, t) of
              NONE => find_contr_eq eqs
            | SOME (subgoal, validation) => (subgoal, validation) in
      find_contr_eq distinct_eq_pairs
    end end end end end end

  (****************************************************************************)
  (*End of equation contradiction**********************************************)
  (****************************************************************************)







  (* A u {...substring...} ?- t
   * --------------------------
   *          A ?- t
   *)
  fun REMOVE_SUBSTRING_ASMS_TAC substring (A, t) =
    let val A' = filter (fn a => not (String.isSubstring substring (term_to_string a))) A in
      ([(A', t)], fn thms => hd thms)
    end

  (* A u {...substring1..., ..., ...substringn...} ?- t
   * --------------------------------------------------
   *                     A ?- t
   *)
  fun REMOVE_SUBSTRINGS_ASMS_TAC [] = ALL_TAC
    | REMOVE_SUBSTRINGS_ASMS_TAC (substring::substrings) =
        REMOVE_SUBSTRING_ASMS_TAC substring THEN REMOVE_SUBSTRINGS_ASMS_TAC substrings

  (*  A u {a1, a2} ?- t
   * -------------------
   * A u {a1 /\ a2} ?- t
   *
   * Algorithm:
   * --------ASSUME    --------ASSUME
   * a1 |- a1          a2 |- a2
   * --------------------------
   *     a1, a2 |- a1 /\ a2         a1 /\ a2 |- t
   *     ----------------------------------------PROVE_HYP
   *                     a1, a2 |- t
   *)
  fun HYPS_TO_CONJ_TAC a1 a2 (A, t) =
    let val A' = filter (fn a => not (Term.compare (a, a1) = EQUAL orelse Term.compare (a, a2) = EQUAL)) A in
    let val A'' = (mk_conj (a1, a2))::A'
        val validation = fn thms =>
          let val subgoal_achieving_thm = hd thms in
          let val a1_thm = ASSUME a1
              val a2_thm = ASSUME a2 in
          let val a1_a2_thm = CONJ a1_thm a2_thm in
          let val goal_achieving_thm = PROVE_HYP a1_a2_thm subgoal_achieving_thm in
            goal_achieving_thm
          end end end end in
      ([(A'', t)], validation)
    end end

  (* A u {P, ~P} ?- t
   * ----------------
   *       -
   *)
  fun CONTR_ASMS_TAC (A, t) =
    let fun is_same t1 t2 = Term.compare (t1, t2) = EQUAL in
    let fun is_contradiction t1 t2 = is_same (mk_neg t1) t2 orelse is_same t1 (mk_neg t2) in
      case List.find (fn a1 => exists (fn a2 => is_contradiction a1 a2) A) A of
        NONE => raise (mk_HOL_ERR "" "" "")
      | SOME a =>
        let val (pos, neg) = if exists (is_same (mk_neg a)) A then (a, mk_neg a) else (dest_neg a, a) in
        let val (subgoals1, validation1) = HYPS_TO_CONJ_TAC pos neg (A, t)
            val pos_and_neg = mk_conj (pos, neg) in
        let val matching = match_term ((#1 o dest_imp o concl) boolTheory.NOT_AND) pos_and_neg in
        let val contr_thm = UNDISCH (INST_TY_TERM matching boolTheory.NOT_AND) in
        let val (subgoals2, validation2) = ASSUME_TAC contr_thm (hd subgoals1) in
        let val (subgoals3, validation3) = SOLVE_F_ASM_TAC (hd subgoals2) in
          (subgoals3, fn thms => validation1 [validation2 [validation3 thms]])
        end end end end end end
    end end

  (* A u {P} ?- t
   * ------------lemma: B |- !x1...xn. ~P[x1...xn], where B is a subset of A.
   *)
  fun HYP_CONTR_NEG_LEMMA_TAC lemma (A, t) =
    let val unnegated_lemma = (#1 o dest_imp o concl o SPEC_ALL) lemma in
    let fun is_match a = let val _ = match_term unnegated_lemma a in true end handle _ => false in
      case List.find is_match A of
        NONE => raise (mk_HOL_ERR "helper_tactics" "HYP_COMNTR_LEMMA_TAC" "Lemma cannot be instantiated to contradict an assumption.")
      | SOME assumption =>
        let val matching = match_term unnegated_lemma assumption in
        let val instantiated_lemma = UNDISCH (INST_TY_TERM matching (SPEC_ALL lemma)) in
        let val (subgoals1, validation1) = ASSUME_TAC instantiated_lemma (A, t) in
        let val (subgoals2, validation2) = SOLVE_F_ASM_TAC (hd subgoals1) in
          (subgoals2, fn thms => validation1 [validation2 thms])
        end end end end
    end end

  (* A u {P} ?- t
   * ------------P = ~P' or ~P = P'.
   *     -
   *
   * lemma: B |- !x1...xn. P'[x1...xn], B is a subset of A.
   *)
  fun HYP_CONTR_NEQ_LEMMA_TAC lemma =
    HYP_CONTR_NEG_LEMMA_TAC lemma ORELSE
    HYP_CONTR_NEG_LEMMA_TAC (GSYM lemma)









  fun CONTR_NEG_ASM_TAC_REC lem_thm invalid_tyrs invalid_ters ote2 oteivs2 otyivs2 ([], t) =
      raise (mk_HOL_ERR "helper_tactics" "CONTR_NEG_ASM_TAC" "No assumption contradicting the given lemma.")
    | CONTR_NEG_ASM_TAC_REC lem_thm invalid_tyrs invalid_ters ote2 oteivs2 otyivs2 (asm::asms, t) =
      let val (oteivs1, asm_body) = strip_forall asm
          val otyivs1 = [] in (* Assumptions cannot be type instantiated. *)
        if is_neg asm_body then
          let val ote1 = dest_neg asm_body in
          let val instantiations = find_equality_instantiations invalid_tyrs invalid_ters ote1 ote2 oteivs1 oteivs2 otyivs1 otyivs2 in
            if isSome instantiations then
              let val (_, tyis2, teis1, teis2, utyvs, utevs) = valOf instantiations in
                if null utevs then (* All instantiable variables must be instantiated: P /\ !y. ~... is not a contradiction. *)
                  let val asm_thm = INST teis1 ((SPEC_ALL o ASSUME) asm)
                      val lem_thm = INST teis2 (SPEC_ALL (INST_TYPE tyis2 lem_thm)) in
                       (* Since the goal is to be solved by this tactic, all other assumptions can be ignored. *)
                  let val (subgoals1, v1) = ASSUME_TAC asm_thm ([asm], t) in
                  let val (subgoals2, v2) = ASSUME_TAC (lem_thm) (hd subgoals1) in
                  let val (subgoals3, v3) = CONTR_ASMS_TAC (hd subgoals2) in
                    (subgoals3, fn thms => v1 [v2 [v3 thms]])
                  end end end end
                else
                  CONTR_NEG_ASM_TAC_REC lem_thm invalid_tyrs invalid_ters ote2 oteivs2 otyivs2 (asms, t)
              end
            else
              CONTR_NEG_ASM_TAC_REC lem_thm invalid_tyrs invalid_ters ote2 oteivs2 otyivs2 (asms, t)
          end end
        else
          CONTR_NEG_ASM_TAC_REC lem_thm invalid_tyrs invalid_ters ote2 oteivs2 otyivs2 (asms, t)
      end

  (* A u {!X. ~P X} ?- t
   * -------------------B |- !Y. P Y, where B is a subset of A.
   *         -
   *)
  fun CONTR_NEG_ASM_TAC lemma (A, t) =
    let val lem_thm = lemma
        val invalid_tyrs = map dest_vartype (find_tyvs (t::A))
        val invalid_ters = map term_to_string (free_varsl ((concl lemma)::t::A))
        val (oteivs2, ote2) = (strip_forall o concl) lemma
        val otyivs2 = type_vars_in_term (concl lemma) in
      CONTR_NEG_ASM_TAC_REC lem_thm invalid_tyrs invalid_ters ote2 oteivs2 otyivs2 (A, t)
    end




















  (*                    A ?- t
   * ---------------------------------------------
   * A u {case_term} ?- t    A u {~case_term} ?- t
   *)
  fun NEW_CASE_TAC case_term (A, t) =
    let val subgoals = [(case_term::A, t), ((mk_neg case_term)::A, t)]
        val validation = fn thms =>
          let val subgoal_achieving_thm1 = hd thms
              val subgoal_achieving_thm2 = (hd o tl) thms
              val case_thm = ISPEC case_term boolTheory.EXCLUDED_MIDDLE in
          let val goal_achieving_thm = DISJ_CASES case_thm subgoal_achieving_thm1 subgoal_achieving_thm2 in
            goal_achieving_thm
          end end in
      (subgoals, validation)
    end

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
  fun INST_IMP_CASE_TAC lemma1 lemma2 (A, t) =
    let fun match_lemma_to_assumptions A [] = []
          | match_lemma_to_assumptions A (lemma_assumption::lemma_assumptions) =
          let val matches = map (fn assumption => SOME (match_term lemma_assumption assumption) handle _ => NONE) A in
            case List.find (fn NONE => false | SOME match => true) matches of
              NONE => match_lemma_to_assumptions A lemma_assumptions
            | SOME NONE => match_lemma_to_assumptions A lemma_assumptions
            | SOME (SOME match) => match::(match_lemma_to_assumptions A lemma_assumptions)
          end
        val stripped_lemma1 = SPEC_ALL lemma1 in
    let val lemma_assumption_conjuncts = (strip_conj o #1 o dest_imp o concl) stripped_lemma1 in
    let val lemma_goal_match_term_types = match_lemma_to_assumptions A lemma_assumption_conjuncts in
    let val match_terms_types = unzip lemma_goal_match_term_types in
    let val (match_terms, match_types) =
      (fn (match_terms, match_types) => (flatten match_terms, flatten match_types)) match_terms_types in

    let val ilemma1 = CONJ_ANT_TO_HYP (INST_TY_TERM (match_terms, match_types) (SPEC_ALL lemma1))
        val ilemma2 = CONJ_ANT_TO_HYP (INST_TY_TERM (match_terms, match_types) (SPEC_ALL lemma2)) in
    let val unquantified_lemma_hyps1 = hyp ilemma1
        val unquantified_lemma_hyps2 = hyp ilemma2

        fun is_compl t1 t2 = if is_neg t1 then Term.compare (dest_neg t1, t2) = EQUAL else Term.compare (mk_neg t1, t2) = EQUAL in
      case List.find (fn hyp1 => exists (fn hyp2 => is_compl hyp1 hyp2) unquantified_lemma_hyps2) unquantified_lemma_hyps1 of
        NONE => raise (mk_HOL_ERR "helper_tactics" "INST_IMP_CASE_TAC" "Lemmas have no complementary conjuncts in their assumptions.")
      | SOME hyp1 =>
        let val (case_term, pos_lemma, neg_lemma) =
              if is_neg hyp1 then (dest_neg hyp1, ilemma2, ilemma1) else (hyp1, ilemma1, ilemma2) in
        let val (case_subgoals, case_validation) = NEW_CASE_TAC case_term (A, t) in
        let val pos_subgoal = hd case_subgoals
            val neg_subgoal = (hd o tl) case_subgoals in
        let val (pos_subgoals, pos_validation) = (ASSUME_TAC pos_lemma THEN SPLIT_ASM_TAC) pos_subgoal
            val (neg_subgoals, neg_validation) = (ASSUME_TAC neg_lemma THEN SPLIT_ASM_TAC) neg_subgoal in
        let val subgoals = pos_subgoals @ neg_subgoals
            val validation = fn thms =>
              let val (pos_thms, neg_thms) = split_list (length pos_subgoals) thms in
              let val pos_thm = pos_validation pos_thms
                  val neg_thm = neg_validation neg_thms in
              let val goal_achieving_thm = case_validation [pos_thm, neg_thm] in
                goal_achieving_thm
              end end end in
          (subgoals, validation)
        end end end end end
    end end end end end end end

  val CONJS_TAC = REPEAT CONJ_TAC







  (****************************************************************************)
  (*Start of false disjunct removing tactic************************************)
  (****************************************************************************)

  fun is_disjunction_with_F term =
    if is_disj term then
      let val disjuncts = strip_disj term in
        exists (fn disjunct => Term.compare (disjunct, F) = EQUAL) disjuncts
      end
    else
      false

  fun has_false_disjunct [] = NONE
    | has_false_disjunct (disjunct::disjuncts) =
        if is_disjunction_with_F disjunct then
          SOME disjunct
        else
          has_false_disjunct disjuncts

  fun remove_F_disjuncts term =
    if is_disj term then
      let val (l, r) = dest_disj term in
      let val l_without_F = remove_F_disjuncts l
          val r_without_F = remove_F_disjuncts r in
        if Term.compare (l_without_F, F) = EQUAL andalso Term.compare (r_without_F, F) = EQUAL then
          F
        else if Term.compare (l_without_F, F) = EQUAL then
          r_without_F
        else if Term.compare (r_without_F, F) = EQUAL then
          l_without_F         
        else
          mk_disj (l_without_F, r_without_F)
       end end
    else
      term

  (* A u {B \/ ... \/ F \/ ... \/ C} |- t ==> A u {B \/ ... \/ C} |- t *)
  val REMOVE_F_DISJUNCTS_TAC =
    let fun tactic (A, t) =
      case has_false_disjunct A of
        NONE => raise (mk_HOL_ERR "helper_tactics" "REMOVE_F_DISJUNCTS" "No false disjunct among the assumptions.\n")
      | SOME assumption_with_F =>
          let val A_without_F_disjunction = filter (fn assumption => Term.compare(assumption, assumption_with_F) <> EQUAL) A in
          let val assumption_without_F = remove_F_disjuncts assumption_with_F in
          let val subgoals = [(assumption_without_F::A_without_F_disjunction, t)] in
          let val validation_function =
            fn thms =>
              let val without_F_thm = hd thms in                          (* A u {B \/...\/ E} |- t *)
              let val with_F_thm = ASSUME assumption_with_F in            (* B \/...\/ F \/...\/ E |- B \/...\/ F \/...\/ E *)
              let val removed_F_thm = REWRITE_RULE [] with_F_thm in       (* B \/...\/ F \/...\/ E |- B \/...\/ E *)
                                                                          (* A u {B \/...\/ F \/... / E} |- B \/...\/ E *)
              let val assumptions_removed_F_thm = foldl (fn (a, thm) => ADD_ASSUM a thm) removed_F_thm A in
              let val goal_achieving_thm = PROVE_HYP assumptions_removed_F_thm without_F_thm in (* A u {B \/...\/ F \/...\/ E} |- t *)
                goal_achieving_thm
              end end end end end in
            (subgoals, validation_function)
          end end end end
    in
      tactic THEN (REPEAT tactic)
    end

  (* Transforms conclusion !x. ...x... to !x. (\x. ...x...) x, making P x matchable to (\x. ...x...) x
   *
   *     A ?- !x. ...x...
   * ------------------------
   * A ?- !x. (\x. ...x...) x
   *)
  fun ABS_APP_TAC (A, t) =
    let val (qv, ut) = dest_forall t in
    let val app_ut = mk_comb (mk_abs (qv, ut), qv) in
    let val qbeta = mk_forall (qv, app_ut)
        val validation = fn thms =>
            let val mark = genvar bool in
            let val thm = GEN qv (SUBST [mark |-> BETA_CONV app_ut] mark (((SPEC qv) o hd) thms)) in
              thm
            end end in
      ([(A, qbeta)], validation)
    end end end

  (****************************************************************************)
  (*End of false disjunct removing tactic**************************************)
  (****************************************************************************)


(*
ADTAC:						A u {P, P ==> Q} ?- t + remove_asm								A u {Q} ?- t or A u {P, Q} ?- t depending on whether remove_asm = true or remove_asm = false
INST_IMP_ASM_TAC:			A u {!x1...xn. P ==> Q} ?- t									==> 'A u {Q} |- t', if A ⊇ P with appropriately instantiated xi.
INST_IMP_TAC:				A ?- t + |- !x1...xn. P ==> Q									==> 'A u {Q} |- t', if A ⊇ P with appropriately instantiated xi.
INST_IMP_CASE_TAC:			A ?- t + lemma1 + lemma2									==> A u {r', s1'} ?-t and A u {~r', s2'} ?- t, lemma1: |- !x1...xn. C1 /\ ... /\ r /\ ... Cm ==> s1 and lemma2: |- !x1...xn. D1 /\ ... /\ ~r /\ ... Dp ==> s2.
INST_IMP_EQ_TAC:			A ?- t + |- !x1...xn. P /\ yi = fi x1...ym ==> Q				==> 'A u {Q} u {yi = fi values} |- t[yi/fi values]', if A ⊇ P with appropriately instantiated xi.
INST_IMP_ASM_GOAL_TAC:		A u {!X. s ==> t} ?- t'											==> 'A |- ?X'. s[V/(X\X')]', V, X, X' are terms/variables, V is inferred by matching subterms of s to subterms of A. X' ⊆ X are unmatched X variables.
IMP_LEMMA_SOLVE_GOAL_TAC:	A u {A1, ..., An} ?- t + !X. A1 X /\ ... /\ An X ==> t X		==> -. Solves goal.
PART_INST_IMP_TAC:			'A |- t' + '|- !x1...xn. C1 x1..xn /\ ... ==> P x1...xn'		==> 'A u {P v1...vn} |- t', where assumptions in A satisfy some 'Ci v1...vn', and other 'Cj x1...xn' are simplifiable to true.
ADD_INST_TAC:				'A |- t' + '|- !x1...xn. s x1..xn' + ["v1"..."vn"]				==> 'A u {s[to_term "v1"...to_term "vn"/x1...xn]} |- t'
INST_IMP_ASM_MP_CON_TAC:	A u {!XY. P XY ==> t(XY)} ?- t(V)								==> A ?- ?X'. P X'V, where Y is matched against V and X against other assumptions in A.
ITAC:						A ?- t + B |- !X. C1 /\.../\ Cn ==> C, B subset of A.			==>	A u {C V} ?- t, V instantiates X, based on Ci and equalities in A, all Ci in the lemma can be discharged.

ASM_INST_ASM_TAC:			A u {P} u {!x1...xn. A /\ ...P... /\ B ==> C} ?- t'				==> A u {A /\ ... /\ B ==> C}[v1...vn/x1...xn] ?- t, with xi appropriately instantiated with vi.
KEEP_ASM_INST_ASM_TAC:		A u {P} u {!x1...xn. A /\ ...P... /\ B ==> C} ?- t'				==> A u {P} u {A /\ ... /\ B ==> C}[v1...vn/x1...xn] ?- t, with xi appropriately instantiated with vi.
ASM_INST_IMP_ASM_ONCE_TAC:	A u {P, !x1...xm y1...yn. A /\ ... /\ B /\ P(x1...xm) /\ C /\ ... /\ D ==> E} ?- t			==>		A u {P, !y1...yn. A /\ ... /\ B /\ C /\ ... /\ D ==> E} ? -t, conjunct removed from antecedent among assumptions.
ASM_INST_IMP_ASM_TAC:		A u {Ai, ..., Aj, !x1...xm y1...yn. A /\ ... /\ Ai /\ ... /\ C /\ ... /\ Aj /\ ... /\ D ==> E} ?- t		==> A u {Ai, ..., Aj, !y1...yn. A /\ ... /\ ... /\ C /\ ... /\ D ==> E} ? -t, conjuncts removed from antecedent.
ASMS_SIMP_QIMP_TAC:			A u {P, !X. Q X , !Y. ...P Y...Q Y... ==> R Y} ?- t				==>	A u {P, !X'. Q VX', !Y'. ...P VY'...Q VY'... ==> R VY'} ?- t, assumptions, quantified or not, are used to simplify implications, quantified or not.
ASM_EQ_INST_ASM_IMP_TAC:	A u {l1=r1...ln=rn, Ai r1...ln, !X Y. A1 X Y /\.../\ Ai Y l1...rn /\.../\ Am X Y ==> A X Y} ?- t ==> A u {l1=r1...ln=rn, Ai r1...ln, !X Y. A1 X Y /\.../\ Am X Y ==> A X Y} ?- t, simplifies implication with assumptions.
AITAC:						A u {!X. C1 /\.../\ Cn ==> C} ?- t								==> A u {C} ?- t, if Ci are in A or can be derived to be in A by means of equations in A.
SIMP_QIMP_ASM_TAC:			A u {!x1...xn. ... /\ xi = si /\ ... ==> s} ?- t				==> A u {!x1...xn. ... @ ... ==> s} ?- t. Instantiates xi to si and removes the conjunct being part of an implication which may contain other connectives.

INST_EXIST_ASM_TAC:			A u {?x1...xn. P} |- t + ?x1...xn. P							==> 'A[x1'...xn'/x1...xn] u {P}[x1'...xn'/x1...xn] |- t[x1'...xn'/x1...xn]', where x1'...xn' are fresh with respect to A, P and t.
AXTAC:						A u {?x1...xn. P, ?y1...xm. Q, ...} |- t						==> 'A[x1'...xn'/x1...xn, y1'...ym'/y1...ym, ...] u {P, Q, ...}[x1'...xn'/x1...xn, y1'...ym'/y1...ym, ...] |- t[x1'...xn'/x1...xn, y1'...ym'/y1...ym, ...]'
INST_EXISTS_TAC:			A |- ?x1...xn. t												==> 'A |- t'
PAXTAC:						A ?- ?X. t														==>	'A ?- ?X'. t[V/(X\X')], where V are identified via a matching of subterms of t with subterms of A. X' are variables failed to be matched.
INST_EXISTS_WITH_ASM_TAC:	A u {t[v1...vn/x1...xn]} |- ?x1...xn. t							==> 'A |- t[v1...vn/x1...xn]
INST_EXISTS_NAMES_TAC:		A |- ?x1...xn. t' + [name1, ..., namen]							==> 'A |- t[mk_var name1... mk_var namen/x1...xn]'
INST_SCALAR_EQ_EXISTS_TAC:	A ?- ?x. x = y or A ?- ?x. y = x								==>	'A ?- y = y
INST_VECTOR_EQ_EXISTS_TAC:	A ?- ?XY. XY' = X'Y'											==>	'A ?- X'Y' = X'Y'', where X, X', Y, X' are vectors of variables.
INST_EQ_EXISTS_TAC:			A ?- ?XY. XY' = X'Y'											==> 'A ?- X'Y' = X'Y'', where X, X', Y, X' are one scalar variable or vectors of variables.
EXISTS_PAT_TAC:				A ?- ?x. t(x) = t(t1) or A ?- ?x. t(x) = t(t1)					==> -
ASM_NOT_EXISTS_TO_FORALL_NOT_TAC:	A u {~?x. P x} ?- t										==> A u {!x. ~P x} ?- t
NEG_FORALL_TAC				A u {~!x1 ... xn. s(x1, ..., xn)} ?- t							==> A u {~s(y1, ... yn)}, where yi are fresh variables after instantiating the x's in ~!x. s <=> ?x. ~s.
EXISTS_EQ_TAC:				A ?- ?x1...xi...xj...xn. ... @ xi = ti @ ... @ tj = xj @...		==> A ?- ?x1...xi-1, xi+1...xj-1, xj+1...xn. ... @ ... @ ... where @ stands for logical connective (negation, conjunction, ...)

RECORD_TAC:					'(record with fi := e).fj'										==> if fi ≠ fj then 'vj' else e
ADD_RECORD_ACCESSOR_ASM_TAC:	A u {recordl = recordr} ?- t + "field_name"					==> A u {recordl.fi = recordr.fi} ?- t, where fi has the name given by field_name.


UNFOLD_FUN_TAC:				'function_name a1...an'											==> 'function_body[a1/p1...an/pn]'
UNFOLD_ARGS_TAC:			'function_name a1...an'											==> 'function_name (cons x1m...x1m)...(cons xn1...xnp)'
UNFOLD_FUN_ARGS_TAC:        'function_name a1...an'											==> 'function_body[cons x1m...x1m, ..., cons xn1...xnp/a1...an]'

EXPAND_TERM_TAC:			A ?- t															==> A1 ?- t1 ... An ?- tn, where term whose string is equal to term_name is expanded according to its nchotomy theorem.

EQ_PAIR_ASM_TAC:			'(p1, p2) = (a1, a2)'											==> 'p1 = a1 ∧ p2 = a2'
EQ_TRANS_ASM_TAC:			'A u {lhs1 = rhs1, lhs2 = rhs2} |- t'							==> 'A u {lhs1 = rhs2} |- t'
REFL_ASM_TAC:				A u {l = r} ?- t + 'l = r'										==> A u {r = l} ?- t
REFL_ASM_EQ_TAC:			A u {l = r} ?- t												==>	A u {r = l} ?- t
REFL_ASM_IN_GOAL_TAC:		'A u {lhs = rhs} |- ...rhs...'									==> 'A u {rhs = lhs} |- ...rhs...'
REFL_PRIMED_RHS_ASMS_TAC:	'{l1 = r1', ... ln = rn'} u A ?- t'								==>	'{r1' = l1, ... rn' = ln} u A ?- t'
REFL_EQ_FUN_ASM_TAC:		A u {l = functiona0_ai-1 ai...an} ?- t + "functiona0_ai"		==> A u {functiona0_ai-1 ai...an = l} ?- t
REFL_SUBSTRING_TAC:			A u {l = r} ?- t												==> A u {r = l} ?- t, substring is a substring of "l = r"

RW_ASM_LEMMA_TAC:			A u {ass} ?- t + ass + lemma									==>	A u {ass'} ?- t, where ass' is ass but rewritten with lemma, whose hypotheses must be in A.
ETAC:						'A |- t' + 'B |- !x1...xn. lhs = rhs'                    	 	==> 'A[rhs/lhs] ?- t[rhs/lhs]', for appropriately instantiated values for x1...xn. B is subset of A.
RW_HYP_LEMMA_TAC:			A u {...old...} ?- t + lemma									==> A u {...new...} ?- t, lemma is of form 'B |- !x1...xn. (!y11...y1m. t1) /\ ... /\ (!yp1...ypk. tp) and instantiatable to 'B |- old = new', B subset A.
ASETAC:						Repeteadly rewrites assumptions with given lemma.
LEMMA_TAC:					A u {a1...p...an} ?- t + A' |- !X. (!X1. l1=r1) /\...~p.../\ (!Xm. lm=rm)	==> A u {b1...F...bn} ?- t', A' subset of A. Each ai=lj[Vj/XjX] and bi=rj[Vj/XjX], and t=lj[Vj/XjX] and t'=rj[Vj/XjX] or t=t'.
RW_HYPS_TAC:				A ?- t + lemma													==> A' ?- t   Rewrites hypotheses with rw_thm, which may be a conjunction of rewrites. Can remove conjuncts if rewrites contain opposite boolean value.

ASM_RW_OTHERS_TAC:			A u {l = r} ?- t + keep + 'l = r'								==> A[r/l] ?- t[r/l] if keep is false, and A[r/l] u {l = r} ?- t[r/l] if keep is true

LRTAC:						A u {...l..., ..., ...l..., l = r} ?- t							==> A u {...r..., ..., ...r...} ?- t', t rewritten to t' if l occurs in t
NLLRTAC:					As LRTAC by r is not let x = ... in ...
NLRTAC:						[v1 = e1, ..., vn = en] @ A |- t								==> A[e1/v1, ..., en/vn] |- t[e1/v1, ..., en/vn]
ASM_LR_RW_OTHERS_KEEP_TAC:	A u {...l..., ..., ...l..., l = r} ?- t							==> A u {...r..., ..., ...r..., l = r} ?- t', t rewritten to t' if l occurs in t
ALL_LRTAC:					A u {...l..., ..., ...l..., l = r} ?- t							==> A u {...r..., ..., ...r...} ?- t', t rewritten to t' if l occurs in t
ALL_ASM_LR_RW_OTHERS_KEEP_TAC:	A u {...l..., ..., ...l..., l = r} ?- t						==> A u {...r..., ..., ...r..., l = r} ?- t', t rewritten to t' if l occurs in t

RLTAC:						A u {...r..., ..., ...r..., l = r} ?- t							==> A u {...l..., ..., ...l...} ?- t', t rewritten to t' if r occurs in t
NRLTAC:						[e1 = v1, ..., en = vn] @ A |- t								==> A[e1/v1, ..., en/vn] |- t[e1/v1, ..., en/vn]
ASM_RL_RW_OTHERS_KEEP_TAC:	A u {...r..., ..., ...r..., l = r} ?- t							==> A u {...l..., ..., ...l..., l = r} ?- t', t rewritten to t' if r occurs in t
ALL_RLTAC:					A u {...r..., ..., ...r..., l = r} ?- t							==> A u {...l..., ..., ...l...} ?- t', t rewritten to t' if r occurs in t
ALL_ASM_RL_RW_OTHERS_KEEP_TAC:	A u {...r..., ..., ...r..., l = r} ?- t						==> A u {...l..., ..., ...l..., l = r} ?- t', t rewritten to t' if r occurs in t

CONJS_TAC					A |- A1 /\ ... /\ An											==> A |- A1, ..., A|- An

RM_ASM_RW_ASM_TAC:			'A u {lhs = rhs, ...lhs...} ?- t' + 'lhs=rhs' + '...lhs...'		==>	'A u {...rhs...} ?- t'
KEEP_ASM_RW_ASM_TAC:		'A u {lhs = rhs, ...lhs...} ?- t' + 'lhs=rhs' + '...lhs...'		==>	'A u {lhs = rhs, ...rhs...} ?- t'
ASM_EQ_RW_ASM_TAC:			'A u {lhs = rhs, ...lhs...} |- t'								==> 'A u {...rhs...} |- t'
KEEP_ASM_EQ_RW_ASM_TAC:		'A u {lhs = rhs, ...lhs...} |- t'								==> 'A u {lhs = rhs,...rhs...} |- t'
RM_ASM_EQS_RW_TAC:			'A u {l1=r1...ln=rn} u {...l1...ln} ?- t'						==>	'A u {...r1...rn} ?- t[ri/li]'
ASM_RHS_RW_ASM_TAC:			A u {lhs = rhs, ...rhs...} ?- t'								==> A u {...lhs...} |- t
ASM_RHS_RW_ASMS_TAC:		A u {lhs = rhs} u {...lhs..., ..., ...lhs...} ?- t				==> A u {...rhs..., ..., ...rhs...} ?- t
ASM_VAR_EQ_RW_ASMS_TAC:		'{v1=v2 ... v(n-1)=vn} u {...v1...v(n-1)...} u A ?- t'			==>	'{...v2... ... ...vn...} u A ?- t'
RM_RHS_ASM_RW_ASM_TAC:		A u {lhs = rhs, ...rhs...} ?- t + 'lhs = rhs'					==> A u {...lhs...} ?- t
KEEP_RHS_ASM_RW_ASM_TAC:	A u {lhs = rhs, ...rhs...} ?- t + 'lhs = rhs'					==> A u {lhs = rhs, ...lhs...} ?- t
QLRTAC:			A u {...L X..., ...L Y...} u {!V. L V = R V} ?- ...L Z...		==> A u {...R X..., ...R Y...} ?- ...R Z...
QRLTAC:			A u {...R X..., ...R Y...} u {!V. L V = R V} ?- ...R Z...		==> A u {...L X..., ...L Y...} ?- ...L Z...
QEQ_RW_LHS_ASM_KEEP_TAC:	A u {...L X..., ...L Y...} u {!V. L V = R V} ?- ...L Z...		==> A u {...R X..., ...R Y...} u {!V. L V = R V} ?- ...R Z...
QEQ_RW_RHS_ASM_KEEP_TAC:	A u {...R X..., ...R Y...} u {!V. L V = R V} ?- ...R Z...		==> A u {...L X..., ...L Y...} u {!V. L V = R V} ?- ...L Z...

APP_SCALAR_TAC:				'(\x. body) argument'											==> 'body[argument/x]'
APP_PAIR_TO_CURRY_TAC:		'(\(p1, p2). body) (a1, a2)'									==> '(\p1 p2. body) a1 a2'
ABS_APP_TAC:				A ?- !x. ...x...												==>	A ?- !x. (\x. ...x...) x
LETS_TAC:					'let x1 = e1; ... xn = en in body'												==> 'body[e1/x1, ..., en/xn] e'
ONCE_LETS_TAC:				'let x = e in b'												==> 'body[e/x] e'
BSIM_ONCE_LETS_TAC			{let x = e in b, let y = f in c} u A |- t						==> {b[e/x], c[f/y]} u A |- t
CASE_PATTERN_TAC:			'case p x1..xn of ...| pi -> funi x1...xn | ... '				==> 'funi x1...xn' if p matches pi.
SPLIT_SCALAR_CASE_TAC:		'A u {b} |- t'													==>	'A u {c1} |- s1' + ... + 'A u {cm} |- sm', b/t have subterm of the form 'case x of p1 => t1 |...| pn => tn' and Ci/si have new subterm '...ti...'
SPLIT_VECTOR_CASE_TAC:		'A u {b} |- t'												==> 'A u {c1} |- s1' + ... + 'A u {cm} |- sm', b/t have subterm of the form 'case (x1...xn) of p1 => t1 |...| pn => tn' and Ci/si have new subterm '...ti...'
CASE_VECTOR_TAC				'case v of (x1, ..., xn) -> fun x1 ... xn'						==> fun v1 ... vn. That is, expands the vector v to (v1, ..., vn) and removes the case.
COND_TAC:					'if t0 then t1 else t2'											==> 't1' or 't2' depending on whether t0 or ¬t0 is an assumption.
CONDS_TAC:					'if t0 then t1 else t2'											==> 't1' or 't2' depending on whether t0 or ¬t0 is an assumption or t0 is of the form x = x.
IF_SPLIT_TAC:				'if t0 then t1 else t2'											==> 't1' and 't2'.
CASE_EQ_TAC:				A ?- t + l_name + r_name										==> A[r_name/l_name] ?- t[r_name/l_name], and A u {l_name <> r_name} ?- t.

UNFOLD_TUPLE_VARS_TAC:		'(c1, ..., cn) = (v1, ..., vm)'									==> '(c1, ..., cn) = (v1, ..., vm, ..., vn)', including let expressions.

ASMS_IMP_CON_TAC:			A u {t(X), eq1, ..., eqn} ?- t(Y)								==> -, if there exists eqi in A such that t[eqi/X] = t(Y), and eqi = 'xi = yi' or eqi = 'yi = xi'.

REMOVE_F_DISJUNCTS_TAC:		'A u {B \/ ... \/ F \/ ... \/ C} |- t'							==> 'A u {B \/ ... \/ C} |- t'
SOLVE_F_ASM_TAC:			'A u {F} |- t'													==> '' (Solves goal.)
CONTR_EQ_ASMS_TAC:			A u {l1 = r1, l2 = r2} |- t + lemma								==> '' (Solves goal.), where lemma implies that l1 = r1 and l2 = r2 contradict each other, potentially after reflecting the equations.
CONTR_ASMS_TAC:				A u {P, ~P} ?- t												==> -
HYP_CONTR_NEQ_LEMMA_TAC:	A u {P} ?- t + lemma											==> -, lemma: B |- !x1...xn. P'[x1...xn], B is a subset of A. P = ~P' or ~P = P'.
CONTR_NEG_ASM_TAC:			A u {!X. ~P X} ?- t + B |- !Y. P Y, where B is a subset of A.	==> -.

STAC:																						==> -. Attempts to solve a goal by rewriting assumptions and then derive the conclusion from the rewritten assumptions.

SPLIT_ASM_DISJS_TAC:		A u {A1 \/ ... \/ An} ?- t										==> A u {A1} |- t ... A u {An} ?- t
NEW_CASE_TAC:				A ?- t + case_term												==> A u {case_term} ?- t    A u {~case_term} ?- t

REMOVE_DUPLICATE_ASMS_TAC:	{a, ..., a} u ... u {b, ..., b} u A ?- t						==>	A ?- t
RM_SINGLE_LHS_ASMS_TAC:		A u {l1 = r1...ln = rn} ?- t									==>	A ?- t, where each li does not occur in any other assumption nor t.
REMOVE_SINGLE_VAR_EQ_ASMS_TAC:	{var1 = t1, ..., tn = varn} u A ?- t						==> A ?- t, where vi only occurs among all assumptions and the conclusion t.
RM_ASM_IDS_TAC:				A u {t1 = t1, ..., tn = tn} ?- t								==>	A ?- t
REMOVE_SUBSTRING_ASMS_TAC:	A u {...substring...} ?- t + "substring"						==> A ?- t
REMOVE_SUBSTRINGS_ASMS_TAC:	A u {...s1..., ..., ...sn...} ?- t + ["s1", ..., "sn"]			==> A ?- t

FUN_PATHS_TAC:				A ?- t + function_name											==> A1 ?- t1 ... An ?- tn, where Ai ?- ti is the resulting goal after expanding all evaluation paths (if, let, case) of the function.
PTAC:						A ?- t + function definition theorem							==> A1 ?- t1 ... An ?- tn, where Ai ?- ti is the resulting goal after expanding all evaluation paths (if, let, case) of the function.
REDUCE_RHS_TAC:				A ?- t							==> A1 ?- t1 ... An ?- tn, where Ai ?- ti is the resulting goal after expanding all evaluation paths (if, let, case) of an assumption equation whose left side contains let, if, case.

SIMP_ANT_RULE:				A |- B ==> C													==> A |- B' ==> C, where B' is a simplification of B, for instance removing conjuncts of the form x = x.
REMOVE_ID_EQ_ANT_CONJS_RULE:	A |- Ai /\ x1 = x1 /\ ... /\ xn = xn /\ Aj ==> B			==> A |- Ai /\ Aj ==> B
HYP_TO_CONJ_RULE:			'{A, ..., B} |- C'												==>	'|- A /\ B ==> C'
RM_ANT_CONJ_SINGLE_LHS_EQS_ANT_RULE:'|- A /\ ... lhs = rhs ... /\ B ==> C'					==>	'|- A /\ ... /\ B ==> C', with lhs not occuring anywhere else in the goal.
MERGE_IMP_LEM_RULE:			'|- !x1...xn. A/\...B.../\C ==> D' + '|- !x1...xn. A/\...~B.../\ C ==> D'	==>				'|- !x1...xn. A /\ ... /\ C ==> D'
MERGE_IMP_BOOL_CASE_RULE:	'|- !x1...xn y. ...A /\ y = c1 /\ B... ==> C' + ... + '|- !x1...xn y. ...A /\ y = cm /\ B... ==> C'	==>	'|- !x1...xn. ...A /\ B... ==> C', possible values of y are {c1...cm}, and n may be 0 and y may not be quantified.
MERGE_IMP_FUN_ARG_CASE_RULE:	'|- !X y. A /\ ... y = f X value1 ... /\ B ==> C' + ... + '|- !X y. A /\ ... y = f X valuen ... /\ B ==> C'	==>	'|- !name_of_quantifier X y. A /\ ... y = f X name_of_quantifier ... /\ B ==> C'
MERGE_IMP_EQ_CASES_RULE:	'|- !x1...xn y. y = construct1 x1...xn /\ ... /\ A ==> B' + ... + '|- !x1...xn y. y = constructm x1...xn /\ ... /\ B ==> C'	==>	'|- !X. A /\ ... /\ B ==> C', where there are m constructs, xi not in C.
*)
end
