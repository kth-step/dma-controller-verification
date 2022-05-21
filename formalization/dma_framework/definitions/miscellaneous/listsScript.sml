open HolKernel Parse boolLib bossLib listTheory;

val _ = new_theory "lists";

Definition LIST1_IN_LIST2:
  LIST1_IN_LIST2 list1 list2 = EVERY (\e. MEM e list2) list1
End

Definition DISJOINT_LISTS:
  DISJOINT_LISTS list1 list2 = EVERY (\e. ~MEM e list2) list1
End

(* True if and only if list1 and list2 do not have the same elements. *)
Definition HAS_DIFFERENT_ELEMENTS:
  HAS_DIFFERENT_ELEMENTS list1 list2 =
  ?e.
    (MEM e list1 /\ ~MEM e list2) \/
    (~MEM e list1 /\ MEM e list2)
End

val _ = export_theory();
