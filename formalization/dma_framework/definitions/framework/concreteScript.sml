open HolKernel Parse boolLib bossLib operationsTheory listsTheory;

val _ = new_theory "concrete";

(* True if and only if the memory write addresses write_addresses do not overlap
 * any read address (location) of a BD to fetch.
 *)
Definition NOT_BD_TO_FETCH:
  NOT_BD_TO_FETCH bds_to_fetch write_addresses =
    let read_addresses_of_bds_to_fetch = FLAT (MAP (\((_, ras, _), _). ras) bds_to_fetch) in
      DISJOINT_LISTS write_addresses read_addresses_of_bds_to_fetch
End

(* Appends the fetched BD to the update or process queue depending on the update
 * flag of the fetched BD.
 *)
Definition fetching_bd_fetch_bd_concrete:
  fetching_bd_fetch_bd_concrete operation_fetch_bd internal_state channel byte_tag =
    let (internal_state, fetch_result) = operation_fetch_bd internal_state byte_tag in
    case fetch_result of
    | NONE => (internal_state, channel)
    | SOME (bd_ras_was, update) => (internal_state, append_bds_to_update channel bd_ras_was)
    | SOME (bd_ras_was, no_update) => (internal_state, append_bds_to_process channel bd_ras_was)
End

val _ = export_theory();
