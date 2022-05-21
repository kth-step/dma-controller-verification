open HolKernel Parse boolLib bossLib stateTheory operationsTheory;

val _ = new_theory "abstract";

(* Given a DMA channel state and a queue of abstract BDs to fetch, fetches the
 * first BD from the queue of BDs to fetch and puts the fetched BD either in the
 * update BD queue or the process BD queue.
 *)
Definition fetching_bd_update_qs_abstract:
(fetching_bd_update_qs_abstract channel [] = channel) /\

(fetching_bd_update_qs_abstract channel ((bd_ras_was, no_update)::fetch_entries) =
  update_channel_qs channel [fetch_queue fetch_entries; process_queue (channel.queue.bds_to_process ++ [bd_ras_was])]) /\

(fetching_bd_update_qs_abstract channel ((bd_ras_was,    update)::fetch_entries) =
  update_channel_qs channel [fetch_queue fetch_entries; update_queue (channel.queue.bds_to_update ++ [bd_ras_was])])
End

(* Fetching BDs from abstract queue.
 *)
Definition fetching_bd_fetch_bd_abstract:
fetching_bd_fetch_bd_abstract operation_fetch_bd internal_state channel byte_tags =
  let (internal_state, fetch_result) = operation_fetch_bd internal_state byte_tags in
    case fetch_result of
    | NONE => (internal_state, channel)
    | SOME fetch_result => (internal_state, fetching_bd_update_qs_abstract channel channel.queue.bds_to_fetch)
End

val _ = export_theory();

