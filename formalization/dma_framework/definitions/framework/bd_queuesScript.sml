open HolKernel Parse boolLib bossLib stateTheory listTheory listsTheory;

val _ = new_theory "bd_queues";

Definition BDS_TO_FETCH_DISJOINT:
BDS_TO_FETCH_DISJOINT bds_to_fetch =
!bd1 bd_ras1 bd_was1 uf1 bd2 bd_ras2 bd_was2 uf2 preceding_bds following_bds.
  preceding_bds ++ [((bd1, bd_ras1, bd_was1), uf1)] ++ following_bds = bds_to_fetch /\
  MEM ((bd2, bd_ras2, bd_was2), uf2) (preceding_bds ++ following_bds)
  ==>
  DISJOINT_LISTS bd_ras1 bd_ras2
End

(*
appended BD must not address any other appended BD
BDs in the pipeline must not address any appended BD

appended BD must not address any BD in the pipeline


Proof obligation of appending BDs:
-Appended BDs do not address other appended BDs.
-Appended BDs do not address BDs in the pipelines.
-BDs in the pipelines do not address the appended BDs
-Appended BDs are disjoint from all other queues and pipelines.

Invariant: BDs to fetch or in the pipelines do not write other BDs to fetch or in the pipelines.
*)

Definition pipeline_bds:
pipeline_bds pipelines channel_id =
  let (pending_accesses, (bds_to_update, bds_to_process, bds_to_write_back)) = THE (pipelines channel_id) in
    bds_to_update ++ bds_to_process ++ bds_to_write_back
End

Definition bds_to_fetch_ras:
  (bds_to_fetch_ras [] = []) /\
  (bds_to_fetch_ras (((bd, bd_ras, bd_was), update_flag)::bds) = bd_ras ++ (bds_to_fetch_ras bds))
End

(* This function ensures that addresses for fetching BDs only depend on the
 * immutable queue of BDs to fetch. The intention of the first two layers is to
 * provide the abstraction that the BDs to fetch are immutable. This avoids
 * dependency on the verification function bds_to_fetch, via the proof
 * obligations, which collects BDs from memory, which may be modified by DMA
 * writes.
 *
 * It is used by the first layer to enable bisimulation with the second layer.
 *)
Definition bd_read_addresses:
  (bd_read_addresses [] fetch_bd_addresses = []) /\
  (bd_read_addresses (((bd, bd_ras, bd_was), update_flag)::bds) fetch_bd_addresses =
    let fetch_bd_read_addresses = FILTER (\address. MEM address bd_ras) fetch_bd_addresses in
      fetch_bd_read_addresses)
End

(* A BD can be written (updated or written back) only if the BD does not overlap
 * any BD to fetch (apart from the BD being written back and its related BDs
 * with the same read addresses).
 *
 * Updates and write backs:
 *	1. Compute BDs to fetch.
 *	2. Extract the unrelated BDs (distinct read addresses).
 *	3. Check that write addresses do not overlap unrelated BDs.
 *	If these three conditions are satisfied and a BD write occurs, then the BD
 *  queue to fetch is preserved.
 *
 * What are reasonable properties to assume about instantiations, and can thus
 * be included in the proof obligations:
 * -Writing a BD that does not overlap any BD in the BD queue to fetch, does not
 *  modify the BD queue to fetch.
 * -Writing a BD that is in the BD queue to fetch and that only coincides
 *  (exactly the same read addresses) with its related BDs, does not modify the
 *  BD queue to fetch.
 *
 * The abstract layers (layer three) only checks properties that satisfy the
 * assumptions of proof obligations. Hence, layer three only checks that the
 * write of the BD to update/write back only addresses that and its related BDs
 * (the BD and its related BDs are disjoint from the other BDs to fetch).
 *
 * This analysis leads to the following predicate:
 * True if and only if the locations to write, identified by bd_write_addresses,
 * do not address any unrelated BDs to fetch. A BD with read addresses bd_ras2
 * is unrelated to the BD to write with read addresses bd_ras1 if bd_ras2 and
 * bd_ras1 do not contain the same addresses.
 *)
Definition DISJOINT_FROM_UNRELATED_BDS_TO_FETCH:
DISJOINT_FROM_UNRELATED_BDS_TO_FETCH device_characteristics channel_id memory internal_state bd_ras bd_was =
!bds_to_fetch' bd' bd_ras' bd_was' uflag'.
  bds_to_fetch' = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state /\
  MEM ((bd', bd_ras', bd_was'), uflag') bds_to_fetch' /\
  HAS_DIFFERENT_ELEMENTS bd_ras bd_ras'
  ==>
  DISJOINT_LISTS bd_ras' bd_was
End

(* The BD update/write back addresses @bd_write_addresses of channel @channel_id
 * must not overlap the BD read addresses of any BD of a different channel.
 *)
Definition DISJOINT_FROM_OTHER_BDS_TO_FETCH:
DISJOINT_FROM_OTHER_BDS_TO_FETCH device_characteristics channel_id memory internal_state bd_was =
!channel_id' bds_to_fetch' bd' bd_ras' bd_was' uflag'.
  VALID_CHANNEL_ID device_characteristics channel_id' /\
  channel_id' <> channel_id /\
  bds_to_fetch' = (cverification device_characteristics channel_id').bds_to_fetch memory internal_state /\
  MEM ((bd', bd_ras', bd_was'), uflag') bds_to_fetch'
  ==>
  DISJOINT_LISTS bd_ras' bd_was
End

Definition WRITE_ADDRESS_NOT_BD_TO_FETCH:
WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory internal_state was =
!channel_id bds_to_fetch bd bd_ras bd_was uflag.
  VALID_CHANNEL_ID device_characteristics channel_id /\
  bds_to_fetch = (cverification device_characteristics channel_id).bds_to_fetch memory internal_state /\
  MEM ((bd, bd_ras, bd_was), uflag) bds_to_fetch
  ==>
  DISJOINT_LISTS bd_ras was
End

(* @bd_ras and @bd_was are the read and write addresses of a single BD.
 *)
Definition CONSISTENT_BD_WRITE:
CONSISTENT_BD_WRITE device_characteristics memory internal_state was = (
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory internal_state was
)
End

Definition WRITE_ADDRESS_NOT_SCRATCHPAD:
WRITE_ADDRESS_NOT_SCRATCHPAD device_characteristics internal_state was =
!scratchpad_addresses.
  scratchpad_addresses = device_characteristics.dma_characteristics.scratchpad_addresses internal_state
  ==>
  DISJOINT_LISTS scratchpad_addresses was
End

(* DMA write requests must not address any BD queue to fetch.
 *)
Definition CONSISTENT_DMA_WRITE:
CONSISTENT_DMA_WRITE device_characteristics memory internal_state was = (
  EXTERNAL_BDS device_characteristics
  ==>
  WRITE_ADDRESS_NOT_BD_TO_FETCH device_characteristics memory internal_state was
)
End

val _ = export_theory();

