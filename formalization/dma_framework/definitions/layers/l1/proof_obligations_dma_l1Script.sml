open HolKernel Parse boolLib bossLib;
open stateTheory;
open proof_obligationsTheory;

val _ = new_theory "proof_obligations_dma_l1";

Definition PROOF_OBLIGATIONS_DMA_L1:
PROOF_OBLIGATIONS_DMA_L1 device_characteristics = (
  PROOF_OBLIGATION_SCHEDULER device_characteristics /\
  PROOF_OBLIGATION_UPDATE_WRITES_DECLARED device_characteristics /\
  PROOF_OBLIGATION_WRITE_BACK_WRITES_DECLARED device_characteristics /\
  PROOF_OBLIGATION_READABLE_WRITABLE device_characteristics (*/\
  PROOF_OBLIGATION_PROCESS_REGISTER_RELATED_MEMORY_REPLIES_NOT_ADDING_MEMORY_REQUESTS device_characteristics*)
  )
End

val _ = export_theory();

