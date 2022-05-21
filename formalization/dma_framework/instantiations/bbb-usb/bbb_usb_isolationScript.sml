open HolKernel Parse boolLib bossLib helper_tactics;
open bbb_usb_proof_obligationsTheory;

val _ = new_theory "bbb_usb_isolation";

Theorem BBB_USB_PRESERVES_INVARIANT_L4_LEMMA:
!cpu_transition INVARIANT_CPU cpu1 cpu2 memory1 memory2 device1 device2 operation.
  PROOF_OBLIGATIONS_CPU_L4 INVARIANT_CPU cpu_transition bbb_usb_device_characteristics /\
  INVARIANT_CPU memory1 cpu1 /\
  system_transition cpu_transition (device_transition_l4 bbb_usb_device_characteristics) (cpu1, memory1, device1) operation (cpu2, memory2, device2) /\
  INVARIANT_L4 bbb_usb_device_characteristics memory1 device1
  ==>
  INVARIANT_L4 bbb_usb_device_characteristics memory2 device2
Proof
INTRO_TAC THEN
MATCH_MP_TAC invariant_l4_preservationTheory.SYSTEM_PRESERVES_INVARIANT_L4_LEMMA THEN
PAXTAC THEN
ASM_REWRITE_TAC [bbb_usb_proof_obligationsTheory.BBB_USB_PROOF_OBLIGATIONS_DMA_L4]
QED

Theorem BBB_USB_DMA_READ_WRITE_LEMMA:
!cpu_transition INVARIANT_CPU cpu1 cpu2 memory1 memory2 device1 device2 operation address_bytes address.
  INVARIANT_L4 bbb_usb_device_characteristics memory1 device1 /\
  INVARIANT_CPU memory1 cpu1 /\
  system_transition cpu_transition (device_transition_l4 bbb_usb_device_characteristics) (cpu1, memory1, device1) operation (cpu2, memory2, device2)
  ==>
  (operation = device_memory_read  address_bytes ==> EVERY (bbb_usb_device_characteristics.dma_characteristics.R memory1) (MAP FST address_bytes)) /\
  (operation = device_memory_write address_bytes ==> EVERY (bbb_usb_device_characteristics.dma_characteristics.W memory1) (MAP FST address_bytes))
Proof
INTRO_TAC THEN
MATCH_MP_TAC memory_isolationTheory.DMA_READ_WRITE_LEMMA THEN
PAXTAC THEN
ASM_REWRITE_TAC [bbb_usb_proof_obligationsTheory.BBB_USB_PROOF_OBLIGATIONS_DMA_L4]
QED

val _ = export_theory();

