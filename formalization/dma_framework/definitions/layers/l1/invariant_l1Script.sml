open HolKernel Parse boolLib bossLib helper_tactics;
open operationsTheory l1Theory read_propertiesTheory write_propertiesTheory;

val _ = new_theory "invariant_l1";

Definition INVARIANT_L1:
  INVARIANT_L1 device_characteristics memory device = (
  DEVICE_REQUESTING_READ_ADDRESSES device_characteristics memory device /\
  DEVICE_REQUESTING_WRITE_ADDRESSES device_characteristics memory device
)
End

val _ = export_theory();

