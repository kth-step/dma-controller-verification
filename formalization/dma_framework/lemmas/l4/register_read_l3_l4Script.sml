open HolKernel Parse boolLib bossLib helper_tactics;
open l3Theory l4Theory;

val _ = new_theory "register_read_l3_l4";

Theorem IS_VALID_L3_EQ_IS_VALID_L4:
is_valid_l3 = is_valid_l4
Proof
REWRITE_TAC [boolTheory.FUN_EQ_THM, is_valid_l3, is_valid_l4]
QED

Theorem DEVICE_REGISTER_READ_L3_EQ_L4_LEMMA:
!device_characteristics memory device addresses.
  (device_register_read_l3 device_characteristics device addresses =
   device_register_read_l4 device_characteristics device addresses)
Proof
REPEAT GEN_TAC THEN
PTAC device_register_read_l3 THEN PTAC device_register_read_l4 THEN
REWRITE_TAC [IS_VALID_L3_EQ_IS_VALID_L4]
QED

val _ = export_theory();

