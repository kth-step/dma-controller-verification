open HolKernel Parse boolLib bossLib helper_tactics;
open l3Theory l4Theory;

val _ = new_theory "register_write_l3_l4";

Theorem IS_VALID_L3_EQ_IS_VALID_L4:
is_valid_l3 = is_valid_l4
Proof
REWRITE_TAC [boolTheory.FUN_EQ_THM, is_valid_l3, is_valid_l4]
QED

Theorem DEVICE_REGISTER_WRITE_L3_EQ_L4_LEMMA:
!device_characteristics memory device address_bytes.
  (device_register_write_l3 device_characteristics device address_bytes =
   device_register_write_l4 device_characteristics device address_bytes)
Proof
REPEAT GEN_TAC THEN
PTAC device_register_write_l3 THEN PTAC device_register_write_l4 THEN
REWRITE_TAC [IS_VALID_L3_EQ_IS_VALID_L4]
QED

val _ = export_theory();

