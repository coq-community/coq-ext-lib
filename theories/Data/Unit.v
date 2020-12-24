Require Import ExtLib.Core.RelDec.

Set Implicit Arguments.
Set Strict Implicit.

Global Instance RelDec_eq_unit : RelDec (@eq unit) :=
{ rel_dec := fun _ _ => true }.
Global Instance RelDec_Correct_eq_unit : RelDec_Correct RelDec_eq_unit.
  constructor. destruct x; destruct y; auto; simpl. intuition.
Qed.
