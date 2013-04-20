Require Import ExtLib.Core.Type.

Global Instance type_unit : type unit :=
{ equal := fun _ _ => True }.

Global Instance typeOk_N : typeOk type_unit.
Proof.
  constructor; compute; auto.
Qed.