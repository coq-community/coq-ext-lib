Require Import ExtLib.Core.Type.
Require Import ExtLib.Structures.Proper.

Global Instance type_unit : type unit :=
{ equal := fun _ _ => True 
; proper := fun _ => True
}.

Global Instance typeOk_N : typeOk type_unit.
Proof.
  constructor; compute; auto.
Qed.

Global Instance proper_tt (x : unit) : proper x.
Proof.
  exact I.
Qed.