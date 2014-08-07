Require Import ExtLib.Core.Type.

Global Instance type_Prop : type Prop :=
{ equal := iff
; proper := fun _ => True
}.

Global Instance typeOk_Prop : typeOk type_Prop.
Proof.
  constructor; compute; firstorder.
Qed.
