Require Import ExtLib.Data.Fin.

Set Implicit Arguments.
Set Strict Implicit.

Section parametric.
  Variable T : Type.

  Inductive vector : nat -> Type :=
  | Vnil : vector 0
  | Vcons : forall {n}, T -> vector n -> vector (S n).

  Definition vector_hd n (v : vector (S n)) : T :=
    match v in vector n' return match n' with
                                  | 0 => unit
                                  | S _ => T
                                end with
      | Vnil => tt
      | Vcons _ x _ => x
    end.

  Definition vector_tl n (v : vector (S n)) : vector n :=
    match v in vector n' return match n' with
                                  | 0 => unit
                                  | S n => vector n
                                end with
      | Vnil => tt
      | Vcons _ _ x => x
    end.

End parametric.

Arguments Vnil {T}.
Arguments Vcons {T} {n} _ _.
Arguments vector_hd {_} {_} _.
Arguments vector_tl {_} {_} _.