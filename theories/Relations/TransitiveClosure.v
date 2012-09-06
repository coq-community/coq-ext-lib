Require Import RelationClasses.

Set Implicit Arguments.
Set Strict Implicit.


Section parametric.
  Variable T : Type.
  Variable R : T -> T -> Prop.

  (** Reflexivity **)
  Inductive makeRefl : T -> T -> Prop :=
  | RRefl : forall x, makeRefl x x
  | RStep : forall x y, R x y -> makeRefl x y.

  Global Instance Refl_makeRefl : Reflexive makeRefl.
  Proof.
    constructor.
  Qed.

  (** Transitivity **)
  Inductive makeTrans : T -> T -> Prop :=
  | TStep : forall x y, R x y -> makeTrans x y
  | TTrans : forall x y z, makeTrans x y -> makeTrans y z -> makeTrans x z.

  Global Instance Trans_makeTrans : Transitive makeTrans.
  Proof.
    intro. intros; eapply TTrans; eassumption.
  Qed.

  Inductive leftTrans : T -> T -> Prop :=
  | LTFin : forall x y, R x y -> leftTrans x y
  | LTStep : forall x y z, R x y -> leftTrans y z -> leftTrans x z.

  Inductive rightTrans : T -> T -> Prop :=
  | RTFin : forall x y, R x y -> rightTrans x y
  | RTStep : forall x y z, rightTrans x y -> R y z -> rightTrans x z.

  (** Equivalence of definitions of transitivity **)
  Fixpoint leftTrans_rightTrans_acc x y (l : leftTrans y x) : forall z, rightTrans z y -> rightTrans z x :=
    match l in leftTrans y x return forall z, rightTrans z y -> rightTrans z x with
      | LTFin _ _ pf => fun z pfR => RTStep pfR pf
      | LTStep _ _ _ pf pfL => fun z pfR =>
        leftTrans_rightTrans_acc pfL (RTStep pfR pf)
    end.

  Definition leftTrans_rightTrans x y (l : leftTrans x y) : rightTrans x y :=
    match l with
      | LTFin _ _ pf => RTFin pf
      | LTStep _ _ _ pf pfR =>
        leftTrans_rightTrans_acc pfR (RTFin pf)
    end.

  Theorem makeTrans_leftTrans : forall s s',
    makeTrans s s' <-> leftTrans s s'.
  Proof. Admitted.

  Theorem makeTrans_rightTrans : forall s s',
    makeTrans s s' <-> rightTrans s s'.
  Proof. Admitted.

End parametric.

