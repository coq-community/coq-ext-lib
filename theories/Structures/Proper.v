Require Import Coq.Relations.Relations.
Require Import RelationClasses.

Set Implicit Arguments.
Set Strict Implicit.

Class Proper (T : Type) : Type :=
  proper : T -> Prop.

Existing Class proper.

Section relations.
  Context {T : Type} {P : Proper T} (R : relation T).

  Class PReflexive : Prop :=
    preflexive : forall x : T, proper x -> R x x.

  Global Instance PReflexive_Reflexive (r : Reflexive R) : PReflexive.
  Proof. red; intros; reflexivity. Qed.
  
  Class PSymmetric : Prop :=
    psymmetric : forall x y, proper x -> proper y -> R x y -> R y x.

  Global Instance PSymmetric_Symmetric (r : Symmetric R) : PSymmetric.
  Proof. red; intros; symmetry; auto. Qed.

  Class PTransitive : Prop :=
    ptransitive : forall x y z, proper x -> proper y -> proper z ->
      R x y -> R y z -> R x z.

  Global Instance PTransitive_Transitive (r : Transitive R) : PTransitive.
  Proof. intro; intros; etransitivity; eauto. Qed.

End relations.

Arguments PReflexive {T} {P} R.
Arguments PSymmetric {T} {P} R.
Arguments PTransitive {T} {P} R.
