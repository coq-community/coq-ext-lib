Require Import RelationClasses.
Require Import Setoid.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.FunctorRelations.
Require Import ExtLib.Structures.MonadLaws.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Data.Monads.IdentityMonad.

Set Implicit Arguments.
Set Strict Implicit.

Section with_T.
  Context {T : Type} (e : relation T) (P : Proper e).

  Definition Identity_leq (a b : ident T) : Prop :=
    e (unIdent a) (unIdent b).
  
  Global Instance Proper_Identity : Proper Identity_leq :=
    { proper := fun f => proper (unIdent f) }.

  Global Instance PReflexive_Identity_leq (PT : PReflexive e): PReflexive Identity_leq.
  Proof.
    red; destruct x; compute; simpl in *; intros; try contradiction; eauto.
  Qed.

  Global Instance PTransitive_Identity_leq (PT : PTransitive e): PTransitive Identity_leq.
  Proof.
    red; destruct x; destruct y; destruct z; compute; simpl in *; intros; try contradiction; eauto.
  Qed.

  Global Instance proper_unIdent : forall x,
    proper x ->
    proper (unIdent x).
  Proof.
    destruct x; compute; auto.
  Qed.

End with_T.

Global Instance FunctorOrder_fmleq : FunctorOrder _ (@Identity_leq) _.
Proof.
  constructor; eauto with typeclass_instances.
Qed.

Global Instance MonadLaws_GFix : MonadLaws Monad_ident (@Identity_leq) _.
Proof.
  constructor; eauto with typeclass_instances; try solve [ compute; intuition ].
Qed.
