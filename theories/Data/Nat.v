Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Tactics.Consider.

Set Implicit Arguments.
Set Strict Implicit.


Global Instance RelDec_eq : RelDec (@eq nat) :=
{ rel_dec := EqNat.beq_nat }.

Global Instance type_nat : type nat :=
{ equal := @eq nat
; proper := fun _ => True
}.

Global Instance typeOk_nat : typeOk type_nat.
Proof.
  constructor.
  { compute; auto. }
  { compute; auto. }
  { compute; auto. }
  { compute. intros. etransitivity; eauto. }
Qed.

Global Instance nat_proper (n : nat) : proper n.
Proof. exact I. Qed.

Global Instance RelDec_lt : RelDec lt :=
{ rel_dec := NPeano.ltb }.

Global Instance RelDec_le : RelDec le :=
{ rel_dec := NPeano.leb }.

Global Instance RelDecCorrect_eq : RelDec_Correct RelDec_eq.
Proof.
  constructor; simpl. intros. consider (EqNat.beq_nat x y); intros; intuition.
  congruence.
Qed.

Global Instance RelDecCorrect_lt : RelDec_Correct RelDec_lt.
Proof.
  constructor; simpl. intros. consider (NPeano.ltb x y); intros; intuition.
  congruence.
Qed.

Global Instance RelDecCorrect_le : RelDec_Correct RelDec_le.
Proof.
  constructor; simpl. intros. consider (NPeano.leb x y); intros; intuition.
  congruence.
Qed.

Set Implicit Arguments.
Set Strict Implicit.

Inductive R_nat_S : nat -> nat -> Prop :=
| R_S : forall n, R_nat_S n (S n).

Theorem wf_R_S : well_founded R_nat_S.
Proof.
  red; induction a; constructor; intros.
    inversion H.
    inversion H; subst; auto.
Defined.

Inductive R_nat_lt : nat -> nat -> Prop :=
| R_lt : forall n m, n < m -> R_nat_lt n m.

Theorem wf_R_lt : well_founded R_nat_lt.
Proof.
  red; induction a; constructor; intros.
  { inversion H. exfalso. subst. inversion H0. }
  { inversion H; clear H; subst. inversion H0; clear H0; subst; auto.
    inversion IHa. eapply H. constructor. eapply H1. }
Defined.
