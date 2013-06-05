Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Tactics.Consider.

Set Implicit Arguments.
Set Strict Implicit.

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
