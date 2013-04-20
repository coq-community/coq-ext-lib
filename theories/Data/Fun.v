Require Import Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Structures.Functor.

Set Implicit Arguments.
Set Strict Implicit.

Definition Fun A B := A -> B.

Section type.
  Variables (T U : Type) (tT : type T) (tU : type U).

  Global Instance type_Fun  : type (T -> U) :=
  { equal := fun f g => respectful equal equal f g }.

  Variables (tOk : typeOk tT) (uOk : typeOk tU).

  Global Instance typeOk_Fun : typeOk type_Fun.
  Proof.
    constructor.
    { unfold equiv. simpl. unfold respectful.
      destruct tOk. destruct uOk; intros.
      split; red; simpl; red; intros.
      { destruct (only_proper _ _ H0).
        etransitivity. eapply H. eassumption.
        symmetry. eapply H. symmetry. auto. }
      { destruct (only_proper _ _ H0).
        symmetry. etransitivity; [ | eapply H ]. 
        symmetry. eapply H. eassumption. symmetry. eauto. } }
    { red. intros. apply H. }
    { compute. intuition. symmetry. eapply H. symmetry. auto. }
    { compute. intuition. 
      etransitivity. eapply H. eassumption.
      eapply H0. eapply preflexive; auto.
      eapply only_proper in H1; intuition. }
  Qed.

  Global Instance  proper_app : forall (f : T -> U) (a : T),
    proper f -> proper a -> proper (f a).
  Proof.
    compute; intuition. 
    eapply H. eauto.
  Qed.

  Theorem proper_fun : forall (f : T -> U),
    (forall x y, equal x y -> equal (f x) (f y)) ->
    proper f.
  Proof. intros. do 5 red. apply H. Qed.

  Theorem equal_fun : forall (f g : T -> U),
    (forall x y, equal x y -> equal (f x) (g y)) ->
    equal f g.
  Proof. intros. do 3 red. apply H. Qed.

  Theorem equal_app : forall (f g : T -> U) (x y : T),
    equal f g -> equal x y ->
    equal (f x) (g y).
  Proof.
    clear. intros. do 3 red in H. auto.
  Qed.

End type.

Instance Functor_Fun A : Functor (Fun A) :=
{ fmap _A _B g f x := g (f x)
}.

Definition compose (A B C : Type) (f : A -> B) (g : B -> C) : A -> C :=
  fun x => g (f x).
