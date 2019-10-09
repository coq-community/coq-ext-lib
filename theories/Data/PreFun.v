Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Core.Type.

Set Implicit Arguments.
Set Strict Implicit.
Set Universe Polymorphism.

Definition Fun@{d c} (A : Type@{d}) (B : Type@{c}) := A -> B.

Section type.
  Universe uT uU.
  Variables (T : Type@{uT}) (U : Type@{uU}) (tT : type T) (tU : type U).

  Global Instance type_Fun@{uU'} : type@{uU'} (T -> U) :=
  { equal := fun f g => respectful equal equal f g
  ; proper := fun x => respectful equal equal x x
  }.

  Variables (tOk : typeOk tT) (uOk : typeOk tU).

  Global Instance typeOk_Fun@{uU'} : typeOk@{uU'} type_Fun.
  Proof.
    constructor.
    { unfold equiv. simpl. unfold respectful.
      destruct tOk. destruct uOk; intros.
      split; intros.
      { destruct (only_proper _ _ H0).
        etransitivity. eapply H. eassumption.
        symmetry. eapply H. symmetry. auto. }
      { destruct (only_proper _ _ H0).
        symmetry. etransitivity; [ | eapply H ].
        symmetry. eapply H. eassumption. symmetry. eauto. } }
    { red. intros. apply H. }
    { compute. intuition. symmetry. eapply H. symmetry. auto. }
    { simpl; intro; intros. intuition. red in H; red in H0; simpl in *.
      red; intros.
      etransitivity. eapply H. eassumption.
      eapply H0.
      eapply only_proper in H1; intuition.
      eapply preflexive with (wf := proper); auto.
      apply tOk. }
  Qed.

  Global Instance proper_app@{uU'} : forall (f : T -> U) (a : T),
    proper@{uU'} f -> proper a -> proper (f a).
  Proof.
    simpl; intros. red in H.
    eapply proper_left; eauto.
    eapply H. eapply preflexive. eapply equiv_prefl; auto. auto.
  Qed.

  Theorem proper_fun@{uU'} : forall (f : T -> U),
    (forall x y, equal x y -> equal (f x) (f y)) ->
    proper@{uU'} f.
  Proof.
    intros. do 3 red. eauto.
  Qed.

  Theorem equal_fun@{uU'} : forall (f g : T -> U),
    (forall x y, equal x y -> equal (f x) (g y)) ->
    equal@{uU'} f g.
  Proof. intros. do 3 red. apply H. Qed.

  Theorem equal_app@{uU'} : forall (f g : T -> U) (x y : T),
    equal@{uU'} f g -> equal x y ->
    equal (f x) (g y).
  Proof.
    clear. intros. do 3 red in H. auto.
  Qed.

End type.

Definition compose@{uA uB uC} {A:Type@{uA}} {B:Type@{uB}} {C : Type@{uC}}
    (g : B -> C) (f : A -> B) : A -> C :=
  fun x => g (f x).
