Require Import Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Structures.Functor.

Set Implicit Arguments.
Set Strict Implicit.

Definition Fun A B := A -> B.

Instance Functor_Fun A : Functor (Fun A) :=
{ fmap _A _B g f x := g (f x)
}.

Definition compose (A B C : Type) (f : A -> B) (g : B -> C) : A -> C :=
  fun x => g (f x).

Section equiv.
  Context {A B : Type} (rA : relation A) (rB : relation B).

  Definition fun_ext (f g : A -> B) :=
    forall a b, rA a b -> rB (f a) (g b).

  Definition pfun_ext (Pa : Proper rA) (Pb : Proper rB) (f g : A -> B) :=
    forall a b, proper a -> proper b -> rA a b -> rB (f a) (g b) /\ proper (f a) /\ proper (g b).

End equiv.

Section proper.
  Context {A B : Type} (rA : relation A) (rB : relation B).

  Global Instance Proper_fun (pA : Proper rA) (pB : Proper rB) : Proper (fun_ext rA rB)%signature :=
  { proper := fun f => 
       (forall x, proper x -> proper (f x))
    /\ (pfun_ext pA pB f f)
  }.

  Global Instance Proper_pfun (pA : Proper rA) (pB : Proper rB) : Proper (pfun_ext pA pB)%signature :=
  { proper := fun f => 
       (forall x, proper x -> proper (f x))
    /\ (pfun_ext pA pB f f)
  }.

  Global Instance PReflexive_pfun_ext (pA : Proper rA) (pB : Proper rB) : PReflexive rA -> PReflexive rB -> PReflexive (pfun_ext pA pB).
  Proof.
    repeat red; intros. eapply H1; eauto.
  Qed.

  Global Instance PTransitive_pfun_ext (pA : Proper rA) (pB : Proper rB) : 
    PReflexive rA -> PTransitive rA -> PTransitive rB -> PTransitive (pfun_ext pA pB).
  Proof.
    repeat red; intros.
    generalize (H5 _ _ H7 H8 H9).
    generalize (H6 _ _ H7 H8 H9). intuition. 
    eapply ptransitive; [ | | | | eassumption | ]; eauto. 
    

5: eapply H5; eauto. eauto. eapply H2; eauto. eapply H3; eauto. eapply H4; eauto.
    eapply H6; eauto.
  Qed.

  Global Instance proper_app (pA : Proper rA) (pB : Proper rB) : forall (f : A -> B) (a : A),
    proper f -> proper a -> proper (f a).
  Proof. compute; intuition. Qed.

  Existing Instance proper_app.

End proper.

Arguments Proper_fun {_} {_} {_} {_} _ _ _.
Arguments Proper_pfun {_} {_} {_} {_} _ _ _.