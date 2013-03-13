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

  Definition pfun_ext (Pa : Proper rA) (f g : A -> B) :=
    forall a b, proper a -> proper b -> rA a b -> rB (f a) (g b).

End equiv.

Section proper.
  Context {A B : Type} (rA : relation A) (rB : relation B).
  Context {Pa : Proper rA} {Pb : Proper rB}.

  Global Instance Proper_fun : Proper (fun_ext rA rB)%signature :=
  { proper := fun f => 
       (forall x, proper x -> proper (f x))
    /\ (pfun_ext rB Pa f f)
  }.

  Global Instance  proper_app : forall (f : A -> B) (a : A),
    proper f -> proper a -> proper (f a).
  Proof. compute; intuition. Qed.

  Existing Instance proper_app.

End proper.

Arguments Proper_fun {_} {_} {_} {_} _ _ _.