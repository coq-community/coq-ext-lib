From Coq.Relations Require Import Relations.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Structures.Functor.

Set Implicit Arguments.
Set Strict Implicit.
Set Universe Polymorphism.

Section laws.

  Class FunctorLaws {F} (Functor_F : Functor F) :=
  { fmap_id : forall {T} (x : F T), fmap id x = x
  ; fmap_compose : forall {T U V} (f : T -> U) (g : U -> V) (x : F T),
        fmap (compose g f) x = fmap g (fmap f x)
  }.
End laws.
