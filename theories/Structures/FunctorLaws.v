Require Import Coq.Relations.Relations.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Structures.Functor.

Set Implicit Arguments.
Set Strict Implicit.
Set Universe Polymorphism.

Section laws.

  Class FunctorLaws@{t u X}
              (F : Type@{t} -> Type@{u})
              (Functor_F : Functor F)
  : Type :=
  { fmap_id : forall T (x : F T), fmap id x = x
  ; fmap_compose : forall (T U V : Type@{t})
                     (x : F T),
      forall (f : T -> U) (g : U -> V),
        fmap (compose g f) x = fmap g (fmap f x)
  }.
End laws.
