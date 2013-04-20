Require Import Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Structures.Functor.

Set Implicit Arguments.
Set Strict Implicit.

Section laws.
  Variable F : Type -> Type.
  Variable Functor_F : Functor F.

  Variable Feq : forall T, relation T -> relation (F T).
  Variable Proper_F : forall T, Proper T -> Proper (F T).

  Class FunctorLaws : Type :=
  { fmap_id : forall T (Pt : Proper T) (Teq : relation T) (f : T -> T),
    (forall x, Teq (f x) x) ->
    respectful (Feq Teq) (Feq Teq) (fmap f) (@id (F T))
  ; fmap_compose : forall T (Teq : relation T) (Pt : Proper T) 
                          U (Ueq : relation U) (Pu : Proper U)
                          V (Veq : relation V) (Pv : Proper V)
                          (f : T -> U) (g : U -> V),
    respectful Teq Ueq f f -> respectful Ueq Veq g g ->
    respectful (Feq Teq) (Feq Veq) (fmap (compose f g)) (compose (fmap f) (fmap g))
  }.
End laws.