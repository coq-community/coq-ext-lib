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

  Class FunctorLaws : Type :=
  { fmap_id : forall T (Teq : relation T) (Pt : Proper Teq) f,
    (forall x, Teq (f x) x) ->
    fun_ext (Feq Teq) (Feq Teq) (fmap f) id
  ; fmap_compose : forall T (Teq : relation T) (Pt : Proper Teq) 
                          U (Ueq : relation U) (Pu : Proper Ueq)
                          V (Veq : relation V) (Pv : Proper Veq)
                          (f : T -> U) (g : U -> V),
    fun_ext (Feq Teq) (Feq Veq) (fmap (compose f g)) (compose (fmap f) (fmap g))
  }.
End laws.