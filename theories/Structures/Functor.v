Require Import ExtLib.Core.Any.

Set Implicit Arguments.
Set Strict Implicit.

Class Functor (t : Type -> Type) : Type :=
{ fmap : forall A B, (A -> B) -> t A -> t B
}.

Class PFunctor (t : Type -> Type) : Type :=
{ FunP : Type -> Type
; pfmap : forall {A B} {P : FunP B}, (A -> B) -> t A -> t B
}.

Existing Class FunP.
Hint Extern 0 (@FunP _ _ _) => progress (simpl FunP) : typeclass_instances.


Global Instance PFunctor_From_Functor t (F : Functor t) : PFunctor t :=
{ FunP := Any
; pfmap := fun _ _ _ f x => fmap f x
}.

Module FunctorNotation.
  Notation "f <$> x" := (@pfmap _ _ _ _ _ f x) (at level 51, right associativity).
End FunctorNotation.


