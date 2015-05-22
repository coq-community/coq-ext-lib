Require Import ExtLib.Core.Any.

Set Implicit Arguments.
Set Strict Implicit.

Polymorphic Class Functor (F : Type@{d} -> Type) : Type :=
{ fmap : forall {A B : Type@{d}}, (A -> B) -> F A -> F B }.

Polymorphic Definition ID {T : Type@{d}} (f : T -> T) : Prop :=
  forall x, f x = x.

Polymorphic Class PFunctor (F : Type@{d} -> Type) : Type :=
{ FunP : Type@{d} -> Type
; pfmap : forall {A B : Type@{d}} {P : FunP B}, (A -> B) -> F A -> F B
}.

Existing Class FunP.
Hint Extern 0 (@FunP _ _ _) => progress (simpl FunP) : typeclass_instances.

Global Polymorphic Instance PFunctor_From_Functor
       (F : Type@{d} -> Type) (FunF : Functor F) : PFunctor F :=
{ FunP := Any
; pfmap := fun _ _ _ f x => fmap f x
}.

Module FunctorNotation.
  Notation "f <$> x" := (@pfmap _ _ _ _ _ f x) (at level 51, right associativity).
End FunctorNotation.
