Require Import ExtLib.Core.Any.

Set Implicit Arguments.
Set Strict Implicit.

Polymorphic Class Functor@{d c} (F : Type@{d} -> Type@{c}) : Type :=
{ fmap : forall {A B : Type@{d}}, (A -> B) -> F A -> F B }.

Polymorphic Definition ID@{d} {T : Type@{d}} (f : T -> T) : Prop :=
  forall x : T, f x = x.

Module FunctorNotation.
  Notation "f <$> x" := (@fmap _ _ _ _ f x) (at level 52, left associativity).
End FunctorNotation.
