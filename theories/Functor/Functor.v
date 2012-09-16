Require Import Fun.

Set Implicit Arguments.
Set Strict Implicit.

Class Functor t :=
{ fmap : forall A B, (A -> B) -> t A -> t B
}.

Module FunctorNotation.
  Notation "f <$> x" := (fmap f x) (at level 51, right associativity).
End FunctorNotation.

Import FunctorNotation.

Definition Fun A B := A -> B.

Instance FunFunctor A : Functor (Fun A) :=
{ fmap _A _B g f := compose g f
}.
