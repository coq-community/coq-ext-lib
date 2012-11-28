Require Import ExtLib.Structures.Functor.

Set Implicit Arguments.
Set Strict Implicit.

Definition Fun A B := A -> B.

Instance FunFunctor A : Functor (Fun A) :=
{ fmap _A _B g f x := g (f x)
}.
