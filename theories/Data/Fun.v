Require Import Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Data.PreFun.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Structures.Functor.

Set Implicit Arguments.
Set Strict Implicit.

Section functors.
  Variable A : Type.

  Instance Functor_Fun : Functor (Fun A) :=
  { fmap _A _B g f x := g (f x) }.

End functors.

Export PreFun.