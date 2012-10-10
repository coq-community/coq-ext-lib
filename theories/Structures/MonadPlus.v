Require Import Monad.

Set Implicit Arguments.
Set Maximal Implicit Arguments.

Class MonadPlus (m : Type -> Type) : Type :=
{ mplus : forall {A B:Type}, m A -> m B -> m (A + B)%type }.

Module MonadPlusNotation.
  Notation "x <+> y" := (mplus x y) (at level 49, right associativity).
End MonadPlusNotation.
