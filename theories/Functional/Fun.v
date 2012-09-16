Require Import List.
Require Import Monad.

Set Implicit Arguments.
Set Strict Implicit.

Definition forEach A B (xs:list A) (f:A -> B) : list B := map f xs.

Definition forEachM m {M:Monad m} A B (xs:list A) (f:A -> m B) : m (list B) :=
  mapM _ f xs.

Module FunNotation.

  Notation "f $ x" := (f x)
    (at level 99, x at level 99, right associativity, only parsing).

  Notation "'begin' e1 'end'" := (e1)
    (at level 0, only parsing).

End FunNotation.
