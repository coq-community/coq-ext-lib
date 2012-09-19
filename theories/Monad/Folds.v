Require Import Monad.
Require Import List.

Set Implicit Arguments.
Set Strict Implicit.

Import MonadNotation.
Open Local Scope monad.

Section mapM.
  Context {A B : Type}.
  Context {m : Type -> Type}.
  Context {M : Monad m}.
  Variable f : A -> m B.

  Fixpoint mapM (ls : list A) : m (list B) :=
    match ls with
      | nil => ret nil
      | l :: ls =>
        l <- f l ;;
        ls <- mapM ls ;;
        ret (l :: ls)
    end.
End mapM.

Section foldM.
  Context {A B : Type}.
  Context {m : Type -> Type}.
  Context {M : Monad m}.
  Variable f : A -> B -> m B.

  Fixpoint foldlM (acc : B) (ls : list A) : m B :=
    match ls with
      | nil => ret acc
      | l :: ls =>
        acc <- f l acc ;;
        foldlM acc ls
    end.

  Definition foldM := foldlM.

  Fixpoint foldrM (rr : B) (ls : list A) : m B :=
    match ls with
      | nil => ret rr
      | l :: ls =>
        rr <- foldrM rr ls ;;
        f l rr
    end.

End foldM.


