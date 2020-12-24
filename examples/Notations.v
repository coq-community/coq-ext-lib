Require Import ExtLib.Structures.Monad.
Generalizable All Variables.

Module NotationExample.

  Import MonadNotation.
  Open Scope monad_scope.

  Fixpoint repeatM `{Monad M} (n : nat) `(x : A) (p : A -> M A) : M unit :=
    match n with
    | O => ret tt
    | S n => y <- p x;;
             repeatM n y p
    end.

End NotationExample.

Module LetNotationExample.

  Import MonadLetNotation.
  Open Scope monad_scope.

  Fixpoint repeatM `{Monad M} (n : nat) `(x : A) (p : A -> M A) : M unit :=
    match n with
    | O => ret tt
    | S n => let* y := p x in
             repeatM n y p
    end.

End LetNotationExample.
