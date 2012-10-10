Require Import Monad.

Set Implicit Arguments.
Set Maximal Implicit Arguments.

Class MonadReader (T : Type) (m : Type -> Type) : Type :=
{ local : (T -> T) -> forall {t}, m t -> m t
; ask : m T
}.

Section monadic.
  Variable m : Type -> Type.
  Context {M : Monad m}.
  Variable T : Type.
  Context {MR : MonadReader T m}.

  Definition asks {U} (f : T -> U) : m U :=
    bind ask (fun x => ret (f x)).

End monadic.