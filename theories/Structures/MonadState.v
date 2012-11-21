Require Import Monad.

Set Implicit Arguments.
Set Maximal Implicit Arguments.

Class MonadState (T : Type) (m : Type -> Type) : Type :=
{ get : m T
; put : T -> m unit
}.

Section monadic.
  Variable m : Type -> Type.
  Context {M : Monad m}.
  Variable T : Type.
  Context {MR : MonadState T m}.

  Definition modify (f : T -> T) : m T :=
    bind get (fun x => bind (put (f x)) (fun _ => ret x)).

  Definition gets {U} (f : T -> U) : m U :=
    bind get (fun x => ret (f x)).

End monadic.