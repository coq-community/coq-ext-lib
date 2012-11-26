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

Section SubReader.
  Variable m : Type -> Type.
  Context {M : Monad m}.
  Variable T S : Type.
  Context {MR : MonadReader T m}.

  Definition ReaderProd (f : T -> S) (g : S -> T -> T) 
    : MonadReader S m :=
  {| ask := @asks m M T MR S f
   ; local := fun up _T (c : m _T)  => @local T m MR (fun s => g (up (f s)) s) _ c
   |}.
End SubReader.
