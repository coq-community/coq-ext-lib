Require Import ExtLib.Structures.Monad.

Set Implicit Arguments.
Set Maximal Implicit Arguments.

Polymorphic Class MonadReader@{d c} (T : Type@{d}) (m : Type@{d} -> Type@{c})
: Type :=
{ local : forall {t : Type@{d}}, (T -> T) -> m t -> m t
; ask : m T
}.

Polymorphic Definition asks@{d c}
            {m : Type@{d} -> Type@{c}}
            {M : Monad m}
            {T : Type@{d}}
            {MR : MonadReader@{d c} T m}
            {U : Type@{d}} (f : T -> U) : m U :=
  bind ask (fun x => ret (f x)).

Polymorphic Definition ReaderProd
            {m : Type -> Type}
            {M : Monad m}
            {T S : Type}
            {MR : MonadReader T m}
            (f : T -> S)
            (g : S -> T -> T)
  : MonadReader S m :=
  {| ask := @asks m M T MR S f
   ; local := fun _T up (c : m _T)  =>
                  @local T m MR _ (fun s => g (up (f s)) s) c
  |}.
