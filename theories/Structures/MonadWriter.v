Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Monoid.

Set Implicit Arguments.
Set Maximal Implicit Arguments.

Polymorphic Class MonadWriter@{d c s} (T : Type@{s}) (M : Monoid T)
            (m : Type@{d} -> Type@{c}) : Type :=
{ tell : T -> m unit
; listen : forall {A : Type@{d}}, m A -> m (A * T)%type
; pass : forall {A : Type@{d}}, m (A * (T -> T))%type -> m A
}.

Polymorphic Definition listens@{d c s}
            {m : Type@{d} -> Type@{c}}
            {S : Type@{s}}
            {Monad_m : Monad m}
            {Monoid_S : Monoid S}
            {Writer_m : MonadWriter Monoid_S m}
            {A B : Type@{d}} (f : S -> B) (c : m A) : m (A * B)%type :=
  liftM (fun x => (fst x, f (snd x))) (listen c).

Polymorphic Definition censor@{d c s}
            {m : Type@{d} -> Type@{c}}
            {S : Type@{s}}
            {Monad_m : Monad m}
            {Monoid_S : Monoid S}
            {Writer_m : MonadWriter Monoid_S m}
            {A : Type@{d}} (f : S -> S) (c : m A) : m A :=
  pass (liftM (fun x => (x, f)) c).
