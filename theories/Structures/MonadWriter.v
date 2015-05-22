Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Monoid.

Set Implicit Arguments.
Set Maximal Implicit Arguments.

Polymorphic Class MonadWriter (T : Type@{s}) (M : Monoid T)
            (m : Type@{d} -> Type) : Type :=
{ tell : T -> m unit
; listen : forall {A : Type@{d}}, m A -> m (A * T)%type
; pass : forall {A : Type@{d}}, m (A * (T -> T))%type -> m A
}.

Section WriterOps.
  Polymorphic Context {m : Type -> Type}.
  Polymorphic Context {S : Type}.
  Context {Monad_m : Monad m}.
  Variable Monoid_S : Monoid S.
  Context {Writer_m : MonadWriter Monoid_S m}.

  Polymorphic Definition listens {A B : Type} (f : S -> B) (c : m A) : m (A * B) :=
    liftM (fun x => (fst x, f (snd x))) (listen c).

  Polymorphic Definition censor {A : Type} (f : S -> S) (c : m A) : m A :=
    pass (liftM (fun x => (x, f)) c).
End WriterOps.
