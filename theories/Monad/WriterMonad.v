Require Import Monad.
Require Import ExtLib.Data.Monoid.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Section WriterType.
  Variable S : Type.

  Record writerT (Monoid_S : Monoid S) (m : Type -> Type) (t : Type) : Type := mkWriterT
  { runWriterT : m (t * S)%type }.

  Variable Monoid_S : Monoid S.
  Variable m : Type -> Type.
  Variable M : Monad m.

  Global Instance Monad_writerT : Monad (writerT Monoid_S m) :=
  { ret := fun _ x => mkWriterT _ _ _ (@ret _ M _ (x, monoid_unit Monoid_S))
  ; bind := fun _ c1 _ c2 =>
    mkWriterT _ _ _ (
      @bind _ M _ (runWriterT c1) _ (fun v =>
        bind (runWriterT (c2 (fst v))) (fun v' =>
        ret (fst v', monoid_plus Monoid_S (snd v) (snd v')))))
  }.

  Global Instance Writer_writerT : Writer Monoid_S (writerT Monoid_S m) :=
  { tell   := fun x => mkWriterT _ _ _ (ret (tt, x))
  ; listen := fun _ c => mkWriterT _ _ _ (bind (runWriterT c) (fun x => ret (fst x, snd x, snd x)))
  ; pass   := fun _ c => mkWriterT _ _ _ (bind (runWriterT c) (fun x => ret (let '(x,ss,s) := x in (x, ss s))))
  }.

  Global Instance MonadT_writerT : MonadT (writerT Monoid_S m) m :=
  { lift := fun _ c => mkWriterT _ _ _ (bind c (fun x => ret (x, monoid_unit Monoid_S)))
  }.

  Global Instance Reader_writerT {S'} (MR : Reader S' m) : Reader S' (writerT Monoid_S m) :=
  { ask := mkWriterT _ _ _ (bind ask (fun v => @ret _ M _ (v, monoid_unit Monoid_S)))
  ; local := fun f _ c =>
    mkWriterT _ _ _ (local f (runWriterT c))
  }.  

  Global Instance State_writerT {S'} (MR : State S' m) : State S' (writerT Monoid_S m) :=
  { get := lift get
  ; put := fun v => lift (put v)
  }.  

  Global Instance Zero_writerT (MZ : Zero m) : Zero (writerT Monoid_S m) :=
  { zero := fun _ => lift zero }.

  Global Instance Exception_writerT {E} (ME : MonadExc E m) : MonadExc E (writerT Monoid_S m) :=
  { raise := fun _ v => lift (raise v)
  ; catch := fun _ c h => mkWriterT _ _ _ (catch (runWriterT c) (fun x => runWriterT (h x)))
  }.

End WriterType.

Section WriterOps.
  Context {m : Type -> Type}.
  Context {S : Type}.
  Context {Monad_m : Monad m}.
  Variable Monoid_S : Monoid S.
  Context {Writer_m : Writer Monoid_S m}.

  Definition listens {A B} (f : S -> B) (c : m A) : m (A * B) :=
    liftM (fun x => (fst x, f (snd x))) (listen c).

  Definition censor {A} (f : S -> S) (c : m A) : m A :=
    pass (liftM (fun x => (x, f)) c).
End WriterOps.

Arguments runWriterT {S} {Monoid_S} {m} {t} _.
