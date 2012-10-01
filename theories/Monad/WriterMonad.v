Require Import Monad.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Section WriterType.
  Variable S : Type.

(*
  Record reader (t : Type) : Type := mkReader
  { runReader : S -> t }.

  Global Instance Monad_reader : Monad reader :=
  { ret  := fun _ v => mkReader (fun _ => v)
  ; bind := fun _ c1 _ c2 =>
    mkReader (fun s =>
      let v := runReader c1 s in
      runReader (c2 v) s)
  }.

  Global Instance Reader_reader : Reader S reader :=
  { ask := mkReader (fun x => x)
  ; local := fun f _ cmd => mkReader (fun x => runReader cmd (f x))
  }.
*)

  Record Monoid (S : Type) : Type :=
  { monoid_plus : S -> S -> S
  ; monoid_unit : S
  }.

  Variable m : Type -> Type.
  Variable Monoid_S : Monoid S.

  Record writerT (t : Type) : Type := mkWriterT
  { runWriterT : m (t * S) }.

  Variable M : Monad m.

  Global Instance Monad_writerT : Monad writerT :=
  { ret := fun _ x => mkWriterT (@ret _ M _ (x, monoid_unit Monoid_S))
  ; bind := fun _ c1 _ c2 =>
    mkWriterT (
      @bind _ M _ (runWriterT c1) _ (fun v =>
        bind (runWriterT (c2 (fst v))) (fun v' =>
        ret (fst v', monoid_plus Monoid_S (snd v) (snd v')))))
  }.

  Global Instance Writer_writerT : Writer S writerT :=
  { tell   := fun x => mkWriterT (ret (tt, x))
  ; listen := fun _ c => mkWriterT (bind (runWriterT c) (fun x => ret (fst x, snd x, snd x)))
  ; pass   := fun _ c => mkWriterT (bind (runWriterT c) (fun x => ret (let '(x,ss,s) := x in (x, ss s))))
  }.

  Global Instance MonadT_writerT : MonadT writerT m :=
  { lift := fun _ c => mkWriterT (bind c (fun x => ret (x, monoid_unit Monoid_S)))
  }.

  Global Instance Reader_writerT {S'} (MR : Reader S' m) : Reader S' writerT :=
  { ask := mkWriterT (bind ask (fun v => @ret _ M _ (v, monoid_unit Monoid_S)))
  ; local := fun f _ c =>
    mkWriterT (local f (runWriterT c))
  }.  

  Global Instance Zero_writerT (MZ : Zero m) : Zero writerT :=
  { zero := fun _ => lift zero }.

  Global Instance Exception_writerT {E} (ME : MonadExc E m) : MonadExc E writerT :=
  { raise := fun _ v => lift (raise v)
  ; catch := fun _ c h => mkWriterT (catch (runWriterT c) (fun x => runWriterT (h x)))
  }.

End WriterType.

Section WriterOps.
  Context {m : Type -> Type}.
  Context {S : Type}.
  Context {Monad_m : Monad m}.
  Context {Writer_m : Writer S m}.

  Definition listens {A B} (f : S -> B) (c : m A) : m (A * B) :=
    liftM (fun x => (fst x, f (snd x))) (listen c).

  Definition censor {A} (f : S -> S) (c : m A) : m A :=
    pass (liftM (fun x => (x, f)) c).
End WriterOps.

Arguments mkWriterT {S} {m} {t} _.
