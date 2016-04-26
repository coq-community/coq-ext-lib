Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.PPair.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Universe Polymorphism.

Set Printing Universes.

Section WriterType.
  Polymorphic Universe s d c.
  Variable S : Type@{s}.

  Record writerT (Monoid_S : Monoid@{s} S) (m : Type@{d} -> Type@{c}) (t : Type@{d}) : Type := mkWriterT
  { runWriterT : m (pprod t S)%type }.

  Variable Monoid_S : Monoid S.
  Variable m : Type@{d} -> Type@{c}.
  Context {M : Monad m}.

  Definition execWriterT {T} (c : writerT Monoid_S m T) : m S :=
    bind (runWriterT c) (fun (x : pprod T S) => ret (psnd x)).

  Definition evalWriterT {T} (c : writerT Monoid_S m T) : m T :=
    bind (runWriterT c) (fun (x : pprod T S) => ret (pfst x)).

  Local Notation "( x , y )" := (ppair x y).

  Global Instance Monad_writerT : Monad (writerT Monoid_S m) :=
  { ret := fun _ x => mkWriterT _ _ _ (@ret _ M _ (x, monoid_unit Monoid_S))
  ; bind := fun _ _ c1 c2 =>
    mkWriterT _ _ _ (
      @bind _ M _ _ (runWriterT c1) (fun v =>
        bind (runWriterT (c2 (pfst v))) (fun v' =>
        ret (pfst v', monoid_plus Monoid_S (psnd v) (psnd v')))))
  }.

  Global Instance Writer_writerT : MonadWriter Monoid_S (writerT Monoid_S m) :=
  { tell   := fun x => mkWriterT _ _ _ (ret (tt, x))
  ; listen := fun _ c => mkWriterT _ _ _ (bind (runWriterT c)
                                               (fun x => ret (pair (pfst x) (psnd x), psnd x)))
  ; pass   := fun _ c => mkWriterT _ _ _ (bind (runWriterT c)
                                               (fun x => ret (let '(ppair (pair x ss) s) := x in (x, ss s))))
  }.

  Global Instance MonadT_writerT : MonadT (writerT Monoid_S m) m :=
  { lift := fun _ c => mkWriterT _ _ _ (bind c (fun x => ret (x, monoid_unit Monoid_S)))
  }.

  Global Instance Reader_writerT {S'} (MR : MonadReader S' m) : MonadReader S' (writerT Monoid_S m) :=
  { ask := mkWriterT _ _ _ (bind ask (fun v => @ret _ M _ (v, monoid_unit Monoid_S)))
  ; local := fun _ f c =>
    mkWriterT _ _ _ (local f (runWriterT c))
  }.

  Global Instance State_writerT {S'} (MR : MonadState S' m) : MonadState S' (writerT Monoid_S m) :=
  { get := lift get
  ; put := fun v => lift (put v)
  }.

  Global Instance Zero_writerT (MZ : MonadZero m) : MonadZero (writerT Monoid_S m) :=
  { mzero := fun _ => lift mzero }.

  Global Instance Exception_writerT {E} (ME : MonadExc E m) : MonadExc E (writerT Monoid_S m) :=
  { raise := fun _ v => lift (raise v)
  ; catch := fun _ c h => mkWriterT _ _ _ (catch (runWriterT c) (fun x => runWriterT (h x)))
  }.

  Global Instance Writer_writerT_pass {T} {MonT : Monoid T} {M : Monad m} {MW : MonadWriter MonT m}
  : MonadWriter MonT (writerT Monoid_S m) :=
  { tell   := fun x => mkWriterT _ m _ (bind (tell x)
                                             (fun x => ret (x, monoid_unit Monoid_S)))
  ; listen := fun _ c => mkWriterT _ m _ (bind (m:=m) (@listen _ _ _ MW  _ (runWriterT c))
                                               (fun x => let '(pair (ppair a t) s) := x in
                                                         ret (m:=m) (pair a s,t)))
  ; pass   := fun _ c => mkWriterT _ m _ (@pass _ _ _ MW _
                                            (bind (m:=m) (runWriterT c)
                                                  (fun x => let '(ppair (pair a t) s) := x in
                                                            ret (m:=m) (pair (ppair a s) t))))
  }.

End WriterType.

Arguments mkWriterT {_} _ {_ _} _.
Arguments runWriterT {S} {Monoid_S} {m} {t} _.
Arguments evalWriterT {S} {Monoid_S} {m} {M} {T} _.
Arguments execWriterT {S} {Monoid_S} {m} {M} {T} _.
