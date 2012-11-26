Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monoid.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Section ReaderType.
  Variable S : Type.

  Record reader (t : Type) : Type := mkReader
  { runReader : S -> t }.

  Global Instance Monad_reader : Monad reader :=
  { ret  := fun _ v => mkReader (fun _ => v)
  ; bind := fun _ c1 _ c2 =>
    mkReader (fun s =>
      let v := runReader c1 s in
      runReader (c2 v) s)
  }.

  Global Instance MonadReader_reader : MonadReader S reader :=
  { ask := mkReader (fun x => x)
  ; local := fun f _ cmd => mkReader (fun x => runReader cmd (f x))
  }.

  Variable m : Type -> Type.

  Record readerT (t : Type) : Type := mkReaderT
  { runReaderT : S -> m t }.

  Variable M : Monad m.

  Global Instance Monad_readerT : Monad readerT :=
  { ret := fun _ x => mkReaderT (fun s => @ret _ M _ x)
  ; bind := fun _ c1 _ c2 =>
    mkReaderT (fun s =>
      @bind _ M _ (runReaderT c1 s) _ (fun v =>
        runReaderT (c2 v) s))
  }.

  Global Instance MonadReader_readerT : MonadReader S readerT :=
  { ask := mkReaderT (fun x => ret x)
  ; local := fun f _ cmd => mkReaderT (fun x => runReaderT cmd (f x))
  }.

  Global Instance MonadT_readerT : MonadT readerT m :=
  { lift := fun _ c => mkReaderT (fun _ => c)
  }.

  Global Instance MonadZero_readerT (MZ : MonadZero m) : MonadZero readerT :=
  { mzero := fun _ => lift mzero }.

  Global Instance MonadState_readerT T (MS : MonadState T m) : MonadState T readerT :=
  { get := lift get
  ; put := fun x => lift (put x)
  }.

  Global Instance MonadWriter_readerT T (Mon : Monoid T) (MW : MonadWriter Mon m) : MonadWriter Mon readerT :=
  { tell := fun v => lift (tell v)
  ; listen := fun _ c => mkReaderT (fun s => listen (runReaderT c s))
  ; pass := fun _ c => mkReaderT (fun s => pass (runReaderT c s))
  }.

  Global Instance MonadExc_readerT {E} (ME : MonadExc E m) : MonadExc E readerT :=
  { raise := fun _ v => lift (raise v)
  ; catch := fun _ c h => mkReaderT (fun s => catch (runReaderT c s) (fun x => runReaderT (h x) s))
  }.

  Global Instance MonadPlus_readerT {mMonadPlus:MonadPlus m} : MonadPlus readerT :=
  { mplus _A _B mA mB := mkReaderT (fun r => mplus (runReaderT mA r)
                                                   (runReaderT mB r))
  }.

End ReaderType.

Arguments mkReaderT {S} {m} {t} _.
Arguments MonadWriter_readerT {S} {m} {T} {Mon} (_).


Global Instance MoandReader_lift_readerT T S m (R : MonadReader T m) : MonadReader T (readerT S m) :=
{ ask := mkReaderT (fun _ => ask)
; local := fun f _ c =>
  mkReaderT (fun s => local f (runReaderT c s))
}.
