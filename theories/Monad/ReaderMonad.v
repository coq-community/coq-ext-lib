Require Import Monad.

Set Implicit Arguments.
Set Strict Implicit.

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

  Global Instance Reader_reader : Reader S reader :=
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

  Global Instance Reader_readerT : Reader S readerT :=
  { ask := mkReaderT (fun x => ret x)
  ; local := fun f _ cmd => mkReaderT (fun x => runReaderT cmd (f x))
  }.

  Global Instance MonadT_readerT : MonadT readerT m :=
  { lift := fun _ c => mkReaderT (fun _ => c)
  }.
  
  Global Instance Zero_readerT (MZ : Zero m) : Zero readerT :=
  { zero := fun _ => lift zero }.

  Global Instance Exception_readerT {E} (ME : MonadExc E m) : MonadExc E readerT :=
  { raise := fun v _ => lift (raise v)
  ; catch := fun _ c h => mkReaderT (fun s => catch (runReaderT c s) (fun x => runReaderT (h x) s))
  }.

End ReaderType.

Implicit Arguments mkReaderT [S m t].
