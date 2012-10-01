Require Import Monad.

Set Implicit Arguments.
Set Strict Implicit.

Import MonadNotation.
Open Local Scope monad_scope.

Global Instance Monad_option : Monad option :=
{ ret  := @Some
; bind := fun _ c1 _ c2 => match c1 with
                             | None => None
                             | Some v => c2 v
                           end
}.

Global Instance Zero_option : Zero option :=
{ zero := @None }.

Global Instance Plus_option : MonadPlus option :=
{ mplus _A _B aM bM :=
    match aM with
    | None => liftM inr bM
    | Some a => Some (inl a)
    end
}.

Section Trans.
  Variable m : Type -> Type.

  Inductive optionT a := mkOptionT { unOptionT : m (option a) }.

  Context {M : Monad m}.

  Global Instance Monad_optionT : Monad optionT :=
  { ret _A := fun x => mkOptionT (ret (Some x))
  ; bind _A aMM _B f := mkOptionT
      (aM <- unOptionT aMM ;;
       match aM with
       | None => ret None
       | Some a => unOptionT (f a)
       end)
  }.

  Global Instance Zero_optionT : Zero optionT :=
  { zero _A := mkOptionT (ret None) }.

  Global Instance MonadT_optionT : MonadT optionT m :=
  { lift _A aM := mkOptionT (liftM ret aM) }.

  Global Instance State_optionT {T} (SM : State T m) : State T optionT :=
  { get := lift get
  ; put v := lift (put v)
  }.

  Global Instance Reader_optionT {T} (SM : Reader T m) : Reader T optionT :=
  { ask := lift ask
  ; local v _T cmd := mkOptionT (local v (unOptionT cmd))
  }.

  Instance OptionTError {mMonad:Monad m} : MonadExc unit optionT :=
  { raise _u _A := zero
  ; catch _A aMM f := mkOptionT
      (aM <- unOptionT aMM ;;
       match aM with
       | None => unOptionT (f tt)
       | Some x => ret (Some x)
       end)
  }.

End Trans.
