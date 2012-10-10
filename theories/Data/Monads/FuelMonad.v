Require Import ExtLib.Structures.Monads.

Set Implicit Arguments.
Set Strict Implicit.

(** The GFix monad is like monad fix except that
 ** it encapsulates the "gas" that is used as the measure
 **)
Section gfix.
  Variable m : Type -> Type.
  Context {M : Monad m}.

  (** This is essentially ReaderT (optionT m)) **)
  Inductive GFixT (T : Type) : Type := mkGFixT
  { runGFixT : nat -> m (option T) }.

  Global Instance MonadFix_GFixT : MonadFix GFixT :=
  { mfix := fun T U f =>
    let F := fix rec (gas : nat) : T -> m (option U) :=
      fun v => runGFixT (f (fun t => mkGFixT (fun _ =>
        match gas with
          | 0 => ret None
          | S n => rec n t
        end)) v) gas
    in fun v => mkGFixT (fun g => F g v)
  }.


  Global Instance Monad_GFixT : Monad GFixT :=
  { ret := fun _ v => mkGFixT (fun _ => ret (Some v))
  ; bind := fun _ c1 _ c2 =>
    mkGFixT (fun gas =>
      bind (runGFixT c1 gas) (fun x =>
        match x with
          | None => ret None
          | Some v => runGFixT (c2 v) gas
        end))
  }.

  Global Instance MonadT_GFixT : MonadT GFixT m :=
  { lift := fun _ c =>
    mkGFixT (fun _ => bind c (fun x => ret (Some x)))
  }.

  Global Instance MonadState_GFixT {T} (SM : MonadState T m) : MonadState T GFixT :=
  { get := lift get
  ; put := fun v => lift (put v)
  }.

  Global Instance MonadReader_GFixT {T} (RM : MonadReader T m) : MonadReader T GFixT :=
  { ask := lift ask
  ; local := fun v _ c => mkGFixT (fun gas => local v (runGFixT c gas))
  }.

  Global Instance MonadZero_GFixT (ZM : MonadZero m) : MonadZero GFixT :=
  { mzero := fun _ => lift mzero }.

  Global Instance Exception_GFixT {E} (ME : MonadExc E m) : MonadExc E GFixT :=
  { raise := fun _ v => lift (raise v)
  ; catch := fun _ c h => mkGFixT (fun s => catch (runGFixT c s) (fun x => runGFixT (h x) s))
  }.

End gfix.

(*
Require Import IdentityMonad.
Require Import Decidable.

Definition func : nat -> GFixT ident nat :=
  mfix (fun rec n =>
    if eq_dec n 9 then ret 100 else rec (S n)).

Eval compute in runGFixT (func 0) 8.
Eval compute in runGFixT (func 0) 9.
*)
