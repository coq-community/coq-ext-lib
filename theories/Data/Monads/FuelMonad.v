Require Import ExtLib.Structures.Monads.
Require Import BinPos.

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
  { runGFixT : N -> m (option T) }.

  Global Instance MonadFix_GFixT : MonadFix GFixT :=
  { mfix := fun T U f v => mkGFixT (fun n : N => 
    match n with
      | N0 => ret None
      | Npos g => 
        let F := fix rec (acc : T -> m (option U)) (gas : positive) (x : T) 
          : m (option U) :=
          match gas return m (option U) with
            | xI p => 
              runGFixT (f (fun x => mkGFixT (fun n => rec (fun x => rec acc p x) p x)) x) n
            | xO p => 
              rec (fun x => rec acc p x) p x
            | xH => runGFixT (f (fun x => mkGFixT (fun _ => acc x)) x) n
          end
        in F (fun x => runGFixT (f (fun _ => mkGFixT (fun _ => ret None)) x) n) g v
      end)
  }.

  Global Instance Monad_GFixT : Monad GFixT :=
  { ret := fun _ v => mkGFixT (fun _ => ret (Some v))
  ; bind := fun _ _ c1 c2 =>
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
  ; local := fun _ v c => mkGFixT (fun gas => local v (runGFixT c gas))
  }.

  Global Instance MonadZero_GFixT (ZM : MonadZero m) : MonadZero GFixT :=
  { mzero := fun _ => lift mzero }.

  Global Instance Exception_GFixT {E} (ME : MonadExc E m) : MonadExc E GFixT :=
  { raise := fun _ v => lift (raise v)
  ; catch := fun _ c h => mkGFixT (fun s => catch (runGFixT c s) (fun x => runGFixT (h x) s))
  }.

End gfix.

(** Demo
Require Import ExtLib.Data.Monads.IdentityMonad.
Definition foo : nat -> GFixT ident nat :=
  mfix (fun recur n => 
    match n with
      | 0 => ret 0
      | S n => recur n
    end).

Eval compute in runGFixT (foo 10) 100000000000000000000000.
**)
