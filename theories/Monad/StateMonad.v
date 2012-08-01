Require Import Monad.

Set Implicit Arguments.
Set Strict Implicit.

Section StateType.
  Variable S : Type.

  Record state (t : Type) : Type := mkState
  { runState : S -> t * S }.

  Instance Monad_state : Monad state :=
  { ret  := fun _ v => mkState (fun s => (v, s))
  ; bind := fun _ c1 _ c2 => 
    mkState (fun s => 
      let (v,s) := runState c1 s in
      runState (c2 v) s)
  }.

  Instance State_state : State S state :=
  { get := mkState (fun x => (x,x))
  ; put := fun v => mkState (fun _ => (tt, v))
  }.

  Variable m : Type -> Type.

  Record stateT (t : Type) : Type := mkStateT
  { runStateT : S -> m (t * S)%type }.

  Instance Monad_stateT (M : Monad m) : Monad stateT :=
  { ret := fun _ x => mkStateT (fun s => @ret _ M _ (x,s))
  ; bind := fun _ c1 _ c2 =>
    mkStateT (fun s => 
      @bind _ M _ (runStateT c1 s) _ (fun vs =>
        let (v,s) := vs in
        runStateT (c2 v) s))
  }.

  Instance State_stateT (M : Monad m) : State S stateT :=
  { get := mkStateT (fun x => ret (x,x))
  ; put := fun v => mkStateT (fun _ => ret (tt, v))
  }.

End StateType.