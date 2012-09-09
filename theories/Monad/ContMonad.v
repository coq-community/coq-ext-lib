Require Import Monad.

Set Implicit Arguments.
Set Strict Implicit.

Section ContType.
  Variable Ans : Type.

  Record cont (t : Type) : Type := mkCont
  { runCont : (t -> Ans) -> Ans }.

  Global Instance Monad_cont : Monad cont :=
  { ret  := fun _ v => mkCont (fun k => k v)
  ; bind := fun _ c1 _ c2 => 
    mkCont (fun k => 
      runCont c1 (fun t => 
        match c2 t with
          | mkCont k' => k' k
        end))
  }.

  Global Instance Cont_cont : Cont cont :=
  { callCC := fun _ _ f => mkCont (fun c => runCont (f (fun x => mkCont (fun _ => c x))) c)
  }.  

  Variable m : Type -> Type.

  Record contT (t : Type) : Type := mkContT
  { runContT : (t -> m Ans) -> m Ans }.

  Global Instance Monad_contT (M : Monad m) : Monad contT :=
  { ret := fun _ x => mkContT (fun k => k x)
  ; bind := fun _ c1 _ c2 =>
    mkContT (fun c => 
      runContT c1 (fun a => runContT (c2 a) c))
  }.

  Global Instance Cont_contT (M : Monad m) : Cont contT :=
  { callCC := fun _ _ f => mkContT (fun c => runContT (f (fun x => mkContT (fun _ => c x))) c)
  }.


End ContType.
