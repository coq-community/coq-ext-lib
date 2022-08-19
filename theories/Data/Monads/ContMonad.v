Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadTrans.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

Section ContType.
  Variable R : Type.

(*
  Record cont (t : Type) : Type := mkCont
  { runCont : (t -> Ans) -> Ans }.

  Global Instance Monad_cont : Monad cont :=
  { ret  := fun _ v => mkCont (fun k => k v)
  ; bind := fun _ c1 _ c2 =>
    mkCont (fun k =>
      runCont c1 (fun t =>
        runCont (c2 t) k))
  }.

  Global Instance Cont_cont : Cont cont :=
  { callCC := fun _ _ f => mkCont (fun c => runCont (f (fun x => mkCont (fun _ => c x))) c)
  }.

  Definition mapCont (f : Ans -> Ans) {a} (c : cont a) : cont a :=
    mkCont (fun x => f (runCont c x)).

  Definition withCont {a b} (f : (b -> Ans) -> (a -> Ans)) (c : cont a) : cont b :=
    mkCont (fun x => runCont c (f x)).
*)

  Variable M : Type -> Type.

  Record contT (A : Type) : Type := mkContT
  { runContT : (A -> M R) -> M R }.

  Global Instance Monad_contT : Monad contT :=
  { ret := fun _ x => mkContT (fun k => k x)
  ; bind := fun _ _ c1 c2 =>
    mkContT (fun c =>
      runContT c1 (fun a => runContT (c2 a) c))
  }.

  Global Instance MonadT_contT {Monad_M : Monad M} : MonadT contT M :=
  { lift := fun _ c => mkContT (bind c)
  }.

(*
  Definition mapContT (f : m Ans -> m Ans) {a} (c : contT a) : contT a :=
    mkContT (fun x => f (runContT c x)).

  Definition withContT {a b} (f : (b -> m Ans) -> (a -> m Ans)) (c : contT a) : contT b :=
    mkContT (fun x => runContT c (f x)).
*)

End ContType.

Definition resetT {M} {Monad_M : Monad M} {R R'} (u : contT R M R) : contT R' M R :=
  mkContT (fun k => bind (runContT u ret) k).

Definition shiftT {M} {Monad_M : Monad M} {R A}
    (f : (A -> M R) -> contT R M R) : contT R M A :=
  mkContT (fun k => runContT (f k) ret).
