Require Import ExtLib.Structures.CoMonad.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Primitive Projections.

Section Delay.

  (** The delay comonad delays computation by hiding it behind a unit.
   ** NOTE: This isn't the same as `lazy` because it will repeat computation.
   **)
  Record Delay (T:Type): Type := delayed
  { unDelay : unit -> T }.

  Global Instance DelayComonad:
    CoMonad (Delay) :=
  {| extract := fun A ma => ma.(unDelay) tt
   ; extend := fun A B f ma => delayed (fun _ => f ma)
   ; duplicate := fun A ma => delayed (fun _ => ma) |}.

End Delay.
