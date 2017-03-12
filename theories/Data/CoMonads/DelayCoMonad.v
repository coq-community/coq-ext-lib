Require Import ExtLib.Structures.CoMonad.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Section Delay.

  Inductive Delay (T:Type): Type :=
    delayed (x:T) : Delay T.

  Definition undelay {T:Type} (d: Delay T): (unit -> T) :=
    match d with
      delayed x =>  fun _ => x
    end.

  Global Instance DelayComonad:
    CoMonad (Delay) :=
    {
      extract A ma := (undelay ma) tt ;
      extend A B f ma := delayed (f ma)
    }.

End Delay.
