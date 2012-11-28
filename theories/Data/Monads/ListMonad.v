Require Import ExtLib.Structures.Monads.
Require Import List.

Set Implicit Arguments.
Set Strict Implicit.

Global Instance Monad_list : Monad list :=
{ ret := fun _ v => v :: nil
; bind := fun _ _ => fix recur c1 c2 :=
  match c1 with
    | nil => nil
    | a :: b => c2 a ++ recur b c2
  end
}.

Global Instance MonadZero_list : MonadZero list :=
{ mzero := @nil }.
