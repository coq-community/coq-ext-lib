Require Import ExtLib.Structures.Monads.
Require Import List.

Set Implicit Arguments.
Set Strict Implicit.

Global Instance Monad_list : Monad list :=
{ ret := fun _ v => v :: nil
; bind := fix recur _ c1 _ c2 :=
  match c1 with
    | nil => nil
    | a :: b => c2 a ++ recur _ b _ c2
  end
}.

Global Instance Zero_list : MonadZero list :=
{ mzero := @nil }.
