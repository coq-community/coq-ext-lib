Require Import ExtLib.Sets.Sets.
Require Import Bool.

Set Implicit Arguments.
Set Strict Implicit.

(** Program with respect to the set interface **)
Section with_set.
  Variable V : Type.
  Variable set : Type.
  Context {Set_set : CSet set (@eq V)}.

  Definition contains_both (v1 v2 : V) (s : set) : bool :=
    contains v1 s && contains v2 s.

End with_set.

(** Instantiate the set **)
Require Import ExtLib.Sets.ListSet.
Require Import ExtLib.Decidables.Decidable.

Eval compute in contains_both (set := lset (@eq nat)) 0 1 empty.