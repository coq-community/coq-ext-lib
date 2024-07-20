From Coq Require Import Bool.
From Coq Require Import PeanoNat.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Data.Nat.

From Coq Require Import ZArith.
From Coq Require Import Lia.

Set Implicit Arguments.
Set Strict Implicit.

(**  Some tests *)
Section test.
  Goal forall x y z,  (Nat.ltb x y && Nat.ltb y z) = true ->
                 Nat.ltb x z = true.
  intros x y z.
  consider (Nat.ltb x y && Nat.ltb y z).
  consider (Nat.ltb x z); auto. intros. exfalso. lia.
  Qed.

  Goal forall x y z,
    Nat.ltb x y = true ->
    Nat.ltb y z = true ->
    Nat.ltb x z = true.
  Proof.
    intros. consider (Nat.ltb x y); consider (Nat.ltb y z); consider (Nat.ltb x z); intros; auto.
    exfalso; lia.
  Qed.

End test.
