Require Import Coq.Bool.Bool.
Require NPeano.
Import NPeano.Nat.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Data.Nat.

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Set Implicit Arguments.
Set Strict Implicit.

(**  Some tests *)
Section test.
  Goal forall x y z,  (ltb x y && ltb y z) = true ->
                 ltb x z = true.
  intros x y z.
  consider (ltb x y && ltb y z).
  consider (ltb x z); auto. intros. exfalso. lia.
  Qed.

  Goal forall x y z,
    ltb x y = true ->
    ltb y z = true ->
    ltb x z = true.
  Proof.
    intros. consider (ltb x y); consider (ltb y z); consider (ltb x z); intros; auto.
    exfalso; lia.
  Qed.

End test.
