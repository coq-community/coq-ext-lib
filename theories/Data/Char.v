Require Import Coq.Strings.Ascii.
Require Import ExtLib.Data.Bool.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Core.RelDec.

Set Implicit Arguments.
Set Strict Implicit.

Global Instance RelDec_ascii : RelDec (@eq Ascii.ascii) :=
{ rel_dec := Ascii.eqb }.

Global Instance RelDec_Correct_ascii : RelDec_Correct RelDec_ascii.
Proof.
  constructor; auto using Ascii.eqb_eq.
Qed.

Global Instance Reflect_ascii_dec a b : Reflect (Ascii.eqb a b) (a = b) (a <> b).
Proof.
  apply iff_to_reflect; auto using Ascii.eqb_eq.
Qed.

Definition digit2ascii (n:nat) : Ascii.ascii :=
  match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | 9 => "9"
    | n => ascii_of_nat (n - 10 + nat_of_ascii "A")
  end%char.

Definition chr_newline : ascii :=
  Eval compute in ascii_of_nat 10.

Export Ascii.
