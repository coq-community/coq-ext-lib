Require Import String.
Require Import EqNat.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Data.Char.

Set Implicit Arguments.
Set Strict Implicit.

Local Notation "x >> y" := (match x with
                              | Eq => y
                              | z => z
                            end) (only parsing, at level 30).

Definition bool_cmp (l r : bool) : comparison :=
  match l , r with
    | true , false => Gt
    | false , true => Lt
    | true , true
    | false , false => Eq
  end.

Definition ascii_cmp (l r : Ascii.ascii) : comparison :=
  match l , r with
    | Ascii.Ascii l1 l2 l3 l4 l5 l6 l7 l8 ,
      Ascii.Ascii r1 r2 r3 r4 r5 r6 r7 r8 =>
      bool_cmp l1 r1 >> bool_cmp l2 r2 >> bool_cmp l3 r3 >> bool_cmp l4 r4 >>
      bool_cmp l5 r5 >> bool_cmp l6 r6 >> bool_cmp l7 r7 >> bool_cmp l8 r8
  end.

Fixpoint string_dec (l r : string) : bool :=
  match l , r with
    | EmptyString , EmptyString => true
    | String l ls , String r rs =>
      if ascii_dec l r then string_dec ls rs
      else false
    | _ , _ => false
  end.

Theorem string_dec_sound : forall l r,
  string_dec l r = true <-> l = r.
Proof.
  induction l; destruct r; simpl; split; try solve [ intuition ; congruence ];
  consider (ascii_dec a a0); intros; subst. f_equal. eapply IHl; auto.
  apply IHl. congruence.
  inversion H. congruence.
Qed.

Global Instance RelDec_string : RelDec (@eq string) :=
{| rel_dec := string_dec |}.

Global Instance RelDec_Correct_string : RelDec_Correct RelDec_string.
Proof.
  constructor; auto using string_dec_sound.
Qed.

Global Instance Reflect_string_dec a b : Reflect (string_dec a b) (a = b) (a <> b).
Proof.
  apply iff_to_reflect; auto using string_dec_sound.
Qed.

Fixpoint string_cmp (l r : string) : comparison :=
  match l , r with
    | EmptyString , EmptyString => Eq
    | EmptyString , _ => Lt
    | _ , EmptyString => Gt
    | String l ls , String r rs =>
      ascii_cmp l r >> string_cmp ls rs
  end.

Require Import Ascii.


Section Program_Scope.
  Require Import Program.
  Import Arith Div2.
  Variable mod : nat.
  Hypothesis one_lt_mod : 1 < mod.

  Program Fixpoint nat2string (n:nat) {measure n}: string :=
    match NPeano.ltb n mod as x return NPeano.ltb n mod = x -> string with
      | true => fun _ => String (digit2ascii n) EmptyString
      | false => fun pf =>
        let m := NPeano.div n mod in
        String.append (nat2string m) (String (digit2ascii (n - 10 * m)) EmptyString)
    end eq_refl.
  Next Obligation.
    (* assert (NPeano.div n mod < n); eauto. *) eapply NPeano.Nat.div_lt; auto.
    consider (NPeano.ltb n mod); try congruence. intros. omega.
  Defined.

End Program_Scope.

Definition nat2string10 : nat -> string.
refine (@nat2string 10 _).
repeat constructor.
Defined.

Definition nat2string2 : nat -> string.
refine (@nat2string 2 _).
repeat constructor.
Defined.

Definition nat2string8 : nat -> string.
refine (@nat2string 8 _).
repeat constructor.
Defined.

Definition nat2string16 : nat -> string.
refine (@nat2string 16 _).
repeat constructor.
Defined.

Global Instance Foldable_string : Foldable string ascii :=
  fun _ f =>
    fix go acc ls :=
    match ls with
      | EmptyString => acc
      | String l ls =>
        go (f l acc) ls
    end.
