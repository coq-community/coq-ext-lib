Require Import String.
Require Import Tactics.Consider.
Require Import EqNat.
Require Import Decidable.

Set Implicit Arguments.
Set Strict Implicit.

Definition ascii_dec (l r : Ascii.ascii) : bool :=
  match l , r with
    | Ascii.Ascii l1 l2 l3 l4 l5 l6 l7 l8 ,
      Ascii.Ascii r1 r2 r3 r4 r5 r6 r7 r8 =>
      if Bool.eqb l1 r1 then
      if Bool.eqb l2 r2 then
      if Bool.eqb l3 r3 then
      if Bool.eqb l4 r4 then
      if Bool.eqb l5 r5 then
      if Bool.eqb l6 r6 then
      if Bool.eqb l7 r7 then
      if Bool.eqb l8 r8 then true
        else false
        else false
        else false
        else false
        else false
        else false
        else false
        else false
  end.

Theorem ascii_dec_sound : forall l r,
  ascii_dec l r = true <-> l = r.
Proof.
  unfold ascii_dec. intros.
  destruct l; destruct r.
  repeat match goal with
           | [ |- (if ?X then _ else _) = true <-> _ ] =>
             consider X; intros; subst
         end; split; congruence.
Qed.

Global Instance RelDec_ascii : RelDec (@eq Ascii.ascii) :=
{| rel_dec := ascii_dec |}.

Global Instance RelDec_Correct_ascii : RelDec_Correct RelDec_ascii.
Proof.
  constructor. auto using ascii_dec_sound.
Qed.

Global Instance Reflect_ascii_dec a b : Reflect (ascii_dec a b) (a = b) (a <> b).
Proof.
  apply iff_to_reflect; auto using ascii_dec_sound.
Qed.

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
  inversion H0. congruence.
Qed.

Global Instance RelDec_string : RelDec (@eq string) :=
{| rel_dec := string_dec |}.

Global Instance RelDec_Correct_string : RelDec_Correct RelDec_string.
Proof.
  constructor. auto using string_dec_sound.
Qed.

Global Instance Reflect_string_dec a b : Reflect (string_dec a b) (a = b) (a <> b).
Proof.
  apply iff_to_reflect; auto using string_dec_sound.
Qed.

Require Import Ascii.

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
    | n => ascii_of_nat (n - 9 + nat_of_ascii "A")
  end%char.

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