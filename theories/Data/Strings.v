Require Import String.
Require Import Tactics.Consider.
Require Import EqNat.

Set Implicit Arguments.
Set Strict Implicit.

Definition ascii_dec (l r : Ascii.ascii) : bool :=
  beq_nat (Ascii.nat_of_ascii l) (Ascii.nat_of_ascii r).

Theorem ascii_dec_sound : forall l r, 
  ascii_dec l r = true <-> l = r.
Proof.
  unfold ascii_dec. intros.
  consider (beq_nat (Ascii.nat_of_ascii l) (Ascii.nat_of_ascii r)); firstorder.
  rewrite <- Ascii.ascii_nat_embedding. symmetry. 
  rewrite <- Ascii.ascii_nat_embedding. f_equal. auto. congruence.
  congruence.
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

Global Instance Reflect_string_dec a b : Reflect (string_dec a b) (a = b) (a <> b).
Proof. 
  apply iff_to_reflect; auto using string_dec_sound.
Qed.
