Require Import Coq.Classes.DecidableClass.

Definition decideP (P:Prop) `{Decidable P} : {P} + {~P}.
  remember (decide P) as dec. 
  destruct dec; [left | right];
  symmetry in Heqdec;
  unfold decide in Heqdec;
  pose proof Decidable_spec; try tauto.
  intro Hc.
  rewrite <- H0 in Hc. congruence.
Defined.

Ltac cases_ifd Hn :=
  match goal with
    |- context[if ?d then ?tt else ?ff] =>
    let Hnt := fresh Hn "t" in
    let Hnf := fresh Hn "f" in
    destruct d as [Hnt | Hnf] end.

Lemma decide_decideP  {P:Prop }`{Decidable P} {R:Type} (a b : R) :
  (if (decide P) then  a else b) = (if (decideP P) then  a else b).
Proof.
  symmetry. unfold decide.
  destruct (decideP P).
- rewrite Decidable_complete; auto.
- rewrite Decidable_sound_alt; auto.
Qed.
