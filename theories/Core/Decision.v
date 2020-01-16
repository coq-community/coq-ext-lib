Require Import Coq.Classes.DecidableClass.

Definition decideP (P : Prop) (D : Decidable P) : {P} + {~P} :=
  match @Decidable_witness P D as X return (X = true -> P) -> (X = false -> ~P) -> {P} + {~P} with
  | true => fun pf _ => left (pf eq_refl)
  | false => fun _ pf => right (pf eq_refl)
  end (@Decidable_sound _ D) (@Decidable_complete_alt _ D).

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
