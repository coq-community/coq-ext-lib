Set Implicit Arguments.
Set Strict Implicit.

Inductive R_nat_S : nat -> nat -> Prop :=
| R_S : forall n, R_nat_S n (S n).

Theorem wf_R_S : well_founded R_nat_S.
Proof.
  red; induction a; constructor; intros.
    inversion H.
    inversion H; subst; auto.
Defined.

Inductive R_nat_lt : nat -> nat -> Prop :=
| R_lt : forall n m, n < m -> R_nat_lt n m.

Theorem wf_R_lt : well_founded R_nat_lt.
Proof.
  red; induction a; constructor; intros.
  { inversion H. exfalso. subst. inversion H0. }
  { inversion H; clear H; subst. inversion H0; clear H0; subst; auto.
    inversion IHa. eapply H. constructor. eapply H1. }
Defined.