Set Implicit Arguments.
Set Strict Implicit.

Section PairWF.
  Variables T U : Type.
  Variable RT : T -> T -> Prop.
  Variable RU : U -> U -> Prop.
  
  Inductive R_pair : T * U -> T * U -> Prop :=
  | L : forall l l' r r',
    RT l l' -> R_pair (l,r) (l',r')
  | R : forall l r r',
    RU r r' -> R_pair (l,r) (l,r').

  Hypothesis wf_RT : well_founded RT.
  Hypothesis wf_RU : well_founded RU.

  Theorem wf_R_pair : well_founded R_pair.
  Proof.
    red. intro x.
    destruct x. generalize dependent u.
    apply (well_founded_ind wf_RT (fun t => forall u : U, Acc R_pair (t, u))) .
    do 2 intro.

    apply (well_founded_ind wf_RU (fun u => Acc R_pair (x,u))). intros.
    constructor. destruct y.
    remember (t0,u). remember (x,x0). inversion 1; subst;
    inversion H4; inversion H3; clear H4 H3; subst; eauto.
  Defined.
End PairWF.

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

Inductive R_list_len {T} : list T -> list T -> Prop :=
| R_len : forall n m, length n < length m -> R_list_len n m.

Theorem wf_R_list_len T : well_founded (@R_list_len T).
Proof.
  constructor. intros.
  refine (@Fix _ _ wf_R_lt (fun n : nat => forall ls : list T, n = length ls -> Acc R_list_len ls) 
    (fun x rec ls pfls => Acc_intro _ _)
    _ _ refl_equal).
  refine (
  match ls as ls return x = length ls -> forall z : list T, R_list_len z ls -> Acc R_list_len z with
    | nil => fun (pfls : x = 0) z pf => _
    | cons l ls => fun pfls z pf =>
      rec _ (match pf in R_list_len xs ys return x = length ys -> R_nat_lt (length xs) x with
               | R_len n m pf' => fun pf_eq => match eq_sym pf_eq in _ = x return R_nat_lt (length n) x with
                                                 | refl_equal => R_lt pf'
                                               end
             end pfls) _ eq_refl
  end pfls).
  clear - pf; abstract (inversion pf; subst; simpl in *; inversion H).
Defined.

Fixpoint guard A (R : A -> A -> Prop) (n : nat) (wfR : well_founded R)
  {struct n}: well_founded R :=
  match n with
    | 0 => wfR
    | S n => fun x => Acc_intro x (fun y _ => guard n (guard n wfR) y)
  end.