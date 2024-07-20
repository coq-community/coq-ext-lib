From Coq.Lists Require Import List.
From Coq.Arith Require Import PeanoNat.

Set Implicit Arguments.
Set Strict Implicit.

Section parametric.
  Variable T : Type.

  Lemma nth_error_app_L : forall (A B : list T) n,
    n < length A ->
    nth_error (A ++ B) n = nth_error A n.
  Proof.
    induction A; destruct n; simpl; intros; auto.
    { inversion H. }
    { inversion H. }
    { eapply IHA. apply Nat.succ_lt_mono; assumption. }
  Qed.

  Lemma nth_error_app_R : forall (A B : list T) n,
    length A <= n ->
    nth_error (A ++ B) n = nth_error B (n - length A).
  Proof.
    induction A; destruct n; simpl; intros; auto.
    + inversion H.
    + apply IHA. apply Nat.succ_le_mono; assumption.
  Qed.

  Lemma nth_error_weaken : forall ls' (ls : list T) n v,
    nth_error ls n = Some v ->
    nth_error (ls ++ ls') n = Some v.
  Proof.
    clear. induction ls; destruct n; simpl; intros; unfold value, error in *; try congruence; auto.
  Qed.

  Lemma nth_error_nil : forall n,
    nth_error nil n = @None T.
  Proof.
    destruct n; reflexivity.
  Qed.

  Lemma nth_error_past_end : forall (ls : list T) n,
    length ls <= n ->
    nth_error ls n = None.
  Proof.
    clear. induction ls; destruct n; simpl; intros; auto.
    + inversion H.
    + apply IHls. apply Nat.succ_le_mono; assumption.
  Qed.

  Lemma nth_error_length : forall (ls ls' : list T) n,
    nth_error (ls ++ ls') (n + length ls) = nth_error ls' n.
  Proof.
    induction ls; simpl; intros.
    rewrite Nat.add_0_r. auto.
    rewrite <-Nat.add_succ_comm.
    simpl. eapply IHls.
  Qed.

  Theorem nth_error_length_ge : forall T (ls : list T) n,
    nth_error ls n = None -> length ls <= n.
  Proof.
    induction ls; destruct n; simpl in *; auto; simpl in *.
    + intro. apply Nat.le_0_l.
    + inversion 1.
    + intros. apply ->Nat.succ_le_mono. auto.
  Qed.

  Lemma nth_error_length_lt : forall {T} (ls : list T) n val,
    nth_error ls n = Some val -> n < length ls.
  Proof.
    induction ls; destruct n; simpl; intros; auto.
    + inversion H.
    + inversion H.
    + apply Nat.lt_0_succ.
    + apply ->Nat.succ_lt_mono. apply IHls with (1 := H).
  Qed.


  Theorem nth_error_map : forall U (f : T -> U) ls n,
    nth_error (map f ls) n = match nth_error ls n with
                               | None => None
                               | Some x => Some (f x)
                             end.
  Proof.
    induction ls; destruct n; simpl; auto.
  Qed.

End parametric.
