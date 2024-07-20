From Coq.Lists Require Import List.
From Coq.ZArith Require Import ZArith.
From Coq.micromega Require Import Lia.

(** For backwards compatibility with hint locality attributes. *)
Set Warnings "-unsupported-attributes".

Lemma firstn_app_L : forall T n (a b : list T),
  n <= length a ->
  firstn n (a ++ b) = firstn n a.
Proof.
  induction n; destruct a; simpl in *; intros; auto.
  exfalso; lia.
  f_equal. eapply IHn; eauto. lia.
Qed.

Lemma firstn_app_R : forall T n (a b : list T),
  length a <= n ->
  firstn n (a ++ b) = a ++ firstn (n - length a) b.
Proof.
  induction n; destruct a; simpl in *; intros; auto.
  exfalso; lia.
  f_equal. eapply IHn; eauto. lia.
Qed.

Lemma firstn_all : forall T n (a : list T),
  length a <= n ->
  firstn n a = a.
Proof.
  induction n; destruct a; simpl; intros; auto.
  exfalso; lia.
  simpl. f_equal. eapply IHn; lia.
Qed.

Lemma firstn_0 : forall T n (a : list T),
  n = 0 ->
  firstn n a = nil.
Proof.
  intros; subst; auto.
Qed.

Lemma firstn_cons : forall T n a (b : list T),
  0 < n ->
  firstn n (a :: b) = a :: firstn (n - 1) b.
Proof.
  destruct n; intros.
  lia.
  simpl. replace (n - 0) with n; [ | lia ]. reflexivity.
Qed.

#[global]
Hint Rewrite firstn_app_L firstn_app_R firstn_all firstn_0 firstn_cons using lia : list_rw.

Lemma skipn_app_R : forall T n (a b : list T),
  length a <= n ->
  skipn n (a ++ b) = skipn (n - length a) b.
Proof.
  induction n; destruct a; simpl in *; intros; auto.
  exfalso; lia.
  eapply IHn. lia.
Qed.

Lemma skipn_app_L : forall T n (a b : list T),
  n <= length a ->
  skipn n (a ++ b) = (skipn n a) ++ b.
Proof.
  induction n; destruct a; simpl in *; intros; auto.
  exfalso; lia.
  eapply IHn. lia.
Qed.

Lemma skipn_0 : forall T n (a : list T),
  n = 0 ->
  skipn n a = a.
Proof.
  intros; subst; auto.
Qed.

Lemma skipn_all : forall T n (a : list T),
  length a <= n ->
  skipn n a = nil.
Proof.
  induction n; destruct a; simpl in *; intros; auto.
  exfalso; lia.
  apply IHn; lia.
Qed.

Lemma skipn_cons : forall T n a (b : list T),
  0 < n ->
  skipn n (a :: b) = skipn (n - 1) b.
Proof.
  destruct n; intros.
  lia.
  simpl. replace (n - 0) with n; [ | lia ]. reflexivity.
Qed.

#[global]
Hint Rewrite skipn_app_L skipn_app_R skipn_0 skipn_all skipn_cons using lia : list_rw.
