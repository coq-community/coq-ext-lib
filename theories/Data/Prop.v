Require Import ExtLib.Core.Type.

Global Instance type_Prop : type Prop :=
{ equal := iff
; proper := fun _ => True
}.

Global Instance typeOk_Prop : typeOk type_Prop.
Proof.
  constructor; compute; firstorder.
Qed.

(** NOTE: These should fit into a larger picture, e.g. lattices or monoids **)
(** And/Conjunction **)
Lemma And_True_iff : forall P, (P /\ True) <-> P.
Proof. intuition. Qed.

Lemma And_And_iff : forall P, (P /\ P) <-> P.
Proof. intuition. Qed.

Lemma And_assoc : forall P Q R, (P /\ Q /\ R) <-> ((P /\ Q) /\ R).
Proof. intuition. Qed.

Lemma And_comm : forall P Q, (P /\ Q) <-> (Q /\ P).
Proof. intuition. Qed.

Lemma And_False_iff : forall P, (P /\ False) <-> False.
Proof. intuition. Qed.

Lemma And_cancel
: forall P Q R : Prop, (P -> (Q <-> R)) -> ((P /\ Q) <-> (P /\ R)).
Proof. intuition. Qed.

(** Or/Disjunction **)
Lemma Or_False_iff : forall P, (P \/ False) <-> P.
Proof. intuition. Qed.

Lemma Or_Or_iff : forall P, (P \/ P) <-> P.
Proof. intuition. Qed.

Lemma Or_assoc : forall P Q R, (P \/ Q \/ R) <-> ((P \/ Q) \/ R).
Proof. intuition. Qed.

Lemma Or_comm : forall P Q, (P \/ Q) <-> (Q \/ P).
Proof. intuition. Qed.

Lemma Or_True_iff : forall P, (P \/ True) <-> True.
Proof. intuition. Qed.

(** Forall **)
Lemma forall_iff : forall T P Q,
                     (forall x,
                        P x <-> Q x) ->
                     ((forall x : T, P x) <-> (forall x : T, Q x)).
Proof.
   intros. setoid_rewrite H. reflexivity.
Qed.

(** Exists **)
Lemma exists_iff : forall T P Q,
                     (forall x,
                        P x <-> Q x) ->
                     ((exists x : T, P x) <-> (exists x : T, Q x)).
Proof.
   intros. setoid_rewrite H. reflexivity.
Qed.