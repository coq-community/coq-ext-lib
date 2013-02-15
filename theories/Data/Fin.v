Require List.

Set Implicit Arguments.
Set Strict Implicit.

Inductive fin : nat -> Type :=
| F0 : forall {n}, fin (S n)
| FS : forall {n}, fin n -> fin (S n).

Fixpoint fin_all (n : nat) : list (fin n) :=
  match n as n return list (fin n) with
    | 0 => nil
    | S n => @F0 n :: List.map (@FS _) (fin_all n)
  end%list.

Theorem fin_all_In : forall {n} (f : fin n),
  List.In f (fin_all n).
Proof.
  induction n; intros. 
  inversion f.
  remember (S n). destruct f.
  simpl; firstorder.
  inversion Heqn0. subst.
  simpl. right. apply List.in_map. auto.
Qed.  

Theorem fin_case : forall n (f : fin (S n)),
  f = F0 \/ exists f', f = FS f'.
Proof.
  intros. generalize (fin_all_In f). intros.
  destruct H; auto.
  eapply List.in_map_iff in H. right. destruct H.
  exists x. intuition.
Qed.
