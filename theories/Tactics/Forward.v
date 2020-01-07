Ltac forward_reason :=
  repeat match goal with
           | H : exists x, _ |- _ =>
             destruct H
           | H : _ /\ _ |- _ => destruct H
           | H' : ?X , H : ?X -> ?Y |- _ =>
             match type of X with
               | Prop => specialize (H H')
             end
           | H : ?X -> ?Y |- _ =>
             match type of X with
               | Prop =>
                 let H' := fresh in
                 assert (H' : X) by eauto ;
               specialize (H H') ;
               clear H'
             end
         end.

(* based on a 2013 version of software foundations/libtatics *)
Definition ltac_something (P:Type) (e:P) := e.

Notation "'Something'" := 
  (@ltac_something _ _).

Lemma ltac_something_eq : forall (e:Type),
  e = (@ltac_something _ e).
Proof. auto. Qed.

Lemma ltac_something_hide : forall (e:Type),
  e -> (@ltac_something _ e).
Proof. auto. Qed.

Lemma ltac_something_show : forall (e:Type),
  (@ltac_something _ e) -> e.
Proof. auto. Qed.

Ltac show_hyp H :=
  apply ltac_something_show in H.

Ltac hide_hyp H :=
  apply ltac_something_hide in H.

Ltac show_hyps :=
  repeat match goal with
    H: @ltac_something _ _ |- _ => show_hyp H end.

Ltac rwHyps :=
  repeat match goal with
           [ H: _ = _ |- _] =>  repeat rewrite -> H; hide_hyp H
         end; show_hyps.

Ltac rwHypsR :=
  repeat match goal with
           [ H: _ = _ |- _] =>  repeat rewrite <- H; hide_hyp H
         end; show_hyps.

Ltac rwHypsA :=
  repeat match goal with
           [ H: _ = _ |- _] =>  repeat rewrite -> H in *; hide_hyp H
         end; show_hyps.

Ltac rwHypsRA :=
  repeat match goal with
           [ H: _ = _ |- _] =>  repeat rewrite <- H in *; hide_hyp H
         end; show_hyps.

(* based on a tactic written by Vincent Rahli *)
Ltac clear_trivials :=
  repeat match goal with
           | [ H : ?T = ?T |- _ ] => clear H
           | [ H : ?T <-> ?T |- _ ] => clear H
           | [ H : ?T -> ?T |- _ ] => clear H
           | [ H1 : ?T, H2 : ?T |- _ ] => clear H2
           | [ H : True |- _ ] => clear H
           | [ H : not False |- _ ] => clear H
         end.
