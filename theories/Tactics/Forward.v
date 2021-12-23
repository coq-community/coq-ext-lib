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

Ltac rwHyps :=
  repeat match goal with
           [ H: ?l = ?r |- _] =>
           match r with
           | context [l] => idtac
           | _ => rewrite -> H
           end
         end.

Ltac rwHypsR :=
  repeat match goal with
           [ H: _ = _ |- _] =>  rewrite <- H
         end.

Ltac rwHypsA :=
  repeat match goal with
           [ H: _ = _ |- _] =>  rewrite -> H in *
         end.

Ltac rwHypsRA :=
  repeat match goal with
           [ H: _ = _ |- _] =>  rewrite <- H in *
         end.

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
