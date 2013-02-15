Require Coq.Logic.Eqdep_dec.
Require Import EquivDec.

Set Implicit Arguments.
Set Strict Implicit.

Section Classes.
  Context {A : Type}.
  Context {dec : EqDec A (@eq A)}.

  Theorem UIP_refl : forall {x : A} (p1 : x = x), p1 = refl_equal _.
    intros.
    eapply Coq.Logic.Eqdep_dec.UIP_dec. apply equiv_dec.
  Qed.

  Theorem UIP_equal : forall {x y : A} (p1 p2 : x = y), p1 = p2.
    eapply Coq.Logic.Eqdep_dec.UIP_dec. apply equiv_dec.
  Qed.

  Lemma inj_pair2 :
    forall (P:A -> Type) (p:A) (x y:P p),
      existT P p x = existT P p y -> x = y.
  Proof.
    intros. eapply Coq.Logic.Eqdep_dec.inj_pair2_eq_dec; auto.
  Qed.    

End Classes.

Ltac notVar X :=
  match X with
    | _ _ => idtac
    | _ _ _ => idtac
    | _ _ _ _ => idtac
    | _ _ _ _ _ => idtac
    | _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
  end.

Ltac uip_all :=
  repeat match goal with
           | [ H : _ = _ |- _ ] => rewrite H
           | [ |- context [ match ?X in _ = t return _ with 
                              | refl_equal => _ 
                            end ] ] => notVar X; generalize X
           | [ |- context [ eq_rect_r _ _ ?X ] ] => notVar X; generalize X
         end;
  intros;
    repeat match goal with
             | [ H : ?X = ?X |- _ ] => rewrite (UIP_refl H) in *
           end.
