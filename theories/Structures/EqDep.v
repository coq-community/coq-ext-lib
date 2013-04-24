Require Coq.Logic.Eqdep_dec.
Require Import EquivDec.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Consider.

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

Section from_rel_dec.
  Variable T : Type.
  Variable RD : RelDec (@eq T).
  Variable RDC : RelDec_Correct RD.

  Global Instance EqDec_RelDec : EqDec T (@eq T).
  Proof.
    red; intros.
    consider (x ?[ eq ] y); intros; subst; auto.
    left. reflexivity.
  Qed.
End from_rel_dec.