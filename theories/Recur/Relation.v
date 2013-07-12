Require Import ExtLib.Relations.TransitiveClosure.

Set Implicit Arguments.
Set Strict Implicit.

Section rightTrans.
  Variables (A : Type) (R : A -> A -> Prop).
  
  Variable wf_R : well_founded R.

  Theorem wf_rightTrans : well_founded (rightTrans R).
  Proof. 
    red.
    eapply Fix. eapply wf_R. clear.
    intros. constructor. intros.
    revert H.
    induction H0.
    { intros. eauto. }
    { intros. 
      eapply IHrightTrans; clear IHrightTrans.
      specialize (H1 _ H). inversion H1.
      intros. eapply H2. eapply RTFin. eassumption. }
  Defined.

End rightTrans.

