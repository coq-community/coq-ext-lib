Require Import RelationClasses.
Require Import Setoid.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.MonadLaws.
Require Import ExtLib.Data.Monads.ReaderMonad.

Set Implicit Arguments.
Set Strict Implicit.

Section Laws2.
  Variable m : Type -> Type.
  Variable Monad_m : Monad m.
  Variable mleq : forall T, (T -> T -> Prop) -> m T -> m T -> Prop.
  Variable MonadOrder_mleq : MonadOrder Monad_m mleq.
  Variable MonadLaws_mleq : MonadLaws Monad_m mleq.

  Variable S : Type.
(**
  (** NOTE: This should be quotiented, something like this:
   **)
  Variable Seq : S -> S -> Prop.
  Variable Refl_Seq : Reflexive Seq.
  Variable Trans_Seq : Transitive Seq.
  
  Definition r_mleq T (e : T -> T -> Prop) (a b : readerT S m T) : Prop :=
    forall s1 s2, Seq s1 s2 -> mleq e (runReaderT a s1) (runReaderT b s2).
  (** But you can't prove that this relation is reflexive unless you know that
   ** the functions inside a and b respect [Seq], but that is what we are proving
   **)
**)

  Definition r_mleq T (e : T -> T -> Prop) (a b : readerT S m T) : Prop :=
    forall s, mleq e (runReaderT a s) (runReaderT b s).

  Global Instance MonadOrder_rmleq : MonadOrder (Monad_readerT S Monad_m) r_mleq.
  Proof.
    constructor.
    { intros. red. destruct x; red; simpl. intros.
      eapply me_refl; eauto. }
    { intros; red; destruct x; destruct y; destruct z; red; simpl in *; try congruence; intros.
      eapply me_trans; eauto. }
    { unfold r_mleq; simpl; intros.
      apply me_ret; eauto. }
  Qed.

  Lemma lower_meq : forall (A : Type) (c c' : readerT S m A)
    (eA : A -> A -> Prop),
    (forall s, meq _ mleq eA (runReaderT c s) (runReaderT c' s)) ->
    meq (readerT S m) r_mleq eA c c'.
  Proof.
    intros. split; unfold r_mleq; intro s; destruct (H s); auto.
  Qed.

  Global Instance MonadLaws_readerT : MonadLaws (@Monad_readerT S _ Monad_m) r_mleq.
  Proof.
    constructor; eauto with typeclass_instances.
    { intros. simpl. eapply lower_meq; simpl.
      intros. apply bind_of_return; eauto. }
    { intros; simpl. eapply lower_meq; simpl.
      intro. eapply return_of_bind; eauto.
      intro. specialize (H0 x). destruct H0. unfold r_mleq in *.
      specialize (H0 s); specialize (H1 s). split; auto. }
    { intros; simpl. eapply lower_meq; simpl.
      intro.
      rewrite bind_associativity; eauto with typeclass_instances.
      eapply bind_parametric_tl; eauto with typeclass_instances.
      intro. reflexivity. }
    { intros; unfold r_mleq in *; simpl in *.
      destruct c; destruct c'; simpl in *.
      intro; eapply bind_parametric_hd_leq. eauto. eapply H. }
    { intros; unfold r_mleq in *; simpl in *.
      destruct c; simpl in *.
      intro; eapply bind_parametric_tl_leq; eauto with typeclass_instances. }
  Qed.

  Global Instance MonadTLaws_readerT : @MonadTLaws (readerT S m) (@Monad_readerT S m _)
    r_mleq m Monad_m (@MonadT_readerT _ m).
  Proof.
    constructor; intros; simpl; eapply lower_meq; unfold liftM; simpl; monad_norm;
      reflexivity.
  Qed.

End Laws2.
