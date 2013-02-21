Require Import RelationClasses.
Require Import Setoid.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.MonadLaws.
Require Import ExtLib.Data.Monads.FuelMonad.

Set Implicit Arguments.
Set Strict Implicit.

Section Laws2.
  Variable m : Type -> Type.
  Variable Monad_m : Monad m.
  Variable mleq : forall T, (T -> T -> Prop) -> m T -> m T -> Prop.
  Variable MonadOrder_mleq : MonadOrder Monad_m mleq.
  Variable MonadLaws_mleq : MonadLaws Monad_m mleq.

  Variable S : Type.
  (** NOTE: This should be quotiented **)

  Definition option_leq {T} (e : T -> T -> Prop) (l r : option T) : Prop :=
    match l , r with
      | None , _ => True
      | Some l , Some r => e l r
      | Some _ , None => False
    end.

  Local Instance Reflexive_option_leq {A} (eA : A -> A -> Prop) (ReA : Reflexive eA) : Reflexive (option_leq eA).
  Proof.
    clear - ReA.
    red; intro. destruct x; simpl; auto.
  Qed.

  Local Instance Transitive_option_leq {A} (eA : A -> A -> Prop) (ReA : Transitive eA) : Transitive (option_leq eA).
  Proof.
    clear - ReA.
    red; intro. destruct x; destruct y; destruct z; simpl; try contradiction; eauto.
  Qed.


  Definition f_mleq {T} (e : T -> T -> Prop) (l r : GFixT m T) : Prop :=
    forall n, 
      mleq (option_leq e) (runGFixT l n) (runGFixT r n).

  Global Instance MonadOrder_fmleq : MonadOrder (@Monad_GFixT _ Monad_m) (@f_mleq).
  Proof.
    constructor.
    { intros. red. destruct x; red; simpl. intros.      
      eapply me_refl; eauto. red; intros. destruct x; simpl; auto. }
    { intros; red; destruct x; destruct y; destruct z; red; simpl in *; try congruence; intros.
      eapply me_trans; eauto. red; intros. destruct x; destruct y; destruct z; try contradiction; auto.
      etransitivity; eassumption. }
    { unfold f_mleq; simpl; intros.
      apply me_ret; eauto. }
  Qed.

  Lemma lower_meq : forall (A : Type) (c c' : GFixT m A)
    (eA : A -> A -> Prop),
    (forall s, meq _ mleq (option_leq eA) (runGFixT c s) (runGFixT c' s)) <->
    meq (GFixT m) (@f_mleq) eA c c'.
  Proof.
    intros. split. 
    { split; unfold f_mleq; intro s; destruct (H s); auto. }
    { destruct 1; simpl; intros; split; auto. }
  Qed.

  Global Instance MonadLaws_readerT : MonadLaws (@Monad_GFixT _ Monad_m) (@f_mleq).
  Proof.
    constructor; eauto with typeclass_instances.
    { intros. eapply lower_meq; intros.
      eapply bind_of_return; eauto. }
    { intros; simpl. eapply lower_meq; simpl.
      intro. eapply return_of_bind; eauto.
      intro. reflexivity. destruct x; try reflexivity.
      specialize (H0 a). eapply lower_meq in H0. eassumption. }
    { intros; simpl. eapply lower_meq; simpl.
      intro.
      rewrite bind_associativity; eauto with typeclass_instances.
      eapply bind_parametric_tl; eauto with typeclass_instances.
      intro. destruct a; try reflexivity.
      rewrite bind_of_return by eauto with typeclass_instances.
      reflexivity. }
    { intros; unfold f_mleq in *; simpl in *.
      destruct c; destruct c'; simpl in *.
      intro; eapply bind_parametric_hd_leq. eauto. eapply H. }
    { intros; unfold f_mleq in *; simpl in *.
      destruct c; simpl in *.
      intro; eapply bind_parametric_tl_leq; eauto with typeclass_instances. 
      destruct a; eauto. eapply me_refl; eauto with typeclass_instances. }
  Qed.

  Global Instance MonadTLaws_GFixT : @MonadTLaws (GFixT m) (@Monad_GFixT m _)
    (@f_mleq) m Monad_m (@MonadT_GFixT m _).
  Proof.
    constructor; intros; simpl; eapply lower_meq; unfold liftM; simpl; monad_norm;
      reflexivity.
  Qed.

End Laws2.
