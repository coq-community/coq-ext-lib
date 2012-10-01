Require Import RelationClasses.
Require Import Setoid.
Require Import ExtLib.Monad.Monad.
Require Import ExtLib.Monad.MonadLaws.
Require Import ExtLib.Monad.OptionMonad.

Set Implicit Arguments.
Set Strict Implicit.

Section Laws.
  Variable m : Type -> Type.
  Variable Monad_m : Monad m.
  Variable mleq : forall T, (T -> T -> Prop) -> m T -> m T -> Prop.
  Variable MonadOrder_mleq : MonadOrder Monad_m mleq.
  Variable MonadLaws_mleq : MonadLaws Monad_m mleq.

  Definition o_mleq T (e : T -> T -> Prop) (a b : optionT m T) : Prop :=
    mleq (fun l r =>
      match l , r with
        | None , None => True
        | Some l , Some r => e l r
        | _ , _ => False
      end)
    (unOptionT a) (unOptionT b).

  Global Instance MonadOrder_omleq : MonadOrder (@Monad_optionT _ _) o_mleq.
  Proof.
    constructor.
    { intros. red. destruct x; red; simpl.
      eapply me_refl; eauto. red; intros. destruct x; auto. }
    { intros; red; destruct x; destruct y; destruct z; red; simpl in *; try congruence; intros.
      eapply me_trans; eauto. red; simpl in *.
      destruct x; destruct y; destruct z; try congruence; intuition.
      etransitivity; eassumption. }
    { intros. unfold o_mleq. simpl. eapply me_ret; eauto. }
  Qed.

  Lemma lower_meq : forall (A : Type) (c c' : optionT m A)
    (eA : A -> A -> Prop),
    meq m mleq (fun l r =>
      match l , r with
        | None , None => True
        | Some l , Some r => eA l r
        | _ , _ => False
      end) (unOptionT c) (unOptionT c') ->
    meq (optionT m) o_mleq eA c c'.
  Proof.
    destruct 1; split; simpl in *; auto.
  Qed.

  Instance refl_omleq : forall A (eA : A -> A -> Prop),
    Reflexive eA ->
    Reflexive (fun l r : option A =>
      match l with
        | Some l0 => match r with
                       | Some r0 => eA l0 r0
                       | None => False
                     end
        | None => match r with
                    | Some _ => False
                    | None => True
                  end
      end).
  Proof.
    intros; destruct x; simpl; auto.
  Qed.

  Instance trans_omleq : forall A (eA : A -> A -> Prop),
    Transitive eA ->
    Transitive (fun l r : option A =>
      match l with
        | Some l0 => match r with
                       | Some r0 => eA l0 r0
                       | None => False
                     end
        | None => match r with
                    | Some _ => False
                    | None => True
                  end
      end).
  Proof.
    intros; destruct x; destruct y; destruct z; simpl; auto; intuition.
    etransitivity; eassumption.
  Qed.

  Global Instance MonadLaws_optionT : MonadLaws (@Monad_optionT _ Monad_m) o_mleq.
  Proof.
    constructor; eauto with typeclass_instances.
    { intros. simpl. eapply lower_meq; simpl.
      eapply bind_of_return; eauto. }
    { intros; simpl. eapply lower_meq; simpl.
      eapply return_of_bind; eauto.
      eauto using refl_omleq.
      { destruct x. specialize (H0 a).
        red in H0. simpl in *. unfold o_mleq in *. eauto.
        reflexivity. } }
    { intros; simpl. eapply lower_meq; simpl.
      rewrite bind_associativity; eauto with typeclass_instances.
      eapply bind_parametric_tl. eauto. eauto with typeclass_instances.
      destruct a. reflexivity. rewrite bind_of_return; eauto.
      reflexivity. }
    { intros; unfold o_mleq in *; simpl in *.
      destruct c; destruct c'; simpl in *.
      eapply bind_parametric_hd_leq. eauto. eassumption. }
    { intros; unfold o_mleq in *; simpl in *.
      destruct c; simpl in *.
      eapply bind_parametric_tl_leq; eauto with typeclass_instances.
      destruct a; auto. eapply me_refl; eauto with typeclass_instances. }
  Qed.

  Global Instance MonadTLaws_optionT : @MonadTLaws (optionT m) (@Monad_optionT m _)
    o_mleq m Monad_m (@MonadT_optionT _ Monad_m).
  Proof.
    constructor; intros; simpl; eapply lower_meq; unfold liftM; simpl; monad_norm;
      reflexivity.
  Qed.

End Laws.
