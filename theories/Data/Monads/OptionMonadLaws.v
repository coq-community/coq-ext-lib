Require Import RelationClasses.
Require Import Setoid.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Structures.MonadLaws.
Require Import ExtLib.Data.Monads.OptionMonad.

Set Implicit Arguments.
Set Strict Implicit.

Section Laws.
  Variable m : Type -> Type.
  Variable Monad_m : Monad m.
  Variable mleq : forall T, (T -> T -> Prop) -> m T -> m T -> Prop.
  Variable mproper : forall T, Proper T -> Proper (m T).
  Variable MonadOrder_mleq : MonadOrder m mproper mleq.
  Variable MonadLaws_mleq : MonadLaws Monad_m mproper mleq.

  Definition o_mleq T (e : T -> T -> Prop) (a b : optionT m T) : Prop :=
    mleq (fun l r =>
      match l , r with
        | None , None => True
        | Some l , Some r => e l r
        | _ , _ => False
      end)
    (unOptionT a) (unOptionT b).

  Global Instance Proper_optionT {T : Type} {PT : Proper T} : Proper (optionT m T) :=
  { proper := fun o => @proper _ (mproper (fun o => match o with
                                                      | None => True
                                                      | Some x => proper x
                                                    end)) (unOptionT o) }.

  Global Instance MonadOrder_omleq : MonadOrder (optionT m) _ o_mleq.
  Proof.
    constructor.
    { intros. red. destruct x; red; simpl. unfold proper. unfold Proper_optionT. simpl.
      intros. eapply me_refl; eauto. red; intros. destruct x; auto. }
    { intros; red; destruct x; destruct y; destruct z; red; simpl in *; try congruence; intros.
      eapply me_trans; [ | | | | | eassumption | eassumption ]; eauto.
      red; simpl in *.
      destruct x; destruct y; destruct z; try congruence; intuition.
      eapply ptransitive; [ | | | | eassumption | eassumption ]; eauto. }
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

  Instance Proper_option {T : Type} (P : Proper T) : Proper (option T) :=
  { proper := fun o => match o with
                         | None => True
                         | Some x => proper x
                       end }.

  Instance refl_omleq : forall A (P : Proper A) (eA : A -> A -> Prop),
    PReflexive eA ->
    PReflexive (fun l r : option A =>
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

  Instance trans_omleq : forall A (Pa : Proper A) (eA : A -> A -> Prop),
    PTransitive eA ->
    PTransitive (fun l r : option A =>
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
    eapply ptransitive; [ | | | | eassumption | eassumption ]; eauto.
  Qed.

  Global Instance MonadLaws_optionT : MonadLaws (@Monad_optionT _ Monad_m) _ o_mleq.

  Proof.
    constructor; eauto with typeclass_instances.
    { intros. simpl. eapply lower_meq; simpl.
      eapply bind_of_return; eauto. }
    { intros; simpl. eapply lower_meq; simpl.
      eapply return_of_bind; eauto.
      eauto using refl_omleq.
      { destruct x; compute; intros; try eapply ret_proper; eauto.
        eapply H1. eauto. }
      { destruct x. specialize (H2 a).
        red in H0. simpl in *. unfold o_mleq in *. eauto.
        eapply preflexive. eapply PReflexive_meq; eauto using refl_omleq.
        eapply ret_proper; eauto. exact I. } }
    { intros; simpl. eapply lower_meq; simpl.
      eapply ptransitive. eapply PTransitive_meq; eauto using trans_omleq.
      repeat eapply bind_proper; eauto. 
      eauto using bind_proper, ret_proper.
      eapply me_trans.XS
      eapply bind_associativity.

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
