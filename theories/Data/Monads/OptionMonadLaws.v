Require Import RelationClasses.
Require Import Setoid.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Structures.FunctorRelations.
Require Import ExtLib.Structures.MonadLaws.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Monads.OptionMonad.

Set Implicit Arguments.
Set Strict Implicit.

Section Laws.
  Variable m : Type -> Type.
  Variable Monad_m : Monad m.
  Variable mleq : forall T, (T -> T -> Prop) -> m T -> m T -> Prop.
  Variable mproper : forall T (rT : relation T), Proper rT -> Proper (mleq rT).
  Variable FunctorOrder_mleq : FunctorOrder m mleq mproper.
  Variable MonadLaws_mleq : MonadLaws Monad_m mleq mproper.

  Definition o_mleq T (e : T -> T -> Prop) (a b : optionT m T) : Prop :=
    mleq (@eqv_option _ e) (unOptionT a) (unOptionT b).

  Global Instance Proper_optionT {T : Type} {rT : relation T} {PT : Proper rT} 
    : Proper (o_mleq rT) :=
  { proper := fun o => proper (unOptionT o) }.

  Global Instance FunctorOrder_omleq : FunctorOrder (optionT m) o_mleq (@Proper_optionT).
  Proof.
    constructor.
    { intros. red. destruct x; red; simpl. unfold proper. unfold Proper_optionT. simpl.
      intros. eapply fun_refl; eauto. red; intros. destruct x; auto.
      simpl in *. compute in H1. eauto. }
    { intros; red; destruct x; destruct y; destruct z; red; simpl in *; try congruence; intros.
      eapply fun_trans; [ | | | | | eassumption | eassumption ]; eauto.
      red; simpl in *.
      destruct x; destruct y; destruct z; try congruence; intuition.
      eapply ptransitive; [ | | | | eassumption | eassumption ]; eauto with typeclass_instances. red in H8. contradiction. }
  Qed.

  Instance refl_omleq : forall A (eA : A -> A -> Prop) (P : Proper eA) ,
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

  Instance trans_omleq : forall A (eA : A -> A -> Prop) (Pa : Proper eA),
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

  Existing Instance bind_proper. 
  Existing Instance ret_proper.
  Existing Instance fun_trans.
  Existing Instance fun_refl.

(*
  Theorem mproper_red : forall (C : Type) (Pc : Proper C) (o : optionT m C),
    proper o ->
    mproper (Proper_option Pc) (unOptionT o).
  Proof. clear. intros. apply H. Qed.
  
  Ltac solve_proper :=
    match goal with
      | [ |- proper ?X ] =>
        is_evar X ; fail 1
      | _ =>
        repeat match goal with
                 | [ H : @proper _ ?X _ |- _ ] => 
                   let z := eval hnf in X in 
                     match z with
                       | X => fail 1
                       | _ => do 2 red in H
                     end
                 | [ |- proper (ret _) ] => 
                   (eapply ret_proper; [ solve [ eauto with typeclass_instances ] | ])
                 | [ |- proper (bind _ _) ] => 
                   eapply bind_proper; [ solve [ eauto with typeclass_instances ] | | ]
                 | [ |- proper match ?X with _ => _ end ] => 
                   destruct X
                 | [ |- _ ] => red ; intros
                 | _ => solve [ eauto with typeclass_instances ]
               end
    end; try match goal with
               | [ |- mproper _ _ ] => eapply mproper_red
             end; eauto.
*)

  Instance proper_unOptionT_app : forall (B : Type) (eB : relation B) (Pb : Proper eB) 
    (A : Type) (a : A) (f : A -> optionT m B) (eA : relation A)
    (Pa : Proper eA), proper a -> proper f -> proper (unOptionT (f a)).
  Proof. intros. eapply H0; eauto. Qed.
  Instance proper_k : forall (A : Type) (eA : relation A) (Pa : Proper eA),
    PReflexive eA ->
    forall (B : Type) (f : A -> optionT m B) (eB : relation B)
      (Pb : Proper eB),
      PReflexive eB ->
      PTransitive eB ->
      proper f ->
      proper
      (fun aM : option A =>
        match aM with
          | Some a => unOptionT (f a)
          | None => ret None
        end).
  Proof.
    intros. split; intros.
    { destruct x. eapply H2; auto. eapply ret_proper; eauto with typeclass_instances. }
    { red; intros. 
      unfold eqv_option in *; destruct a; destruct b; simpl in *; try contradiction.
      eapply H2; eauto. eapply ret_respectful_leq; eauto with typeclass_instances. }
  Qed.
  Lemma mret_respectful : forall (A : Type) (eA : relation A),
    Proper eA -> forall x y : A, eA x y -> o_mleq eA (ret x) (ret y). 
  Proof. intros. simpl. unfold o_mleq; simpl.
    eapply ret_respectful_leq; eauto with typeclass_instances.
  Qed.
  Instance proper_match : forall (A : Type) (eA : relation A) (PA : Proper eA) 
    (B : Type) (eB : relation B) (Pb : Proper eB) 
    (x : option A),
    PReflexive eB ->
    proper x ->
    forall f : A -> optionT m B,
      proper f ->
      proper match x with
               | Some a => unOptionT (f a)
               | None => ret None
             end.
  Proof.
    destruct x; intros; eauto with typeclass_instances.
  Qed.

  Global Instance MonadLaws_optionT : MonadLaws (@Monad_optionT _ Monad_m) _ (@Proper_optionT).
  Proof.
    constructor; eauto with typeclass_instances.
    { red; intros; simpl.
      eapply ptransitive; [ | | | | eapply (@bind_of_return _ _ _ _ MonadLaws_mleq) | ]; eauto with typeclass_instances. 
      eapply bind_proper; eauto with typeclass_instances.
      eapply H3; eauto. }
    { red; intros; simpl. 
      eapply return_of_bind; eauto with typeclass_instances.
      { destruct x; simpl; intros. eapply H3. eapply ret_respectful_leq; eauto with typeclass_instances. exact I. } }
    { red; intros; simpl.
      eapply ptransitive; [ | | | | eapply (@bind_associativity _ _ _ _ MonadLaws_mleq) | ]; eauto with typeclass_instances.
      { eapply bind_proper; eauto with typeclass_instances.
        eapply bind_proper; eauto with typeclass_instances. }
      { eapply bind_proper; eauto with typeclass_instances.
        split; intros; eauto with typeclass_instances.
        { eapply bind_proper; eauto with typeclass_instances. }
        { red; intros. eapply bind_respectful_leq; eauto with typeclass_instances.
          destruct a; destruct b; simpl in *; try contradiction; eauto with typeclass_instances.
          eapply H5; eauto. eapply ret_respectful_leq; eauto with typeclass_instances.
          intros. destruct a0; destruct b0; simpl in *; try contradiction; eauto with typeclass_instances. eapply H6; eauto. eapply ret_respectful_leq; eauto with typeclass_instances. } }
      { eapply bind_proper; eauto with typeclass_instances.
        split; intros; eauto with typeclass_instances.
        { destruct x; eauto with typeclass_instances.
          eapply bind_proper; eauto with typeclass_instances. }
        { red; intros. 
          destruct a; destruct b; simpl in *; try contradiction; eauto with typeclass_instances.
          eapply bind_respectful_leq; eauto with typeclass_instances.
          eapply H5; eauto.
          intros. destruct a1; destruct b; simpl in *; try contradiction; 
          eauto with typeclass_instances. eapply H6; eauto. 
          eapply ret_respectful_leq; eauto with typeclass_instances.
          eapply ret_respectful_leq; eauto with typeclass_instances.
        } }      
      { eapply bind_respectful_leq; eauto with typeclass_instances.
        eapply preflexive; eauto with typeclass_instances.
        intros. destruct a; destruct b; simpl in *; try contradiction.
        { eapply bind_respectful_leq; eauto with typeclass_instances.
          eapply H5; eauto.
          intros. destruct a1; destruct b; simpl in *; try contradiction; eauto with typeclass_instances.
          eapply H6; eauto. eapply ret_respectful_leq; eauto with typeclass_instances. }
        { eapply ptransitive; [ | | | | eapply (@bind_of_return _ _ _ _ MonadLaws_mleq) | ]; eauto with typeclass_instances.
          { eapply bind_proper; eauto with typeclass_instances. }
          { eapply ret_respectful_leq; eauto with typeclass_instances. } } } }
    { exact mret_respectful. }
    { intros; simpl; unfold o_mleq; simpl.
      eapply bind_respectful_leq; eauto with typeclass_instances; intros. 
      destruct a; destruct b; simpl in *; try contradiction. 
      eapply H0; eauto. eapply ret_respectful_leq; eauto with typeclass_instances. }
    { simpl; intros. do 2 red; simpl. 
      eapply ret_proper; eauto with typeclass_instances. }
    { simpl; intros; do 2 red; simpl. 
      eapply bind_proper; eauto with typeclass_instances. }
  Qed.

End Laws.
