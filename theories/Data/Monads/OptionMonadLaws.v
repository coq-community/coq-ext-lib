Require Import RelationClasses.
Require Import Setoid.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Structures.FunctorRelations.
Require Import ExtLib.Structures.MonadLaws.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.TypeTac. 

Set Implicit Arguments.
Set Strict Implicit.

Section Laws.
  Variable m : Type -> Type.
  Variable Monad_m : Monad m.
  Variable mtype : forall T, type T -> type (m T).
  Variable mtypeOk : forall T (tT : type T), typeOk tT -> typeOk (mtype tT).
  Variable ML_m : MonadLaws Monad_m mtype.

  Section parametric.
    Variable T : Type.
    Variable tT : type T.

    Definition optionT_eq (a b : optionT m T) : Prop :=
      equal (unOptionT a) (unOptionT b).

    Global Instance type_optionT : type (optionT m T) :=
    { equal := optionT_eq }.

    Variable tokT : typeOk tT.

    Global Instance typeOk_readerT : typeOk type_optionT.
    Proof.
      constructor.
      { simpl. unfold optionT_eq. intros.
        generalize (only_proper _ _ _ H); intros.
        split; do 4 red; intuition. }
      { red. intuition. }
      { red. unfold equal; simpl. unfold optionT_eq; simpl.
        unfold Morphisms.respectful; simpl. symmetry. auto. }
      { red. unfold equal; simpl. unfold optionT_eq; simpl.
        unfold Morphisms.respectful; simpl. intros.
        etransitivity; eauto. }
    Qed.

    Global Instance proper_unOptionT : proper (@unOptionT m T).
    Proof. do 5 red; eauto. Qed.

    Global Instance proper_mkOptionT : proper (@mkOptionT m T).
    Proof. do 5 red; eauto. Qed.
  End parametric.

  Theorem equal_match : forall (A B : Type) (eA : type A) (eB : type B), 
    typeOk eA -> typeOk eB ->
    forall (x y : option A) (a b : B) (f g : A -> B),
      equal x y ->
      equal a b ->
      equal f g ->
      equal match x with
              | Some a => f a
              | None => a
            end
            match y with
              | Some a => g a
              | None => b
            end.
  Proof.
    destruct x; destruct y; intros; eauto with typeclass_instances; type_tac.
    { inversion H1. }
    { inversion H1. }
  Qed.

  Instance proper_match : forall (A B : Type) (eA : type A) (eB : type B), 
    typeOk eA -> typeOk eB ->
    forall (x : option A),
    proper x ->
    forall f : A -> optionT m B,
      proper f ->
      proper match x with
               | Some a => unOptionT (f a)
               | None => ret None
             end.
  Proof.
    destruct x; intros; eauto with typeclass_instances; type_tac.
  Qed.

  Global Instance MonadLaws_optionT : MonadLaws (@Monad_optionT _ Monad_m) type_optionT.
  Proof.
    constructor.
    { (* bind_of_return *)
      intros. do 3 red. unfold bind; simpl.
      rewrite bind_of_return; eauto with typeclass_instances; type_tac.
      eapply equal_match; eauto with typeclass_instances; type_tac. }
    { (* return_of_bind *)
      simpl; unfold optionT_eq; simpl; intros.
      rewrite return_of_bind; eauto with typeclass_instances; intros; type_tac.
      destruct x; type_tac. }
    { (* bind_associativity *)
      simpl; unfold optionT_eq; simpl; intros.
      rewrite bind_associativity; eauto with typeclass_instances; intros; type_tac.
      destruct x; destruct y; try solve [ inversion H5 ]; type_tac.
      eapply equal_match; eauto with typeclass_instances; type_tac.
      rewrite bind_of_return; eauto with typeclass_instances; type_tac.
      eapply equal_match; eauto with typeclass_instances; type_tac.
      eapply equal_match; eauto with typeclass_instances; type_tac.
      eapply equal_match; eauto with typeclass_instances; type_tac. }
    { simpl; unfold optionT_eq; simpl; intros; type_tac. }
    { simpl; unfold optionT_eq; simpl; intros; type_tac. 
      eapply equal_match; eauto with typeclass_instances; type_tac. }
  Qed.

  Global Instance MonadZeroLaws_optionT : MonadZeroLaws (@Monad_optionT _ Monad_m) type_optionT _.
  Proof.
    constructor.
    { simpl; unfold optionT_eq; simpl; intros.
      rewrite bind_of_return; eauto with typeclass_instances; type_tac.
      eapply equal_match; eauto with typeclass_instances; type_tac. }
    { unfold mzero; simpl; intros. red. red. type_tac. }
  Qed.

End Laws.
