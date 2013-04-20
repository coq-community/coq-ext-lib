Require Import RelationClasses.
Require Import Setoid.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.FunctorRelations.
Require Import ExtLib.Structures.MonadLaws.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Data.Monads.FuelMonad.
Require Import BinPos.

Set Implicit Arguments.
Set Strict Implicit.

Section Laws.
  Section with_T.
    Context {T : Type} (e : type T).

    Definition FixResult_eq (a b : FixResult T) : Prop :=
      match a , b with
        | Diverge , Diverge => True
        | Term a , Term b => equal a b
        | _ , _ => False
      end.

    Global Instance type_FixResult : type (FixResult T) :=
    { equal := FixResult_eq }.

    Variable tokE : typeOk e.

    Global Instance typeOk_FixResult : typeOk type_FixResult.
    Proof.
      constructor.
      { unfold proper; simpl.
        destruct x; destruct y; simpl; intros; auto; try contradiction.
        apply only_proper; auto. }
      { red; destruct x; compute; auto. }
      { red. destruct x; destruct y; simpl; auto; simpl. symmetry; auto. }
      { red. destruct x; destruct y; destruct z; simpl; intros; auto; try contradiction.
        etransitivity; eauto. }
    Qed.

    Require Import ExtLib.Data.N.
    
    Definition fix_meq (l r : GFix T) : Prop :=
      equal (runGFix l) (runGFix r).

    Global Instance type_GFix : type (GFix T) :=
    { equal := fix_meq }.
    
    Global Instance typeOk_GFix : typeOk type_GFix.
    Proof.
      constructor.
      { destruct x; destruct y; simpl. 
        intros; split; intros. 
        { red; simpl.
          red in H; red. simpl FuelMonad.runGFix in *.
          eapply only_proper in H; eauto with typeclass_instances.
          eapply preflexive; eauto with typeclass_instances; intuition. }
        { red; simpl.
          red in H; red; simpl FuelMonad.runGFix in *.
          eapply only_proper in H; eauto with typeclass_instances.
          eapply preflexive; eauto with typeclass_instances; intuition. } }
      { red. eauto. }
      { red. destruct x; destruct y; simpl; unfold fix_meq.
        simpl FuelMonad.runGFix in *. intros.
        symmetry; auto. }
      { red; destruct x; destruct y; destruct z; simpl; unfold fix_meq;
        simpl FuelMonad.runGFix in *. intros.
        etransitivity; eauto. }
    Qed.      
    
    Global Instance proper_runGFix : proper (@runGFix T).
    Proof.
      repeat red; simpl; intros. eapply H. subst. reflexivity.
    Qed.

    Global Instance proper_mkGFix : proper (@mkGFix T).
    Proof.
      repeat red; simpl; intros. eapply H. subst. reflexivity.
    Qed.
  End with_T.

  Require Import ExtLib.Tactics.TypeTac.

  Global Instance MonadLaws_GFix : MonadLaws Monad_GFix (@type_GFix).
  Proof.
    constructor.
    { (* bind_of_return *)
      red; simpl; intros. red. simpl runGFix. type_tac. }
    { (* return_of_bind *)
      red; simpl; intros. red. simpl runGFix. type_tac.
      assert (equal (runGFix aM x) (runGFix aM y)) by type_tac.
      destruct (runGFix aM x); destruct (runGFix aM y); simpl in *; try contradiction; auto.
      specialize (H0 a x y H2). 
      red. destruct (runGFix (f a) x); simpl in *; auto. etransitivity; eauto. }
    { (* bind associativity *)
      red; simpl; intros.
      red; simpl runGFix. type_tac.
      assert (equal (runGFix aM x) (runGFix aM y)) by type_tac.
      destruct (runGFix aM x); destruct (runGFix aM y); simpl in H6; try contradiction; auto.
      assert (equal (runGFix (f a) x) (runGFix (f a0) y)) by type_tac.
      destruct (runGFix (f a) x); destruct (runGFix (f a0) y); simpl in H7; try contradiction; type_tac. }
    { unfold ret; simpl. intros; type_tac. }
    { unfold bind; simpl; intros; type_tac.
      assert (equal (runGFix x x1) (runGFix y y1)) by type_tac.
      destruct (runGFix x x1); destruct (runGFix y y1); simpl in H4; try contradiction; type_tac. }
  Qed.

(*
  Theorem Diverge_minimal : forall C (eC : relation C) x,
    FixResult_leq eC Diverge x.
  Proof.
    destruct x; compute; auto.
  Qed.

  Theorem Term_maximal : forall C (eC : relation C) x y,
    FixResult_leq eC (Term x) y ->
    exists z, y = Term z /\ eC x z.
  Proof.
    destruct y; simpl; intros; try contradiction; eauto.
  Qed.
  Lemma leq_app : forall B C (eB : relation B) (eC : relation C) (pB : Proper eB) (pC : Proper eC) g (b b' : B) n n',
    proper g -> proper b -> proper b' ->
    eB b b' ->
    BinNat.N.le n n' ->
    FixResult_leq eC (runGFix (g b) n) (runGFix (g b') n').
  Proof.
    intros. destruct H. specialize (H4 _ _ H0 H1 H2 _ _ H3). auto.
  Qed.
*)

End Laws.
