Require Import RelationClasses.
Require Import Setoid.
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
    Context {T : Type} (e : relation T) (P : Proper e).

    Definition FixResult_leq (a b : FixResult T) : Prop :=
      match a , b with
        | Diverge , _ => True
        | Term a , Term b => e a b
        | Term _ , Diverge => False
      end.

    Global Instance Proper_FixResult : Proper FixResult_leq :=
    { proper := fun f =>
      match f with
        | Term e => proper e
        | Diverge => True
      end }.

    Global Instance PReflexive_FixResult_leq (PT : PReflexive e): PReflexive FixResult_leq.
    Proof.
      red; destruct x; simpl in *; intros; try contradiction; eauto.
    Qed.

    Global Instance PTransitive_FixResult_leq (PT : PTransitive e): PTransitive FixResult_leq.
    Proof.
      red; destruct x; destruct y; destruct z; simpl in *; intros; try contradiction; eauto.
    Qed.

    Definition fix_mleq (l r : GFix T) : Prop :=
      forall n1 n2 : N,
        BinNat.N.le n1 n2 ->
        FixResult_leq (runGFix l n1) (runGFix r n2).

    Instance Proper_N : Proper BinNat.N.le :=
    { proper := fun _ => True }.
    
    Global Instance Proper_fix_mleq : Proper fix_mleq :=
    { proper := fun f => proper (runGFix f) }.
    
    Global Instance PReflexive_fix_mleq (ReA : PReflexive e) : PReflexive fix_mleq.
    Proof.
      repeat red; intros. destruct H. red in H1. eapply H1; try solve [ apply I ]; auto.
    Qed.

    Global Instance proper_runGFixT : forall x n1,
      proper x ->
      proper (runGFix x n1).
    Proof.
      repeat red; simpl; intros. eapply H. exact I. 
    Qed.
    Global Instance N_proper : forall (n : N), proper n := fun _ => I.

    Global Instance PReflexive_fix_leq (ReA : PReflexive e) : PReflexive fix_mleq.
    Proof.
      repeat red; intros. eapply H; eauto with typeclass_instances.
    Qed. 

    Global Instance PTransitive_fix_leq (ReA : PTransitive e) : PTransitive fix_mleq.
    Proof.
      red; intros. destruct H; destruct H0; destruct H1.
      red; intros. specialize (H n1 I). specialize (H0 n2 I). specialize (H1 n2 I).
      specialize (H2 _ _ H7). specialize (H3 n2 n2).
      unfold FixResult_leq in *.
      destruct (runGFix x n1); destruct (runGFix y n2); destruct (runGFix z n2); try contradiction; auto.
      eapply ptransitive; [ | | | | eassumption | ]; eauto. eapply H3; reflexivity.
      exfalso. apply H3; reflexivity. 
    Qed.
  End with_T.

  Global Instance FunctorOrder_fmleq : FunctorOrder _ (@fix_mleq) _.
  Proof.
    constructor; eauto with typeclass_instances.
  Qed.

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

  Global Instance MonadLaws_GFix : MonadLaws Monad_GFix (@fix_mleq) _.
  Proof.
    constructor; eauto with typeclass_instances.
    { (* bind_of_return *)
      red; simpl; intros.
      eapply leq_app; eauto. }
    { (* return_of_bind *)
      red; simpl; intros.
      red.
      destruct H1.
      specialize (H5 _ _ I I H4).
      generalize (H1 n1 I). specialize (H1 n2 I); intros. 
      red in H5. destruct (runGFix aM n1); destruct (runGFix aM n2); auto.
      specialize (H3 a _ _ H4). simpl in *.
      red in H3. revert H3. 
      assert (proper (runGFix (f a) n1)).
      eapply H2; eauto. exact I.
      revert H3. destruct (runGFix (f a) n1); eauto.
      destruct (runGFix (f a) n1); auto. }
    { (* bind associativity *)
      red; simpl; intros.
      assert (forall n, proper (runGFix aM n)). intros; eapply H4; apply I.
      generalize (H8 n2). specialize (H8 n1). intro.
      assert (FixResult_leq eA (runGFix aM n1) (runGFix aM n2)).
      { destruct H4. eapply H10; eauto with typeclass_instances. }        
      generalize dependent (runGFix aM n1).
      generalize dependent (runGFix aM n2).
      destruct f0; destruct f0; simpl in *; intros; try contradiction; auto.
      consider (runGFix (f a0) n1); intros; try eapply Diverge_minimal.
      { destruct H5.
        specialize (H12 _ _ H8 H9 H10 _ _ H7).
        rewrite H11 in H12.
        eapply Term_maximal in H12. destruct H12.
        destruct H12. rewrite H12 in *.
        eapply leq_app; eauto.
        specialize (H5 _ H8). destruct H5. specialize (H5 n1 I). rewrite H11 in *; auto.
        specialize (H5 _ H9). destruct H5. specialize (H5 n2 I). rewrite H12 in *; auto.
      } }
    { intros; unfold fix_mleq in *; simpl in *; eauto. }
    { intros; unfold fix_mleq in *; simpl in *; intros.
      specialize (H _ _ H3). consider (runGFix c n1); intros; try eapply Diverge_minimal.
      eapply Term_maximal in H4. destruct H4; intuition.
      rewrite H5. eapply H0; eauto with typeclass_instances.
      destruct H1. specialize (H1 n1 I). rewrite H in *; auto.
      destruct H2. specialize (H2 n2 I). rewrite H5 in *; auto. }
    { simpl; intros. repeat red; simpl. split. eauto.
      red. simpl. intros. eapply preflexive; eauto. }
    { simpl; intros; repeat red; simpl. intuition.
      { destruct H2. specialize (H2 _ H4). destruct (runGFix c x). eapply H3; eauto.
        exact I. }
      { red; intros. destruct H2. specialize (H7 _ _ H4 H5 H6).
        consider (runGFix c a); intros; try eapply Diverge_minimal.
        red in H8. consider (runGFix c b); intros; try contradiction.
        eapply leq_app; eauto. specialize (H2 _ H4); rewrite H7 in *; auto.
        specialize (H2 _ H5); rewrite H8 in *; auto. } }
  Qed.

End Laws.
