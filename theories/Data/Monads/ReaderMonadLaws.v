Require Import RelationClasses.
Require Import Setoid.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Structures.FunctorRelations.
Require Import ExtLib.Structures.MonadLaws.
Require Import ExtLib.Data.Monads.ReaderMonad.

Set Implicit Arguments.
Set Strict Implicit.

Section Laws2.
  Variable m : Type -> Type.
  Variable Monad_m : Monad m.
  Variable mleq : forall T, (T -> T -> Prop) -> m T -> m T -> Prop.
  Variable mproper : forall T (rT : relation T), Proper rT -> Proper (mleq rT).
  Variable FunctorOrder_mleq : FunctorOrder m mleq mproper.
  Variable MonadLaws_mleq : MonadLaws Monad_m mleq mproper.

  Variable S : Type.
  Variable Seq : relation S.
  Variable PS : Proper Seq.
  Variable Refl_Seq : PReflexive Seq.
  Variable Trans_Seq : PTransitive Seq.

  Definition r_mleq T (e : T -> T -> Prop) (a b : readerT S m T) : Prop :=
    forall s1 s2, proper s1 -> proper s2 -> Seq s1 s2 ->
      mleq e (runReaderT a s1) (runReaderT b s2).

  Global Instance Proper_readerT {T : Type} {rT : relation T} {PT : Proper rT} 
    : Proper (r_mleq rT) :=
  { proper := fun r => proper (runReaderT r) }.

  Theorem mproper_red : forall (C : Type) (rC : relation C) (Pc : Proper rC)
    (o : readerT S m C),
    proper o ->
    proper (runReaderT o).
  Proof. clear. intros. apply H. Qed.

  Global Instance FunctorOrder_rmleq : FunctorOrder (readerT S m) r_mleq _.
  Proof.
    constructor.
    { intros. red. destruct x; red; simpl. intros.
      do 2 red in H0. simpl in H0. do 2 red in H0. destruct H0.
      repeat red in H4. eauto. }
    { intros; red; destruct x; destruct y; destruct z; 
      red; simpl in *; try congruence; intros. 
      red in H3. red in H4. simpl in *.
      eapply fun_trans; eauto. do 2 red in H0; simpl in *. red. eapply H0; eauto.
      eapply H1; eauto. eapply H2; eauto.  }
  Qed.

  Instance proper_bind_k : forall s1 : S,
    proper s1 ->
    forall (B : Type) (eB : relation B) (Pb : Proper eB) 
      (A : Type) (f : A -> readerT S m B) (eA : relation A)
      (Pa : Proper eA),
      proper f -> 
      proper (fun v : A => runReaderT (f v) s1).
  Proof.
    intros. split. 
    { intros. eapply H0; auto. }
    { red. intros. eapply H0; auto. }
  Qed.
  Instance proper_bind_k' : forall s1 : S,
    proper s1 ->
    forall (B : Type) (eB : relation B) (Pb : Proper eB) 
      (A : Type) (a : A) (f : A -> readerT S m B) (eA : relation A)
      (Pa : Proper eA) v,
      proper a -> proper v -> proper f -> 
      proper (runReaderT (f v) s1).
  Proof.
    intros. eapply H2; eauto.
  Qed.
  Instance proper_runReaderT : forall s1 : S,
    proper s1 ->
    forall (B : Type) (eB : relation B) (Pb : Proper eB) 
      (A : Type) (aM : readerT S m A) (f : A -> readerT S m B) (eA : relation A)
      (Pa : Proper eA),
      proper s1 -> proper aM -> 
      proper (runReaderT aM s1).
  Proof.
    intros. eapply H1; eauto.
  Qed.
  Instance m_ret_proper : forall (T : Type) (rT : relation T) (P : Proper rT) (x : T),
    PReflexive rT -> proper x -> proper (ret x).
  Proof.
    repeat red; simpl; intros.    
    split.
    { intros; eapply ret_proper; eauto. }
    { red. intros. eapply ret_respectful_leq; eauto. }
  Qed.
  Instance m_bind_proper : forall (A B : Type) (rA : relation A) (rB : relation B) 
    (Pa : Proper rA) (Pb : Proper rB) (c : readerT S m A)
    (f : A -> readerT S m B), PReflexive rA -> PReflexive rB -> PTransitive rB ->
    proper c -> proper f -> proper (bind c f).
  Proof.
    simpl; intros. do 4 red. simpl.
    split; intros.
    { eapply bind_proper; eauto. eapply H2; eauto.
      do 2 red. split.
      { intros. eapply H3; eauto. }
      { red; simpl; intros. eapply H3; eauto. } }
    { red; intros. eapply bind_respectful_leq; eauto.
      eapply H2; eauto.
      intros. eapply H3; eauto. }
  Qed.
  Lemma runReaderT_app_mleq : forall s2 : S,
    proper s2 ->
    forall s1 : S,
      proper s1 ->
      Seq s1 s2 ->
      forall (B : Type) (eB : relation B) (Pb : Proper eB),
        forall (A : Type) (a b : A) (f : A -> readerT S m B) 
          (eA : relation A) (Pa : Proper eA),
          proper a -> proper b -> eA a b ->
          proper f ->              
          mleq eB (runReaderT (f a) s1) (runReaderT (f b) s2).
  Proof.
    intros. destruct H5. repeat red in H6.
    eapply H6; eauto.
  Qed.

  Existing Instance bind_proper. 
  Existing Instance ret_proper.
  Existing Instance fun_trans.
  Existing Instance fun_refl.

  Global Instance MonadLaws_readerT : MonadLaws (@Monad_readerT S _ Monad_m) r_mleq _.
  Proof.
    constructor.
    { (* bind_of_return *)
      red; simpl; intros.
      eapply ptransitive; [ | | | | eapply (@bind_of_return _ _ _ _ MonadLaws_mleq); eauto | ];
      eauto with typeclass_instances.
      eapply runReaderT_app_mleq; eauto. }
    { (* return_of_bind *)
      intros. red; intros.
      simpl. 
      eapply ptransitive; [ | | | | eapply return_of_bind | ]; eauto with typeclass_instances.
      intros. eapply H3; eauto.
      eapply H1; eauto. }
    { (* bind_associativity *)
      red; simpl; intros.      
      eapply ptransitive; [ | | | | eapply (@bind_associativity _ _ _ _ MonadLaws_mleq) | ]; instantiate; eauto with typeclass_instances.
      { eapply bind_proper; eauto with typeclass_instances. }
      { eapply bind_proper; eauto with typeclass_instances.
        split.
        { intros. eapply bind_proper; eauto with typeclass_instances. }
        { red; intros. eapply bind_respectful_leq; eauto. eapply runReaderT_app_mleq; eauto.
          intros. eapply runReaderT_app_mleq; eauto. } }
      { eapply bind_proper; eauto with typeclass_instances. 
        split.
        { intros; eauto with typeclass_instances. }
        { red; intros; eapply bind_respectful_leq; eauto; intros; try eapply runReaderT_app_mleq; eauto. } }
      eapply bind_respectful_leq; eauto with typeclass_instances.
      eapply H4; eauto.
      intros. eapply bind_respectful_leq; eauto with typeclass_instances.
      eapply runReaderT_app_mleq; eauto. intros. eapply runReaderT_app_mleq; eauto. }
    { (* ret_respectful_leq *)
      simpl; intros. red; simpl. intros.
      eapply ret_respectful_leq; eauto. }
    { (* bind_respectful_leq *)
      simpl; intros; red; simpl; intros.
      eapply bind_respectful_leq; eauto.
      intros. red in H0. eauto. }
    { (* ret_proper *)      
      exact m_ret_proper. }
    { (* bind_proper *)
      exact m_bind_proper. }
  Qed.

(*
  Global Instance MonadTLaws_readerT : @MonadTLaws (readerT S m) (@Monad_readerT S m _)
    r_mleq m Monad_m (@MonadT_readerT _ m).
  Proof.
    constructor; intros; simpl; eapply lower_meq; unfold liftM; simpl; monad_norm;
      reflexivity.
  Qed.
*)

End Laws2.
