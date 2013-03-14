Require Import RelationClasses.
Require Import Setoid.
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
  Variable m : Type -> Type.
  Variable Monad_m : Monad m.
  Variable mleq : forall T, (T -> T -> Prop) -> m T -> m T -> Prop.
  Variable mproper : forall T (rT : relation T), Proper rT -> Proper (mleq rT).
  Variable FunctorOrder_mleq : FunctorOrder m mleq mproper.
  Variable MonadLaws_mleq : MonadLaws Monad_m mleq mproper.

  Section with_T.
    Context {T : Type} (e : relation T) (P : Proper e).

    Definition FixResult_leq (a b : FixResult T) : Prop :=
      match a , b with
        | _ , Diverge => True
        | Term a , Term b => e a b
        | Diverge , Term _ => False
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

    Definition fix_mleq (l r : GFixT m T) : Prop :=
      forall n1 n2 : N,
        BinNat.N.le n1 n2 ->
        mleq FixResult_leq (runGFixT l n1) (runGFixT r n2).

    Instance Proper_N : Proper BinNat.N.le :=
    { proper := fun _ => True }.
    
    Global Instance Proper_fix_mleq : Proper fix_mleq :=
    { proper := fun f => proper (runGFixT f) }.
    
    Global Instance PReflexive_fix_mleq (ReA : PReflexive e) : PReflexive fix_mleq.
    Proof.
      repeat red; intros. destruct H. red in H1. eapply H1; try solve [ apply I ]; auto.
    Qed.

    Global Instance proper_runGFixT : forall x n1,
      proper x ->
      proper (runGFixT x n1).
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
      red; intros. red in H. red in H0. red; intros.
      eapply fun_trans; [ | | | | | eapply H2 | eapply H3 ];
        eauto with typeclass_instances; try reflexivity.
    Qed. 
  End with_T.

  Global Instance FunctorOrder_fmleq : FunctorOrder _ (@fix_mleq) _.
  Proof.
    constructor; eauto with typeclass_instances.
  Qed.

  Existing Instance bind_proper. 
  Existing Instance ret_proper.
  Existing Instance fun_trans.
  Existing Instance fun_refl.

  Instance proper_bind_k : 
    forall (B : Type) (eB : relation B) (Pb : Proper eB) 
      (A : Type) (f : A -> GFixT m B) (eA : relation A)
      (Pa : Proper eA) n,
      proper f -> 
      proper (fun v : A => runGFixT (f v) n).
  Proof.
    intros. split. 
    { intros. eapply H; eauto with typeclass_instances. }
    { red. intros. eapply H; eauto with typeclass_instances. reflexivity. }
  Qed.
  Instance proper_bind_k' : 
    forall (B : Type) (eB : relation B) (Pb : Proper eB) 
      (A : Type) (f : A -> GFixT m B) (eA : relation A)
      (Pa : Proper eA) n, PReflexive eB ->
      proper f -> 
      proper (fun v =>
        match v with
          | Term v => runGFixT (f v) n
          | Diverge => ret Diverge
        end).
  Proof.
    intros. split. 
    { intros. destruct x; eauto with typeclass_instances. }
    { red. intros. destruct a; destruct b; simpl in *; try contradiction.
      eapply H0; eauto with typeclass_instances. reflexivity.
      destruct H0. red in H4. repeat red in H4.
      (** TODO: how do you prove [x <= ret Diverge], you need a requirement
       ** on how [ret] produces only maximal elements of the relation...
       **) admit.
      eapply ret_respectful_leq; eauto with typeclass_instances. }
  Qed.
(*
  Instance m_bind_proper : forall (A B : Type) (rA : relation A) (rB : relation B) 
    (Pa : Proper rA) (Pb : Proper rB) (c : GFixT m A)
    (f : A -> GFixT m B), PReflexive rA -> PReflexive rB -> PTransitive rB ->
    proper c -> proper f -> proper (bind c f).
  Proof.
    simpl; intros. do 4 red. simpl.
    split; intros.
    { eapply bind_proper; eauto with typeclass_instances. }
    { red; intros. eapply bind_respectful_leq; eauto with typeclass_instances.
      eapply H2; eauto.
      intros. eapply H3; eauto. }
  Qed.


  Global Instance MonadLaws_readerT : MonadLaws (@Monad_GFixT _ Monad_m) (@fix_mleq) _.
  Proof.
    constructor; eauto with typeclass_instances.
    { (* bind_of_return *)
      red; simpl; intros. 
      eapply ptransitive; [ | | | | eapply (@bind_of_return _ _ _ _ MonadLaws_mleq); eauto | ];
      eauto with typeclass_instances.
      admit.
      admit.
      eapply H3; eauto with typeclass_instances. }
    { (* return_of_bind *)
      red; simpl; intros.
      eapply ptransitive; [ | | | | eapply (@return_of_bind _ _ _ _ MonadLaws_mleq); eauto | ]; eauto with typeclass_instances.



      intros; simpl. eapply lower_meq; simpl.
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
*)

End Laws.
