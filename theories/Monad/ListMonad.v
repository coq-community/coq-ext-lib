Require Import Monad.
Require Import List.

Set Implicit Arguments.
Set Strict Implicit.

Global Instance Monad_list : Monad list :=
{ ret := fun _ v => v :: nil
; bind := fix recur _ c1 _ c2 :=
  match c1 with
    | nil => nil
    | a :: b => c2 a ++ recur _ b _ c2
  end
}.

Global Instance Zero_list : Zero list :=
{ zero := @nil }.

(* List does not have a monad transformer!
Section trans.
  Variable m : Type -> Type.

  Inductive listT (T : Type) : Type :=
  | mkListT : m (option (T * listT T)) -> listT T.

  Definition listT : Type -> Type :=
    fun x => m (list x).

  Context {M : Monad m}.

  Fixpoint flat_map T U (c2 : T -> m (list U)) (vs : list T) : m (list U) :=
    match vs with
      | nil => ret nil
      | v :: vs => liftM2 (@app _) (c2 v) (flat_map c2 vs)
    end.

  Global Instance Monad_listT : Monad listT :=
  { ret := fun _ x => @ret m M _ (x :: nil)
  ; bind := fun _ c1 _ c2 =>
    @bind _ M _ c1 _ (flat_map c2)
  }.

  Global Instance MonadT_listT : MonadT listT m :=
  { lift := fun _ cmd => bind cmd (fun x => ret (x :: nil)) }.

  Global Instance Zero_listT : Zero listT :=
  { zero := fun _ => @ret _ M _ nil }.

  Global Instance State_listT {T} (SM : State T m) : State T listT :=
  { get := lift get
  ; put := fun v => lift (put v)
  }.

  Global Instance Reader_listT {T} (RM : Reader T m) : Reader T listT :=
  { ask   := lift ask
  ; local := fun v _ cmd => local (Reader := RM) v cmd
  }.

  Section Laws.
    Require Import RelationClasses.
    Require Import MonadLaws.
    Require Import Setoid.

    Variable meq : forall T, m T -> m T -> Prop.
    Variable MonadLaws_m : MonadLaws M meq.

    Definition o_meq T (a b : listT T) : Prop :=
      meq a b.

    Global Instance Equivalence_o_meq T : Equivalence (@o_meq T).
    Proof.
      constructor; red; unfold o_meq; destruct MonadLaws_m.
      { intros. eapply mequiv. }
      { intros. symmetry. auto. }
      { intros. etransitivity; eauto. }
    Qed.

    Theorem flat_map_app : forall T U (c : T -> m (list U)) vs vs',
      meq (flat_map c (vs ++ vs'))
          (bind (flat_map c vs) (fun x =>
            (bind (flat_map c vs') (fun y =>
              ret (x ++ y))))).
    Proof.
      induction vs; intros; simpl; monad_norm; simpl.
      { symmetry. eapply return_of_bind. auto. reflexivity. }
      { rewrite bind_parametric_hd. 3: eapply IHvs. 2: eauto.
        monad_norm. rewrite app_ass. reflexivity. }
    Qed.

    Global Instance MonadLaws_OptionT : MonadLaws Monad_listT o_meq.
    Proof.
      constructor; eauto with typeclass_instances;
        unfold o_meq; destruct MonadLaws_m; simpl; intros; monad_norm.
      { monad_norm.
        apply return_of_bind; intros. rewrite bind_of_return. rewrite List.app_nil_r. reflexivity. }
      { apply return_of_bind. intros. induction x; simpl; auto; try reflexivity.
        unfold liftM2. specialize (H a). rewrite bind_parametric_hd. 2: eapply H.
        monad_norm. simpl. rewrite bind_parametric_hd. 2: eapply IHx.
        monad_norm. reflexivity. }
      { induction a.
        { simpl. monad_norm. reflexivity. }
        { simpl. unfold liftM2; simpl.
          symmetry. etransitivity.
          eapply bind_parametric_tl.
          intros. eapply bind_parametric_hd. symmetry. eapply IHa.
          monad_norm.

monad_norm.


 change (a :: a0) with ((a :: nil) ++ a0).
          etransitivity. eapply bind_parametric_hd. eapply flat_map_app.
          simpl; unfold liftM2; simpl.
          repeat rewrite bind_associativity.
          eapply bind_parametric_tl. intro.
          repeat rewrite bind_associativity. monad_norm.

 monad_norm. etransitivity.
          instantiate (1 := bind (flat_map f a0) (fun x => bind (flat_map g a1) (fun y => bind (flat_map g x) (fun z => ret (y ++ z))))).
          eapply bind_parametric_tl.
          intro. rewrite bind_of_return. eapply flat_map_app.
          etransitivity. instantiate (1 :=
          eapply bind_parametric_tl. intro. inst










generalize dependent a0. clear a.
          induction a1. simpl.
          { intros. etransitivity. eapply bind_parametric_tl. intros.
            rewrite bind_of_return. reflexivity.
            monad_norm. reflexivity. }
          { intros.
            etransitivity. eapply bind_parametric_tl.
            intro. rewrite bind_of_return. simpl.
            instantiate (1 := fun a2 => (bind (g a)
        (fun x : list C =>
         bind
           ((fix recur (vs : list B) : m (list C) :=
               match vs with
               | nil => ret nil
               | v :: vs0 =>
                   bind (g v)
                     (fun x0 : list C =>
                      bind (recur vs0) (fun y : list C => ret (x0 ++ y)))
               end) (a1 ++ a2)) (fun y : list C => ret (x ++ y))))).



 match goal with
        | [ |- meq (bind _ ?X) _ ] => remember X as Y;
          assert (forall x, meq (Y x) (X x))
        end.
        { subst. reflexivity. }
        clear HeqY. generalize dependent Y.
        induction a; monad_norm.
        { etransitivity. eapply H. reflexivity. }
        { etransitivity. eapply bind_parametric_hd. eapply IHa.




induction a; monad_norm. reflexivity.



destruct x; auto; reflexivity. }
      { destruct a; auto; try reflexivity.
        monad_norm. reflexivity. }
      { destruct a; auto; try reflexivity. }
    Qed.

    Global Instance MonadTLaws_listT : MonadTLaws Monad_listT o_meq M MonadT_listT.
    Proof.
      constructor; intros; simpl in *; destruct MonadLaws_m; unfold o_meq, liftM.
      { simpl; monad_norm; simpl; reflexivity. }
      { simpl. autorewrite with monad_rw.
        apply bind_parametric; intros. autorewrite with monad_rw.
        reflexivity. }
    Qed.

    Global Instance MonadZeroLaws_OptionT : MonadZeroLaws Monad_listT o_meq Zero_listT.
    Proof.
      constructor; intros; unfold o_meq; monad_norm; simpl.
      destruct MonadLaws_m. monad_norm. reflexivity.
    Qed.
  End Laws.


End trans.
*)