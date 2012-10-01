Require Import Monad.

Set Implicit Arguments.
Set Strict Implicit.

Import MonadNotation.
Open Local Scope monad_scope.

Global Instance Monad_option : Monad option :=
{ ret  := @Some
; bind := fun _ c1 _ c2 => match c1 with
                             | None => None
                             | Some v => c2 v
                           end
}.

Global Instance Zero_option : Zero option :=
{ zero := @None }.

Global Instance Plus_option : MonadPlus option :=
{ mplus _A _B aM bM :=
    match aM with
    | None => liftM inr bM
    | Some a => Some (inl a)
    end
}.

Section Trans.
  Variable m : Type -> Type.

  Inductive optionT a := mkOptionT { unOptionT : m (option a) }.

  Context {M : Monad m}.

  Global Instance Monad_optionT : Monad optionT :=
  { ret _A := fun x => mkOptionT (ret (Some x))
  ; bind _A aMM _B f := mkOptionT
      (aM <- unOptionT aMM ;;
       match aM with
       | None => ret None
       | Some a => unOptionT (f a)
       end)
  }.

  Global Instance Zero_optionT : Zero optionT :=
  { zero _A := mkOptionT (ret None) }.

  Global Instance MonadT_optionT : MonadT optionT m :=
  { lift _A aM := mkOptionT (liftM ret aM) }.

  Global Instance State_optionT {T} (SM : State T m) : State T optionT :=
  { get := lift get
  ; put v := lift (put v)
  }.

  Global Instance Reader_optionT {T} (SM : Reader T m) : Reader T optionT :=
  { ask := lift ask
  ; local v _T cmd := mkOptionT (local v (unOptionT cmd))
  }.

  Instance OptionTError {mMonad:Monad m} : MonadExc unit optionT :=
  { raise _u _A := zero
  ; catch _A aMM f := mkOptionT
      (aM <- unOptionT aMM ;;
       match aM with
       | None => unOptionT (f tt)
       | Some x => ret (Some x)
       end)
  }.

  Section Laws.
    Require Import RelationClasses.
    Require Import MonadLaws.
    Require Import Setoid.

    Variable meq : forall T, m T -> m T -> Prop.
    Variable MonadLaws_m : MonadLaws M meq.

    Definition o_meq T (a b : optionT T) : Prop :=
      meq (unOptionT a) (unOptionT b).

    Global Instance Equivalence_o_meq T : Equivalence (@o_meq T).
    Proof.
      constructor; red; unfold o_meq; destruct MonadLaws_m.
      { intros. eapply mequiv. }
      { intros. symmetry. auto. }
      { intros. etransitivity; eauto. }
    Qed.

    Global Instance MonadLaws_OptionT : MonadLaws Monad_optionT o_meq.
    Proof.
      constructor; eauto with typeclass_instances;
        unfold o_meq; destruct MonadLaws_m; simpl; intros; monad_norm;
          try reflexivity; auto.
      { eapply return_of_bind. destruct x; auto; reflexivity. }
      { destruct a; auto; try reflexivity.
        monad_norm. reflexivity. }
      { destruct a; auto; try reflexivity. }
    Qed.

    Global Instance MonadTLaws_optionT : MonadTLaws Monad_optionT o_meq M MonadT_optionT.
    Proof.
      constructor; intros; simpl in *; destruct MonadLaws_m; unfold o_meq, liftM.
      { simpl; monad_norm; simpl; reflexivity. }
      { simpl. autorewrite with monad_rw.
        apply bind_parametric_tl; intros. autorewrite with monad_rw.
        reflexivity. }
    Qed.

    Global Instance MonadZeroLaws_OptionT : MonadZeroLaws Monad_optionT o_meq Zero_optionT.
    Proof.
      constructor; intros; unfold o_meq; monad_norm; simpl.
      destruct MonadLaws_m. monad_norm. reflexivity.
    Qed.
  End Laws.

End Trans.
