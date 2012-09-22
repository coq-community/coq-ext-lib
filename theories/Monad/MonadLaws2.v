Require Import Monad.
Require Import Equivalence.

Set Implicit Arguments.
Set Strict Implicit.

Section MonadLaws.
  Variable m : Type -> Type.
  Variable M : Monad m.

  Variable mleq : forall {T}, (T -> T -> Prop) -> m T -> m T -> Prop.

  Class MonadOrder : Type :=
  { me_refl : forall T (e : T -> T -> Prop), 
    Reflexive e -> Reflexive (mleq e)
  ; me_trans : forall T (e : T -> T -> Prop), 
    Transitive e -> Transitive (mleq e)
  }.

  Definition meq {T} (leq : T -> T -> Prop) (a b : m T) :  Prop :=
    mleq leq a b /\ mleq leq b a.

  Global Instance Reflexive_meq {T} (leq : T -> T -> Prop) {_ : Reflexive leq}
    (_ : MonadOrder) : Reflexive (meq leq).
  Proof.
    split; eapply me_refl; eauto.
  Qed.

  Global Instance Symmetric_meq {T} (leq : T -> T -> Prop)
    (_ : MonadOrder) : Symmetric (meq leq).
  Proof.
    unfold meq; split; intuition; intuition.
  Qed.

  Global Instance Transitive_meq {T} (leq : T -> T -> Prop) {_ : Transitive leq}
    (_ : MonadOrder) : Transitive (meq leq).
  Proof.
    split; unfold meq in *; intuition; eapply me_trans; try eassumption.
  Qed.
    
  Class MonadLaws : Type :=
  { morder :> MonadOrder 
  ; bind_of_return : forall A B (a:A) (f:A -> m B) (eB : B -> B -> Prop),
    meq eB (bind (ret a) f) (f a)
  ; return_of_bind : forall A (aM:m A) (f:A -> m A) (eA : A -> A -> Prop),
    Reflexive eA ->
    (forall x, meq eA (f x) (ret x)) -> meq eA (bind aM f) aM
  ; bind_associativity : 
    forall A B C (aM:m A) (f:A -> m B) (g:B -> m C) (eC : C -> C -> Prop),
      Reflexive eC -> Transitive eC ->
      meq eC (bind (bind aM f) g) (bind aM (fun a => bind (f a) g))

  ; bind_parametric_hd_leq : forall A B c c' (f : A -> m B) (eA : A -> A -> Prop) (eB : B -> B -> Prop),
    mleq eA c c' ->
    mleq eB (bind c f) (bind c' f)
  ; bind_parametric_tl_leq : forall A B (f g : A -> m B) (eB : B -> B -> Prop),
    Reflexive eB ->
    (forall a, mleq eB (f a) (g a)) ->
    forall c, mleq eB (bind c f) (bind c g)

  }.

  Theorem bind_parametric_hd (ml : MonadLaws) : forall A B c c' (f : A -> m B)
    (eA : A -> A -> Prop) (eB : B -> B -> Prop),
    meq eA c c' ->
    meq eB (bind c f) (bind c' f).
  Proof.
    intros; intuition. destruct H; split; eapply bind_parametric_hd_leq; eauto.
  Qed.

  Theorem bind_parametric_tl (ml : MonadLaws) : forall A B (f g : A -> m B) (eB : B -> B -> Prop),
    Reflexive eB ->
    (forall a, meq eB (f a) (g a)) ->
    forall c, meq eB (bind c f) (bind c g).
  Proof.
    intros; intuition. split; eapply bind_parametric_tl_leq; eauto; intros; edestruct H0; eauto.
  Qed.

(*
  Class MonadTLaws (n : Type -> Type) (nM : Monad n) (MT : MonadT m n) : Type :=
  { lift_ret  : forall T (x : T), meq (lift (ret x)) (ret x)
  ; lift_bind : forall T U (c : n T) (f : T -> n U), meq (lift (bind c f)) (bind (lift c) (fun x => lift (f x)))
  }.

  Class MonadStateLaws s (MS : State s m) : Type :=
  { get_put : meq (bind get put) (ret tt)
  }.

  Class MonadReaderLaws S (MS : Reader S m) : Type :=
  { ask_local : forall f, meq (local f ask) (bind ask (fun x => ret (f x)))
  ; local_local : forall T (s s' : S -> S) (c : m T), 
    meq (local s (local s' c)) (local (fun x => s' (s x)) c)
  }.

  Class MonadZeroLaws (MZ : Zero m) : Type :=
  { bind_zero : 
    forall A B c, meq (@bind _ M _ (@zero _ _ A) _ c) (@zero _ _ B)
  }.

  Class MonadFixLaws (MF : MonadFix m) (leq : forall {T}, m T -> m T -> Prop) 
    : Type :=
  { leq_refl : forall T, Reflexive (@leq T)
  ; leq_trans : forall T, Transitive (@leq T)
  ; mfix_monotonic : forall T U (F : (T -> m U) -> T -> m U),
    forall x, leq (mfix F x) (F (mfix F) x)
  }.
*)

End MonadLaws.

(*
Hint Rewrite bind_of_return bind_associativity using (eauto with typeclass_instances) : monad_rw.
(* Hint Rewrite lift_ret lift_bind get_put ask_local local_local bind_zero : monad_rw. *)

Ltac monad_norm :=
  let tac := 
    repeat (rewrite bind_parametric_hd; [ eassumption | eauto with typeclass_instances | intros ]); 
    repeat (rewrite bind_parametric_tl; [ reflexivity | eauto with typeclass_instances | intros ]); 
    repeat (rewrite return_of_bind; [ solve [ eauto ] | eauto with typeclass_instances | intros ]); 
    try (autorewrite with monad_rw; intros)
  in
  try ( unfold liftM, liftM2 in * ) ;
  repeat progress tac.
*)