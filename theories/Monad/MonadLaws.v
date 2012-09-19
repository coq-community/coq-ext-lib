Require Import Monad.
Require Import Equivalence.

Set Implicit Arguments.
Set Strict Implicit.

Section MonadLaws.
  Variable m : Type -> Type.
  Variable M : Monad m.

  Variable meq : forall T, m T -> m T -> Prop.

  Class MonadLaws : Type :=
  { mequiv : forall a, Equivalence (@meq a)
  ; bind_of_return : forall A B (a:A) (f:A -> m B),
    meq (bind (ret a) f) (f a)
  ; return_of_bind : forall A (aM:m A) (f:A -> m A),
    (forall x, meq (f x) (ret x)) -> meq (bind aM f) aM
  ; bind_associativity :
    forall A B C (aM:m A) (f:A -> m B) (g:B -> m C),
      meq (bind (bind aM f) g) (bind aM (fun a => bind (f a) g))
  ; bind_parametric_hd : forall A B c c' (f : A -> m B),
    meq c c' ->
    meq (bind c f) (bind c' f)
  ; bind_parametric_tl : forall A B (f g : A -> m B),
    (forall a, meq (f a) (g a)) ->
    forall c, meq (bind c f) (bind c g)
  }.

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
  { mfix_monotonic : forall T U (F : (T -> m U) -> T -> m U),
    forall x, leq (mfix F x) (F (mfix F) x)
  (** This probably needs stronger properties that express what F is doing **)
  }.

End MonadLaws.

Hint Rewrite bind_of_return bind_associativity using (eauto with typeclass_instances) : monad_rw.
Hint Rewrite lift_ret lift_bind get_put ask_local local_local bind_zero : monad_rw.

Ltac monad_norm :=
  let tac :=
    repeat (rewrite bind_parametric_hd; [ eassumption | eauto with typeclass_instances | intros ]);
    repeat (rewrite bind_parametric_tl; [ reflexivity | eauto with typeclass_instances | intros ]);
    repeat (rewrite return_of_bind; [ solve [ eauto ] | eauto with typeclass_instances | intros ]);
    try (autorewrite with monad_rw; intros)
  in
  try ( unfold liftM, liftM2 in * ) ;
  repeat progress tac.
