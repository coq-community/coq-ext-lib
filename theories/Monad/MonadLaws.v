Require Import Monad.
Require Import Equivalence.

Set Implicit Arguments.
Set Strict Implicit.

Section MonadLaws.
  Variable m : Type -> Type.
  Variable M : Monad m.

  Variable meq : forall T, m T -> m T -> Prop.

  Class MonadLaws : Prop :=
  { mequiv : forall a, Equivalence (@meq a)
  ; bind_of_return : forall A B (a:A) (f:A -> m B), 
    meq (bind (ret a) f) (f a)
  ; return_of_bind : forall A (aM:m A) (f:A -> m A),
    (forall x, meq (f x) (ret x)) -> meq (bind aM f) aM
  ; bind_associativity : 
    forall A B C (aM:m A) (f:A -> m B) (g:B -> m C), 
      meq (bind (bind aM f) g) (bind aM (fun a => bind (f a) g))
  ; bind_parametric : forall A B (f g : A -> m B),
    (forall a, meq (f a) (g a)) ->
    forall c, meq (bind c f) (bind c g)
  }.

  Class MonadStateLaws s (MS : State s m) : Prop :=
  { get_put : meq (bind get put) (ret tt)
  }.

  Class MonadReaderLaws S (MS : Reader S m) : Prop :=
  { ask_local : forall s, meq (local s ask) (ret s)
  ; local_local : forall T (s s' : S) (c : m T), meq (local s (local s' c)) (local s' c)
  }.

  Class MonadZeroLaws (MZ : Zero m) : Prop :=
  { bind_zero : 
    forall A B c, meq (@bind _ M _ (@zero _ _ A) _ c) (@zero _ _ B)
  }.

End MonadLaws.