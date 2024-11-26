Require Import Setoid.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Unit.

Set Implicit Arguments.
Set Strict Implicit.

Section MonadLaws.
  Variable m : Type -> Type.
  Variable M : Monad m.

  (** This <= relation is a computational <= relation based on the ideas
      of domain theory. It generalizes the usual equivalence relation by,
      enabling the relation to talk about computations that are "more defined"
      than others.
   
      This generalization is done to support the fixpoint law.
   **)

  Class MonadLaws :=
  { bind_of_return : forall {A B} (a : A) (f : A -> m B),
      bind (ret a) f = f a
  ; return_of_bind : forall {A} (aM: m A),
      bind aM ret = aM
  ; bind_associativity :
      forall {A B C} (aM:m A) (f:A -> m B) (g:B -> m C),
        bind (bind aM f) g = bind aM (fun a => bind (f a) g)
  }.

  Class MonadTLaws {n} (nM : Monad n) (MT : MonadT m n) :=
  { lift_ret  : forall {T} (x : T),
      lift (ret x) = ret x
  ; lift_bind : forall {T U} (c : n T) (f : T -> n U),
      lift (bind c f) = bind (lift c) (fun x => lift (f x))
  }.

  Section with_state.
    Context {S : Type}.

    Class MonadStateLaws  (MS : MonadState S m) :=
    { get_put : bind get put = ret tt :> m unit
    ; put_get : forall x : S,
        bind (put x) (fun _ => get) = bind (put x) (fun _ => ret x) :> m S
    ; put_put : forall {A} (x y : S) (f : unit -> m A),
        bind (put x) (fun _ => bind (put y) f) = bind (put y) f
    ; get_get : forall {A} (f : S -> S -> m A),
        bind get (fun s => bind get (f s)) = bind get (fun s => f s s)
    ; get_ignore : forall {A} (aM : m A),
        bind get (fun _ => aM) = aM
    }.

    Class MonadReaderLaws (MR : MonadReader S m) :=
    { ask_local : forall f : S -> S,
        local f ask = bind ask (fun x => ret (f x))
    ; local_bind : forall {A B} (aM : m A) (f : S -> S) (g : A -> m B),
          local f (bind aM g) = bind (local f aM) (fun x => local f (g x))
    ; local_ret : forall {A} (x : A) (f : S -> S),
        local f (ret x) = ret x
    ; local_local : forall {T} (s s' : S -> S) (c : m T),
        local s (local s' c) = local (fun x => s' (s x)) c
    }.

  End with_state.

  Class MonadZeroLaws (MZ : MonadZero m) :=
  { bind_zero : forall {A B} (f : A -> m B),
      bind mzero f = mzero
  }.

  Class MonadFixLaws (MF : MonadFix m) : Type :=
  { mleq : forall {T}, relation T -> relation (m T)
  ; mfix_monotonic : forall {T U} (F : (T -> m U) -> T -> m U),
    respectful eq (mleq eq) (mfix F) (F (mfix F))
  }.

End MonadLaws.
