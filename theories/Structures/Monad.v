Require Import Functor.
Require Import Applicative.
Require Import ExtLib.Structures.Monoid.

Set Implicit Arguments.
Set Strict Implicit.

Class Monad (m : Type -> Type) : Type :=
{ ret : forall {t}, t -> m t
; bind : forall {t}, m t -> forall {u}, (t -> m u) -> m u
}.

Section monadic.
  Variable m : Type -> Type.
  Context {M : Monad m}.
  
  Definition liftM T U (f : T -> U) : m T -> m U :=
    fun x => bind x (fun x => ret (f x)).

  Definition liftM2 T U V (f : T -> U -> V) : m T -> m U -> m V :=
    fun x y => bind x (fun x => bind y (fun y => ret (f x y))).

  Definition apM {A B} (fM:m (A -> B)) (aM:m A) : m B := bind fM (fun f => liftM f aM).
End monadic.

Module MonadNotation.

  Delimit Scope monad_scope with monad.

  Notation "c >>= f" := (@bind _ _ _ c _ f) (at level 50, left associativity) : monad_scope.
  Notation "f =<< c" := (@bind _ _ _ c _ f) (at level 51, right associativity) : monad_scope.

  (** DEPRECATED **)
  Notation "x <- c1 ; c2" := (@bind _ _ _ c1 _ (fun x => c2))
    (at level 100, c1 at next level, right associativity, only parsing) : monad_scope.

  Notation "x <- c1 ;; c2" := (@bind _ _ _ c1 _ (fun x => c2))
    (at level 100, c1 at next level, right associativity) : monad_scope.

  Notation "e1 ;; e2" := (_ <- e1%monad ;; e2%monad)%monad
    (at level 100, right associativity) : monad_scope.

End MonadNotation.

Instance MonadFunctor {m} {mMonad:Monad m} : Functor m :=
{ fmap := @liftM _ _ }.

Instance MonadApplicative {m} {M:Monad m} : Applicative m :=
{ pure := @ret _ _
; ap := @apM _ _
}.
