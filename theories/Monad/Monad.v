Require Import Functor.

Set Implicit Arguments.
Set Strict Implicit.

Class Monad (m : Type -> Type) : Type :=
{ ret : forall {t}, t -> m t
; bind : forall {t}, m t -> forall {u}, (t -> m u) -> m u
}.

Class MonadT (m : Type -> Type) (mt : Type -> Type) : Type :=
{ lift : forall {t}, mt t -> m t }.

Definition liftM m {M : Monad m} T U (f : T -> U) : m T -> m U :=
  fun x => bind x (fun x => ret (f x)).

Definition liftM2 m {M : Monad m} T U V (f : T -> U -> V) : m T -> m U -> m V :=
  fun x y => bind x (fun x => bind y (fun y => ret (f x y))).

Module MonadNotation.

  Delimit Scope monad_scope with monad.

  Notation "c >>= f" := (@bind _ _ _ c _ f) (at level 51, right associativity) : monad_scope.
  Notation "f =<< c" := (@bind _ _ _ c _ f) (at level 50, left associativity) : monad_scope.

  Notation "x <- c1 ;; c2" := (@bind _ _ _ c1 _ (fun x => c2))
    (at level 100, c1 at next level, right associativity) : monad_scope.

  (** DEPRECATED **)
  Notation "x <- c1 ; c2" := (@bind _ _ _ c1 _ (fun x => c2))
    (at level 100, c1 at next level, right associativity) : monad_scope.

  Notation "e1 ;; e2" := (_ <- e1%monad ;; e2%monad)%monad
    (at level 100, right associativity) : monad_scope.

End MonadNotation.

Class Reader (T : Type) (m : Type -> Type) : Type :=
{ local : (T -> T) -> forall {t}, m t -> m t
; ask : m T
}.

Class State (T : Type) (m : Type -> Type) : Type :=
{ get : m T
; put : T -> m unit
}.

Class Cont (m : Type -> Type) : Type :=
{ callCC : forall a b, ((a -> m b) -> m a) -> m a }.

Class Zero (m : Type -> Type) : Type :=
{ zero : forall {T}, m T }.

Class MonadFix (m : Type -> Type) : Type :=
{ mfix : forall {T U}, ((T -> m U) -> T -> m U) -> T -> m U }.

Class MonadExc E (m : Type -> Type) : Type :=
{ raise : E -> forall {T}, m T
; catch : forall {T}, m T -> (E -> m T) -> m T
}.

Instance MonadFunctor {m} {mMonad:Monad m} : Functor m := { fmap := @liftM _ _ }.
