Require Import Functor.
Require Import Applicative.

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

Definition apM m {M:Monad m} {A B} (fM:m (A -> B)) (aM:m A) : m B := bind fM (fun f => liftM f aM).

Module MonadNotation.

  Delimit Scope monad_scope with monad.

  Notation "c >>= f" := (@bind _ _ _ c _ f) (at level 50, left associativity) : monad_scope.
  Notation "f =<< c" := (@bind _ _ _ c _ f) (at level 51, right associativity) : monad_scope.

  (** DEPRECATED **)
  Notation "x <- c1 ; c2" := (@bind _ _ _ c1 _ (fun x => c2))
    (at level 100, c1 at next level, right associativity) : monad_scope.

  Notation "x <- c1 ;; c2" := (@bind _ _ _ c1 _ (fun x => c2))
    (at level 100, c1 at next level, right associativity) : monad_scope.

  Notation "e1 ;; e2" := (_ <- e1%monad ;; e2%monad)%monad
    (at level 100, right associativity) : monad_scope.

End MonadNotation.

Class Reader (T : Type) (m : Type -> Type) : Type :=
{ local : (T -> T) -> forall {t}, m t -> m t
; ask : m T
}.

Class Writer (T : Type) (m : Type -> Type) : Type :=
{ tell : T -> m unit
; listen : forall {A}, m A -> m (A * T)%type
; pass : forall {A}, m (A * (T -> T))%type -> m A
}.

Class State (T : Type) (m : Type -> Type) : Type :=
{ get : m T
; put : T -> m unit
}.

Class Cont (m : Type -> Type) : Type :=
{ callCC : forall a b, ((a -> m b) -> m a) -> m a }.

Class Zero (m : Type -> Type) : Type :=
{ zero : forall {T}, m T }.

Section MonadFix.
  Variable m : Type -> Type.

  Class MonadFix : Type :=
  { mfix : forall {T U}, ((T -> m U) -> T -> m U) -> T -> m U }.

  Fixpoint ftype (ls : list Type) (r : Type) : Type :=
    match ls with
      | nil => r
      | cons l ls => l -> ftype ls r
    end.

  Fixpoint tuple (ls : list Type) : Type :=
    match ls with
      | nil => unit
      | cons l ls => l * tuple ls
    end%type.

  Fixpoint wrap (ls : list Type) R {struct ls} : (tuple ls -> R) -> ftype ls R :=
    match ls as ls return (tuple ls -> R) -> ftype ls R with
      | nil => fun f => f tt
      | cons l ls => fun f => fun x => wrap ls (fun g => f (x,g))
    end.

  Fixpoint apply (ls : list Type) R {struct ls} : ftype ls R -> tuple ls -> R :=
    match ls as ls return ftype ls R -> tuple ls -> R with
      | nil => fun f _ => f
      | cons l ls  => fun f t => @apply ls R (f (fst t)) (snd t)
    end.

  Context {MF : MonadFix}.

  Definition mfix_multi (ls : list Type) (R : Type)
    (f : ftype ls (m R) -> ftype ls (m R))
    : ftype ls (m R) :=
    @wrap ls (m R) (@mfix MF (tuple ls) R
      (fun packed => apply ls (m R) (f (wrap ls packed)))).

End MonadFix.
Arguments mfix {m MonadFix T U} _ _.

Class MonadExc E (m : Type -> Type) : Type :=
{ raise : forall {T}, E -> m T
; catch : forall {T}, m T -> (E -> m T) -> m T
}.

Class MonadPlus (m : Type -> Type) : Type :=
{ mplus : forall {A B:Type}, m A -> m B -> m (A + B)%type }.

Module MonadPlusNotation.
  Notation "x <+> y" := (mplus x y) (at level 49, right associativity).
End MonadPlusNotation.

Instance MonadFunctor {m} {mMonad:Monad m} : Functor m :=
{ fmap := @liftM _ _ }.

Instance MonadApplicative {m} {M:Monad m} : Applicative m :=
{ pure := @ret _ _
; ap := @apM _ _
}.
