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

  Notation "x <- c1 ; c2" := (@bind _ _ _ c1 _ (fun x => c2)) (at level 51, right associativity).
  Notation "e1 ;; e2" := (_ <- e1 ; e2) (at level 51, right associativity).

(*
  Section test.
    Variable m : Type -> Type.
    Variable M : Monad m.

    Definition test : m nat :=
      x <- ret 2 ;
      y <- ret 3 ;
      ret (x + y).
*)

End MonadNotation.

Class Reader (T : Type) (m : Type -> Type) : Type :=
{ local : T -> forall {t}, m t -> m t
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