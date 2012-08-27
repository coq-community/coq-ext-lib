Set Implicit Arguments.
Set Strict Implicit.

Class Monad (m : Type -> Type) : Type :=
{ ret : forall {t}, t -> m t
; bind : forall {t}, m t -> forall {u}, (t -> m u) -> m u
}.

Class MonadT (mt : Type -> Type) (m : Type -> Type) : Type :=
{ lift : forall {t}, mt t -> m t }.

Definition liftM m (M : Monad m) T U (f : T -> U) : m T -> m U :=
  fun x => bind x (fun x => ret (f x)).

Definition liftM2 m (M : Monad m) T U V (f : T -> U -> V) : m T -> m U -> m V :=
  fun x y => bind x (fun x => bind y (fun y => ret (f x y))).

Module MonadNotation.

  Notation "x <- c1 ; c2" := (@bind _ _ _ c1 _ (fun x => c2)) (at level 51, right associativity).

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
{ local : T -> forall t, m t -> m t
; ask : m T
}.

Class State (T : Type) (m : Type -> Type) : Type :=
{ get : m T 
; put : T -> m unit
}.

Class Zero (m : Type -> Type) : Type :=
{ zero : forall {T}, m T }.
