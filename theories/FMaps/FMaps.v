Set Implicit Arguments.
Set Strict Implicit.

(** First-class, non-dependent finite maps **)

Class Map (K : Type) (M : Type -> Type) : Type :=
{ empty    : forall {V}, M V
; add      : forall {V}, K -> V -> M V -> M V
; remove   : forall {V}, K -> M V -> M V
; find     : forall {V}, K -> M V -> option V
}.


Class MapFacts (K : Type) (M : Type -> Type) : Type :=
{ MapsTo   : forall {V}, K -> V -> M V -> Prop
}.



