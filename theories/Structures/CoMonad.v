Set Implicit Arguments.
Set Strict Implicit.

Class CoMonad (m : Type -> Type) : Type :=
{ extract : forall {A}, m A -> A
; extend : forall {A B}, (m A -> B) -> m A -> m B
}.
