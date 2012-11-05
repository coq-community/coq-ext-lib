(** A monadic structure where the index is fixed **)

Class DMonad (m T : Type) : Type :=
{ dzero : m
; dreturn : T -> m
; djoin : m -> m -> m
}.

Require Import ExtLib.Structures.Monads.

Section DMonad.
  Variable m : Type -> Type.
  Context {M : Monad m}.
  Context {MP : MonadPlus m}.
  Context {MZ : MonadZero m}.

  Instance DMonad_Monad (T : Type) : DMonad (m T) T :=
  { dreturn := ret 
  ; djoin := mjoin _ _ _
  ; dzero := mzero
  }.
End DMonad.