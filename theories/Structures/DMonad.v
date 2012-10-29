(** A monadic structure where the index is fixed **)

Class DMonad (m T : Type) : Type :=
{ dzero : m
; dreturn : T -> m
; djoin : m -> m -> m
}.