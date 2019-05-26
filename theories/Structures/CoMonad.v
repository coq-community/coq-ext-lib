Set Implicit Arguments.
Set Strict Implicit.

Class CoMonad (m : Type -> Type) : Type :=
{ extract : forall {A}, m A -> A
; extend : forall {A B}, (m A -> B) -> m A -> m B
}.

(* Aliases for [extract] and [extend] for backward compatiblity *)
Section BackwardCompatibility.
  Context {m: Type->Type}.
  Context {CoMonad: CoMonad m}.

  Definition coret {A: Type} := extract (A:=A).
  Definition cobind {A B: Type} := extend (A:=A) (B:=B).

End BackwardCompatibility.

