Set Implicit Arguments.
Set Maximal Implicit Insertion.

Class PApplicative (T : Type@{d} -> Type) :=
{ AppP : Type@{d} -> Type
; ppure : forall {A : Type@{d}} {P : AppP A}, A -> T A
; pap : forall {A B : Type@{d}} {P : AppP B}, T (A -> B) -> T A -> T B
}.

Class Applicative (T : Type@{d} -> Type) :=
{ pure : forall {A : Type@{d}}, A -> T A
; ap : forall {A B : Type@{d}}, T (A -> B) -> T A -> T B
}.

Module ApplicativeNotation.
  Notation "f <*> x" := (ap f x) (at level 51, right associativity).
End ApplicativeNotation.
Import ApplicativeNotation.

Section applicative.
  Definition liftA {T : Type@{d} -> Type} {AT:Applicative T} {A B : Type@{d}} (f:A -> B) (aT:T A) : T B := pure f <*> aT.
  Definition liftA2 {T : Type@{d} -> Type} {AT:Applicative T} {A B C : Type@{d}} (f:A -> B -> C) (aT:T A) (bT:T B) : T C := liftA f aT <*> bT.
End applicative.
