From ExtLib Require Import
     Functor.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Universe Polymorphism.

Class Applicative@{d c} (T : Type@{d} -> Type@{c}) :=
{ pure : forall {A : Type@{d}}, A -> T A
; ap : forall {A B : Type@{d}}, T (A -> B) -> T A -> T B
}.

Global Hint Mode Applicative ! : typeclass_instances.

Module ApplicativeNotation.
  Notation "f <*> x" := (ap f x) (at level 52, left associativity).
End ApplicativeNotation.
Import ApplicativeNotation.

Section applicative.
  Definition liftA@{d c} {T : Type@{d} -> Type@{c}} {AT:Applicative@{d c} T} {A B : Type@{d}} (f:A -> B) (aT:T A) : T B := pure f <*> aT.
  Definition liftA2@{d c} {T : Type@{d} -> Type@{c}} {AT:Applicative@{d c} T} {A B C : Type@{d}} (f:A -> B -> C) (aT:T A) (bT:T B) : T C := liftA f aT <*> bT.
End applicative.

Section Instances.

Universe d c.
Context (T : Type@{d} -> Type@{c}) {AT : Applicative T}.

Global Instance Functor_Applicative@{} : Functor T :=
{ fmap := @liftA _ _ }.

End Instances.
