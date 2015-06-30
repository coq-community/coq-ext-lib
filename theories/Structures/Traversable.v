Require Import ExtLib.Structures.Applicative.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Class Traversable (T : Type@{d} -> Type@{r}) : Type :=
{ mapT : forall {F : Type@{r} -> Type } {Ap:Applicative F} {A B : Type@{d}}, (A -> F B) -> T A -> F (T B) }.

Section traversable.

  Definition sequence {T : Type@{d} -> Type@{d}} {Tr:Traversable T} {F : Type@{d} -> Type@{d}} {Ap:Applicative F} {A : Type@{d}}
  : T (F A) -> F (T A) := mapT (@id _).
  Definition forT  {T : Type@{d} -> Type@{d}} {Tr:Traversable T} {F : Type@{d} -> Type@{d}} {Ap:Applicative F} {A B : Type@{d}} (aT:T A) (f:A -> F B) : F (T B) := mapT f aT.
End traversable.
