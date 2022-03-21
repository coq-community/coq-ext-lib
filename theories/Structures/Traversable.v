Require Import ExtLib.Structures.Applicative.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Polymorphic Class Traversable@{d r} (T : Type@{d} -> Type@{r}) : Type :=
{ mapT : forall {F : Type@{d} -> Type@{r} }
                {Ap:Applicative@{d r} F} {A B : Type@{d}},
    (A -> F B) -> T A -> F (T B)
}.

Polymorphic Definition sequence@{d r}
            {T : Type@{d} -> Type@{r}}
            {Tr:Traversable T}
            {F : Type@{d} -> Type@{r}} {Ap:Applicative F} {A : Type@{d}}
  : T (F A) -> F (T A) := mapT (@id (F A)).

Polymorphic Definition forT@{d r}
            {T : Type@{d} -> Type@{r}}
            {Tr:Traversable T} {F : Type@{d} -> Type@{r}} {Ap:Applicative F}
            {A B : Type@{d}} (aT:T A) (f:A -> F B) : F (T B)
:= mapT f aT.
