Set Implicit Arguments.
Set Strict Implicit.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** This class should be used when no requirements are needed **)
Class Any (T : Type) : Type.

Global Instance Any_a (T : Type) : Any T := {}.

Definition RESOLVE (T : Type) : Type := T.

Existing Class RESOLVE.

#[global]
Hint Extern 0 (RESOLVE _) => unfold RESOLVE : typeclass_instances.
