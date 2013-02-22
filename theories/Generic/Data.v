(** This module gives a representation of inductive types **)

Inductive itype : Type :=
| Par : nat -> itype
| Rec : itype
| Inj : Type -> itype.

