Require Import Lists.List.
Require Import String.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Section Monoid.
  Variable S : Type.

  Record Monoid : Type :=
  { monoid_plus : S -> S -> S
  ; monoid_unit : S
  }.

  Variable M : Monoid.

  Definition monoid_sum (ls : list S) : S :=
    fold_left (monoid_plus M) ls (monoid_unit M).

End Monoid.

(** Some Standard Instances **)
Definition Monoid_list_app {T} : Monoid (list T) :=
{| monoid_plus := @List.app _
 ; monoid_unit := @nil _
 |}.

Definition Monoid_nat_plus : Monoid nat :=
{| monoid_plus := plus
 ; monoid_unit := 0
 |}.

Definition Monoid_nat_mult : Monoid nat :=
{| monoid_plus := mult
 ; monoid_unit := 1
 |}.

Definition Monoid_string_append : Monoid string :=
{| monoid_plus := String.append
 ; monoid_unit := EmptyString
|}.

Definition Monoid_string_append_compose : Monoid (string -> string) :=
{| monoid_plus g f x := g (f x)
 ; monoid_unit x := x
|}.
