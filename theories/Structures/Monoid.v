Set Implicit Arguments.
Set Maximal Implicit Insertion.

Section Monoid.
  Variable S : Type.

  Record Monoid : Type :=
  { monoid_plus : S -> S -> S
  ; monoid_unit : S
  }.

  (* Variable M : Monoid. *)

  (* Definition monoid_sum (ls : list S) : S := *)
  (*   fold_left (monoid_plus M) ls (monoid_unit M). *)

End Monoid.
