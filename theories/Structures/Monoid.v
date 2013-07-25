Set Implicit Arguments.
Set Maximal Implicit Insertion.

Section Monoid.
  Variable S : Type.

  Record Monoid : Type :=
  { monoid_plus : S -> S -> S
  ; monoid_unit : S
  }.

End Monoid.
