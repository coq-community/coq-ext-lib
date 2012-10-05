

Section Sets.
  Variable S : Type.

  Class CSet {T} (R : T -> T -> Prop) : Type :=
  { contains : T -> S -> bool
  ; empty    : S
  ; add      : T -> S -> S
  ; remove   : T -> S -> S
  }.

End Sets.
