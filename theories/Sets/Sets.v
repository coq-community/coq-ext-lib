

Section Sets.
  Variable S : Type.

  Class CSet {T} (R : T -> T -> Prop) : Type :=
  { contains : T -> S -> bool
  ; empty    : S
  ; add      : T -> S -> S
  ; remove   : T -> S -> S
  }.

End Sets.

Arguments empty {S} {T} {R} {_}.
Arguments contains {S} {T} {R} {_} _ _.
Arguments add {S} {T} {R} {_} _ _.
Arguments remove {S} {T} {R} {_} _ _.