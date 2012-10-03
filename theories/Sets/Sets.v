

Section Sets.
  Variable S : forall {T : Type}, (T -> T -> Prop) -> Type.

  Class CSet {T} (R : T -> T -> Prop) : Type :=
  { contains : T -> S _ R -> bool
  ; empty    : S _ R
  ; add      : T -> S _ R -> S _ R
  ; remove   : T -> S _ R -> S _ R
  }.

End Sets.
