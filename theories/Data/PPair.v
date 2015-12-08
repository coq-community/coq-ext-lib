

Set Printing Universes.
Set Primitive Projections.

Section pair.
  Polymorphic Universes i j.
  Context {T : Type@{i}} {U : Type@{j}}.

  Polymorphic Record ppair : Type :=
  { fst : T ; snd : U }.

End pair.
