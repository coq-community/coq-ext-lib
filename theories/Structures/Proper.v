Set Implicit Arguments.
Set Strict Implicit.

Class Proper (T : Type) : Type :=
  proper : T -> Prop.

Section relations.
  Context {T : Type} {P : Proper T} (R : T -> T -> Prop).


  Class PReflexive : Prop :=
    preflexive : forall x : T, proper x -> R x x.
  
  Class PSymmetric : Prop :=
    psymmetric : forall x y, proper x -> proper y -> R x y -> R y x.

  Class PTransitive : Prop :=
    ptransitive : forall x y z, proper x -> proper y -> proper z ->
      R x y -> R y z -> R x z.
End relations.