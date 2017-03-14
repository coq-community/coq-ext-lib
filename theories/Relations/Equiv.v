Require Import Coq.Setoids.Setoid.
Require Export Coq.Classes.Morphisms.

Class Equiv A := equiv: relation A.

Definition ext_equiv {A B: Type} `{Ea: Equiv A, Eb: Equiv B}: Equiv (A -> B)
  := ((equiv) ==> (equiv))%signature.

Typeclasses Transparent Equiv.

Hint Extern 10 (Equiv (_ -> _)) => apply @ext_equiv : typeclass_instances.

