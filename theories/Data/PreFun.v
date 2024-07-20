From Coq.Classes Require Import Morphisms.
From Coq.Relations Require Import Relations.

Set Implicit Arguments.
Set Strict Implicit.
Set Universe Polymorphism.

Definition Fun@{d c} (A : Type@{d}) (B : Type@{c}) := A -> B.

Definition compose@{uA uB uC} {A:Type@{uA}} {B:Type@{uB}} {C : Type@{uC}}
    (g : B -> C) (f : A -> B) : A -> C :=
  fun x => g (f x).
