Require Import List.
Require Import ExtLib.Sets.Sets.
Require Import ExtLib.Decidables.Decidable.

Set Implicit Arguments.
Set Strict Implicit.

Section ListSet.

  Definition lset {T : Type} (R : T -> T -> Prop) : Type :=
    list T.

  Variable T : Type.
  Variable R : T -> T -> Prop.
  Variable R_dec : T -> T -> bool.

  Fixpoint lset_contains (v : T) (ls : lset R) : bool :=
    match ls with
      | nil => false
      | l :: ls => if R_dec v l then true else lset_contains v ls
    end.

  Definition lset_empty : lset R := nil.

  Definition lset_add (v : T) (ls : lset R) : lset R :=
    if lset_contains v ls then ls else v :: ls.

  Definition lset_remove (v : T) : lset R -> lset R :=
    filter (fun x => negb (R_dec v x)).
End ListSet.

Global Instance CSet_weak_listset {T} (R : T -> T -> Prop)
  (R_dec : RelDec R) : CSet (@lset T R) R :=
{ contains := lset_contains rel_dec
; empty    := lset_empty R
; add      := lset_add rel_dec
; remove   := lset_remove rel_dec
}.
