Require Import List.
Require Import ExtLib.Structures.Sets.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Lists.

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
    List.filter (fun x => negb (R_dec v x)).

  Definition lset_union (l r : lset R) : lset R :=
    fold_left (fun x y => lset_add y x) l r.

  Definition lset_difference (l r : lset R) : lset R :=
    List.filter (fun x => negb (lset_contains x r)) l.

  Definition lset_intersect (l r : lset R) : lset R :=
    List.filter (fun x => lset_contains x r) l.

  Definition lset_subset (l r : lset R) : bool :=
    allb (fun x => lset_contains x r) l.

End ListSet.

Global Instance CSet_weak_listset {T} (R : T -> T -> Prop)
  (R_dec : RelDec R) : CSet (@lset T R) R :=
{ contains  := lset_contains rel_dec
; empty     := lset_empty R
; add       := lset_add rel_dec
; singleton := fun x => lset_add rel_dec x (lset_empty R)
; remove    := lset_remove rel_dec
; union     := lset_union rel_dec
; intersect := lset_union rel_dec
; difference := lset_union rel_dec
; subset     := lset_subset rel_dec
; filter     := @List.filter _
}.


