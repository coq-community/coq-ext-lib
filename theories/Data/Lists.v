Require Import Coq.Lists.List.
Require Import ExtLib.Structures.Reducible.

Set Implicit Arguments.
Set Strict Implicit.

Section AllB.
  Variable T : Type.
  Variable p : T -> bool.

  Fixpoint allb (ls : list T) : bool :=
    match ls with
      | nil => true
      | l :: ls =>
        if p l then allb ls else false
    end.

  Fixpoint anyb (ls : list T) : bool :=
    match ls with
      | nil => false
      | l :: ls =>
        if p l then true else anyb ls
    end.
End AllB.

Global Instance Foldable_list {T} : Foldable (list T) T :=
  fun _ f x ls => fold_left (fun x y => f y x) ls x.

Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Applicative.

Global Instance Traversable_list : Traversable list :=
{ mapT := fun F _ A B f =>
  List.fold_right (fun x acc => ap (ap (pure (@cons B)) (f x)) acc) (pure nil)
}.

Global Instance Monad_list : Monad list :=
{ ret  := fun _ x => x :: nil
; bind := fun _ _ x f =>
  List.fold_right (fun x acc => f x ++ acc) nil x
}.
