Require Import List.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Structures.DMonad.

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
  fun _ f x ls => fold_right (fun y x => f y x) x ls.

Global Instance DMonad_list {T} : DMonad (list T) T :=
{ dreturn := fun x => cons x nil
; dzero := nil
; djoin := @List.app _
}.

Section toList.
  Variable C E : Type.
  Context {F : Foldable C E}.

  Definition toList : C -> list E :=
    map (fun x => x).
End toList.