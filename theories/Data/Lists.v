Require Import List.

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