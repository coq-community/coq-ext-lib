Require Import ExtLib.Structures.Reducible.

Global Instance Foldable_option {T} : Foldable (option T) T :=
  fun _ f d v => 
    match v with
      | None => d
      | Some x => f x d
    end.

