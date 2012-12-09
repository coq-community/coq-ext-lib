Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Structures.Functor.

Global Instance Foldable_option {T} : Foldable (option T) T :=
  fun _ f d v => 
    match v with
      | None => d
      | Some x => f x d
    end.
