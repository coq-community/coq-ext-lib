Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Structures.DMonad.

Global Instance Foldable_option {T} : Foldable (option T) T :=
  fun _ f d v => 
    match v with
      | None => d
      | Some x => f x d
    end.

Global Instance DMonad_option (T : Type) : DMonad (option T) T :=
{| dreturn := @Some _
 ; djoin   := fun x y => match x with 
                           | None => y
                           | x => x
                         end
 ; dzero := None
|}.