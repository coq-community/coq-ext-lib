Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Structures.Applicative.

Global Instance Foldable_option {T} : Foldable (option T) T :=
  fun _ f d v => 
    match v with
      | None => d
      | Some x => f x d
    end.

Global Instance Traversable_option : Traversable option :=
{| mapT := fun F _ _ _ f o =>
  match o with
    | None => pure None
    | Some o => ap (pure (@Some _)) (f o)
  end
|}.

