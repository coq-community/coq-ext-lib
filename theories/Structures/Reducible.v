Require Import RelationClasses.
Require Import ExtLib.Structures.BinOps.

Class Container (T E : Type) : Type :=
  In : T -> E -> Prop.

Class Reducible (T E : Type) : Type :=
  reduce : forall {A} (base : A) (single : E -> A) (join : A -> A -> A), T -> A.

Class Foldable (T E : Type) : Type :=
  fold : forall {A} (add : E -> A -> A) (base : A), T -> A.

Section foldM.
  Require Import ExtLib.Structures.Monad.
  Variables T E : Type.
  Variable Foldable_te : Foldable T E.
  Variable m : Type -> Type.
  Variable Monad_m : Monad m.

  Definition foldM {A} (add : E -> A -> m A) (base : m A) (t : T) : m A :=
    fold (fun x acc => bind acc (add x)) base t.  
End foldM.



(*
Section Laws.
  Context (T E : Type).
  Context (R : Reducible T E).

  Class ReducibleLaw : Prop :=
    reduce_spec : forall A 
      (unit : A)
      (single : E -> A)
      (join : A -> A -> A)
      (eqA : A -> A -> Prop),
      LeftUnit join unit eqA ->
      RightUnit join unit eqA ->
      Commutative join eqA ->
      Associative join eqA ->
      forall t, eqA (reduce unit single join t)
                    (fold_right (fun acc x => join acc (single x)) ?? unit)
*)