Require Import RelationClasses.
Require Import ExtLib.Structures.BinOps.

Class Reducible (T E : Type) : Type :=
  reduce : forall {A} (base : A) (single : E -> A) (join : A -> A -> A), T -> A.

Class Foldable (T E : Type) : Type :=
  fold : forall {A} (add : E -> A -> A) (base : A), T -> A.

Section RedFold.
  Variables T E : Type.
  
  Definition Reducible_from_Foldable (R : Foldable T E) : Reducible T E :=
    fun A base single join =>
      @fold _ _ R A (fun x => join (single x)) base.
End RedFold.

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
Section mapping.
  Variables T E : Type.
  Variables U V : Type.
  
  Variable f : E -> V.

  Variable Red_te : Reducible T E. 
  Variable Ctor_uv : Constructable U V. (* [unit], [inj], [plus] *)


  reduce unit (fun x => inj (f x)) plus.
*)  
  







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