Require Import RelationClasses.
Require Import ExtLib.Structures.BinOps.
Require Import ExtLib.Structures.DMonad.

Set Implicit Arguments.
Set Strict Implicit.

Class Reducible (T E : Type) : Type :=
  reduce : forall {A} (base : A) (single : E -> A) (join : A -> A -> A), T -> A.

Class Foldable (T E : Type) : Type :=
  fold : forall {A} (add : E -> A -> A) (base : A), T -> A.

Section RedFold.
  Variables T E : Type.
  
  Global Instance Reducible_from_Foldable (R : Foldable T E) : Reducible T E | 100 :=
    fun A base single join =>
      @fold _ _ R A (fun x => join (single x)) base.
End RedFold.

Section foldM.
  Require Import ExtLib.Structures.Monad.
  Context {T E : Type}.
  Context {Foldable_te : Foldable T E}.
  Context {m : Type -> Type}.
  Context {Monad_m : Monad m}.

  Definition foldM {A} (add : E -> A -> m A) (base : m A) (t : T) : m A :=
    fold (fun x acc => bind acc (add x)) base t.  
End foldM.

Section reduceM.
  Require Import ExtLib.Structures.Monad.
  Context {T E : Type}.
  Context {Reducible_te : Reducible T E}.
  Context {m : Type -> Type}.
  Context {Monad_m : Monad m}.

  Definition reduceM {A} (base : m A) (single : E -> m A) (join : m A -> m A -> m A)  (t : T) : m A :=
    reduce base single join t.  
End reduceM.

Section mapping.
  Context {T E : Type}.
  Context {U V : Type}.

  Context {Red_te : Reducible T E}. 
  Context {DMonad_uv : DMonad U V}.
  
  Variable f : E -> V.

  Definition map : T -> U :=
    reduce dzero (fun x => dreturn (f x)) djoin.
End mapping.







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