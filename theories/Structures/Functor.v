Require Import ExtLib.Core.Any.

Set Implicit Arguments.
Set Strict Implicit.

Section functor.
  Variable F : Type -> Type.

  Class Functor : Type :=
  { fmap : forall A B, (A -> B) -> F A -> F B
  }.

  Definition ID {T : Type} (f : T -> T) : Prop :=
    forall x, f x = x.

  Class FunctorOk (ff : Functor) : Type :=
  { fmap_id : forall T (f : T -> T) (g : F T -> F T), ID f -> ID (fmap f) }.

  Class PFunctor : Type :=
  { FunP : Type -> Type
  ; pfmap : forall {A B} {P : FunP B}, (A -> B) -> F A -> F B
  }.

  Existing Class FunP.
  Hint Extern 0 (@FunP _ _ _) => progress (simpl FunP) : typeclass_instances.

  Global Instance PFunctor_From_Functor (F : Functor) : PFunctor :=
  { FunP := Any
  ; pfmap := fun _ _ _ f x => fmap f x
  }.
End functor.

Arguments FunctorOk {F} Fun : rename.

Module FunctorNotation.
  Notation "f <$> x" := (@pfmap _ _ _ _ _ f x) (at level 51, right associativity).
End FunctorNotation.

