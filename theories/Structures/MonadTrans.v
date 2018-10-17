Require Import ExtLib.Structures.Monad.

Set Implicit Arguments.
Set Universe Polymorphism.
Set Primitive Projections.

Class MonadT (m : Type -> Type) (mt : Type -> Type) : Type :=
{ lift : forall {t}, mt t -> m t }.
