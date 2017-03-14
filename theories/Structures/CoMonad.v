Require Import ExtLib.Structures.Functor.

Set Implicit Arguments.
Set Strict Implicit.

Section CoMonad.
  Variable m : Type -> Type.

  Class CoMonad : Type :=
  { extract : forall {A}, m A -> A
  ; extend : forall {A B}, (m A -> B) -> m A -> m B
  ; duplicate : forall {A}, m A -> m (m A)
  }.

  Definition from_extend
             (doExtract : forall {A}, m A -> A)
             (doExtend : forall {A B}, (m A -> B) -> m A -> m B)
  : CoMonad :=
  {| extract := @doExtract
   ; extend := @doExtend
   ; duplicate := fun A c => doExtend (fun x => x) c |}.

  Context {Fm : Functor m}.

  Definition from_duplicate
             (doExtract : forall {A}, m A -> A)
             (doDuplicate : forall {A}, m A -> m (m A))
  : CoMonad :=
  {| extract := @doExtract
   ; extend := fun A B k c => fmap (F:=m) k (doDuplicate c)
   ; duplicate := @doDuplicate |}.

End CoMonad.

Arguments CoMonad _ : clear implicits.
Arguments extract {m _ _} _.
Arguments extend {m _ _ _} _ _.
Arguments duplicate {m _ _} _.