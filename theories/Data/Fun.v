Require Import Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Data.PreFun.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.CoFunctor.

Set Implicit Arguments.
Set Strict Implicit.

Section functors.
  Variable A : Type.

  Local Instance Functor_Fun : Functor (Fun A) :=
  { fmap _A _B g f x := g (f x) }.

  Local Instance CoFunctor_Fun T : CoFunctor (fun x => x -> T) :=
  {| cofmap := fun _ _ g f => fun x => f (g x) |}.

  Local Instance Functor_functor F G (fF : Functor F) (fG : Functor G) : Functor (fun x => F (G x)) :=
  {| fmap := fun _ _ g => @fmap F _ _ _ (@fmap G _ _ _ g) |}.

  Local Instance CoFunctor_functor F G (fF : Functor F) (fG : CoFunctor G) : CoFunctor (fun x => F (G x)) :=
  {| cofmap := fun _ _ g => @fmap F _ _ _ (@cofmap G _ _ _ g) |}.

  Local Instance Functor_cofunctor F G (fF : CoFunctor F) (fG : Functor G) : CoFunctor (fun x => F (G x)) :=
  {| cofmap := fun _ _ g => @cofmap F _ _ _ (@fmap G _ _ _ g) |}.

  Local Instance CoFunctor_cofunctor F G (fF : CoFunctor F) (fG : CoFunctor G) : Functor (fun x => F (G x)) :=
  {| fmap := fun _ _ g => @cofmap F _ _ _ (@cofmap G _ _ _ g) |}.


End functors.

Global Instance proper_id (T : Type) {tT : type T} : proper (fun x => x).
Proof.
  repeat red; intros. apply H.
Qed.

Export PreFun.