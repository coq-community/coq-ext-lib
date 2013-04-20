Require Import Coq.Relations.Relations.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Data.Fun.

Set Implicit Arguments.
Set Strict Implicit.

(** TODO: It should be possible to define this completely generically.
 ** i.e. to support [Type -> Type], [Type -> Type -> Type], ...
 **)
Section FunctorOrder.
  Variable F : Type -> Type.

  (** This <= relation is a computational <= relation based on the ideas
   ** of domain theory. It generalizes the usual equivalence relation by,
   ** enabling the relation to talk about computations that are "more defined"
   ** than others.
   **)
  Variable Fleq : forall {T}, relation T -> relation (F T).

  (** This states when an element is a proper element under an equivalence
   ** relation.
   **)
  Variable Proper_m : forall T, Proper T -> Proper (F T).

(*
  Class PreOrder : Type :=
  { fun_refl   : forall T (r : relation T) {P : Proper r}, 
    PReflexive r -> PReflexive (Fleq r)
  ; fun_trans  : forall T (r : relation T) {P : Proper r},
    PTransitive r -> PTransitive (Fleq r)
  }.
*)

End FunctorOrder.