Require Import Relations.
Require Import RelationClasses.
Require Import ExtLib.Structures.Proper.

(** Types are defined by their equivalence relations
 ** Proper elements are the elements for which the equivalence
 ** relation is reflexive.
 **)
Class type (T : Type) : Type :=
{ equiv : relation T }.

Section type.
  Context {T : Type}.
  Variable type_T : type T.
  
  Instance Proper_type : Proper equiv :=
  { proper := fun x => equiv x x }.

  Class typeOk (T : Type) (t : type T) :=
  { equiv_sym : Symmetric equiv
  ; equiv_trans : Transitive equiv
  }.
End type.