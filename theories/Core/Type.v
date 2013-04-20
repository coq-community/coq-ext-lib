Require Import Relations.
Require Import RelationClasses.
Require Import ExtLib.Structures.Proper.

(** Types are defined by their equivalence relations
 ** Proper elements are the elements for which the equivalence
 ** relation is reflexive.
 **)
Class type (T : Type) : Type :=
{ equal : relation T }.

Section type.
  Context {T : Type}.
  Variable tT : type T.
  
  Global Instance Proper_type : Proper T :=
  { proper := fun x => equal x x }.

  Class typeOk :=
  { only_proper : forall x y, equal x y -> proper x /\ proper y
  ; equiv_prefl :> PReflexive equal
  ; equiv_sym :> Symmetric equal
  ; equiv_trans :> Transitive equal
  }.

  Global Instance proper_left :
    typeOk -> 
    forall x y : T, equal x y -> proper x.
  Proof.
    clear. intros. eapply only_proper in H0; intuition.
  Qed.
  Global Instance proper_right :
    typeOk -> 
    forall x y : T, equal x y -> proper x.
  Proof.
    clear. intros. eapply only_proper in H0; intuition.
  Qed.

End type.
