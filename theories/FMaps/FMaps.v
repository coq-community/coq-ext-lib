Require Import RelationClasses.

Set Implicit Arguments.
Set Strict Implicit.

(** First-class, non-dependent finite maps **)
Section Maps.
  Variable K : Type.
  Variable map : Type -> Type.

  Class Map : Type :=
  { empty    : forall {V}, map V
  ; add      : forall {V}, K -> V -> map V -> map V
  ; remove   : forall {V}, K -> map V -> map V
  ; find     : forall {V}, K -> map V -> option V
  ; keys     : forall {V}, map V -> list K
  }.

  Variable M : Map.

  Definition contains {V} (k : K) (m : map V) : bool :=
    match find k m with
      | None => false
      | Some _ => true
    end.

  Definition singleton {V} (k : K) (v : V) : map V :=
    add k v empty.

(*
  Class MapMember : Type :=
  { MapsTo : forall {V}, K -> V -> map V -> Prop }.

  Variable MM : MapMember.

  Definition Empty {V} (m : map V) : Prop :=
    forall k v, MapsTo k v m -> False.

  Definition SubMap {V} (l r : map V) : Prop :=
    forall k v, MapsTo k v l -> MapsTo k v r.

  Global Instance Refl_SubMap V : Reflexive (@SubMap V).
  Proof.
    red. red. auto.
  Qed.

  Global Instance Trans_SubMap V : Transitive (@SubMap V).
  Proof.
    red. red. auto.
  Qed.
*)

(*
  Class MapFacts (K : Type) (map : Type -> Type) (M : Map K map) : Type :=
  { empty_is_Empty : forall {V}, exists MapsTo empty
  }.
*)
End Maps.

Arguments empty {_} {_} {_} {_} .
Arguments add {K} {map} {Map} {V} _ _ _.
Arguments remove {K} {map} {Map} {V} _ _.
Arguments find {K} {map} {Map} {V} _ _.
Arguments contains {K} {map} {M} {V} _ _.
Arguments singleton {K} {map} {M} {V} _ _.