Require Import RelationClasses.
Require Import ExtLib.Structures.Monad.

Set Implicit Arguments.
Set Strict Implicit.

(** First-class, non-dependent finite maps **)
Section Maps.
  Variable K : Type.
  Variable map : Type -> Type.

  (** General Maps **)
  Class Map : Type :=
  { empty    : forall {V}, map V
  ; add      : forall {V}, K -> V -> map V -> map V
  ; remove   : forall {V}, K -> map V -> map V
  ; lookup   : forall {V}, K -> map V -> option V
  }.

  (** Finite Maps **)
  (** This is temporary, it should be something like "foldable" **)
  Class FMap : Type :=
  { fmap_foldM : forall {m} {M : Monad m} {V T} , (K -> V -> T -> m T) -> T -> map V -> m T }.

  Variable M : Map.

  Definition contains {V} (k : K) (m : map V) : bool :=
    match lookup k m with
      | None => false
      | Some _ => true
    end.

  Definition singleton {V} (k : K) (v : V) : map V :=
    add k v empty.

  Variable FM : FMap.

(*
  Definition combine {T} (f : K -> T -> T -> T) (m1 m2 : map T) : map T :=
    unIdent (fmap_foldM (m := ident) (fun k v acc =>
      ret match lookup k acc with
            | None => add k v acc
            | Some v' => add k (f k v' v) acc
          end) m2 m1).
*)
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
Arguments lookup {K} {map} {Map} {V} _ _.
Arguments contains {K} {map} {M} {V} _ _.
Arguments singleton {K} {map} {M} {V} _ _.
Arguments fmap_foldM {K} {map} {FMap} {m} {M} {V} {T} _ _ _.
(*
Arguments combine {K} {map} {M} {FM} {T} _ _ _.
*)
