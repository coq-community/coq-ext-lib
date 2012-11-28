Require Import RelationClasses.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Reducible.

Set Implicit Arguments.
Set Strict Implicit.

(** First-class, non-dependent finite maps **)
Section Maps.
  Variable K : Type.
  Variable map : Type -> Type.

  (** General Maps **)
  Class DMap : Type :=
  { empty    : forall {V}, map V
  ; add      : forall {V}, K -> V -> map V -> map V
  ; remove   : forall {V}, K -> map V -> map V
  ; lookup   : forall {V}, K -> map V -> option V
  ; union    : forall {V}, map V -> map V -> map V
  }.

  Variable M : DMap.

  Definition contains {V} (k : K) (m : map V) : bool :=
    match lookup k m with
      | None => false
      | Some _ => true
    end.

  Definition singleton {V} (k : K) (v : V) : map V :=
    add k v empty.

  Definition combine {T} {F : Foldable (map T) (K * T)} (f : K -> T -> T -> T) (m1 m2 : map T) : map T :=
    fold (fun k_v acc =>
      let '(k,v) := k_v in
      match lookup k acc with
        | None => add k v acc
        | Some v' => add k (f k v v') acc
      end) m2 m1.

  Definition filter {T} {F : Foldable (map T) (K * T)} (f : K -> T -> bool) (m : map T) : map T :=
    fold (fun k_v acc =>
      let '(k,v) := k_v in
      if f k v
        then add k v acc
        else acc) empty m.
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
Arguments add {K} {map} {DMap} {V} _ _ _.
Arguments remove {K} {map} {DMap} {V} _ _.
Arguments lookup {K} {map} {DMap} {V} _ _.
Arguments contains {K} {map} {M} {V} _ _.
Arguments singleton {K} {map} {M} {V} _ _.
Arguments combine {K} {map} {M} {T} {_} _ _ _.

Section dmonad.
  Require Import ExtLib.Structures.DMonad.

  Variable M : Type -> Type.
  Context {K : Type}.
  Context {set : DMap K M}. 

  Global Instance DMonda_map {V} : DMonad (M V) (K * V) :=
  {| dzero := empty
   ; dreturn := fun k_v => singleton (fst k_v) (snd k_v)
   ; djoin := @union _ _ _ _
  |}.
End dmonad.