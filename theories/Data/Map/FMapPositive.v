Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Data.Positive.

Set Implicit Arguments.
Set Strict Implicit.

Section pmap.
  Variable T : Type.
  Inductive pmap : Type :=
  | Empty 
  | Branch : option T -> pmap -> pmap -> pmap.

  Definition pmap_here (m : pmap) : option T :=
    match m with
      | Empty => None
      | Branch d _ _ => d
    end.

  Definition pmap_left (m : pmap) : pmap :=
    match m with
      | Empty => Empty
      | Branch _ l _ => l
    end.

  Definition pmap_right (m : pmap) : pmap :=
    match m with
      | Empty => Empty
      | Branch _ _ r => r
    end.

  Fixpoint pmap_lookup (p : positive) (m : pmap) : option T :=
    match m with
      | Empty => None
      | Branch d l r =>
        match p with
          | xH => d
          | xO p => pmap_lookup p l
          | xI p => pmap_lookup p r
        end
    end.

  Fixpoint pmap_insert (p : positive) (v : T) (m : pmap) : pmap :=
    match p with
      | xH => Branch (Some v) (pmap_left m) (pmap_right m)
      | xO p => Branch (pmap_here m) (pmap_insert p v (pmap_left m)) (pmap_right m)
      | xI p => Branch (pmap_here m) (pmap_left m) (pmap_insert p v (pmap_right m)) 
    end.

  Definition branch (o : option T) (l r : pmap) : pmap :=
    match o , l , r with
      | None , Empty , Empty => Empty
      | _ , _ , _ => Branch o l r
    end.

  Fixpoint pmap_remove (p : positive) (m : pmap) : pmap :=
    match m with
      | Empty => Empty
      | Branch d l r =>
        match p with
          | xH => branch None l r
          | xO p => branch d (pmap_remove p l) r
          | xI p => branch d l (pmap_remove p r)
        end
    end.

  Definition pmap_empty : pmap := Empty.

  Fixpoint pmap_union (f m : pmap) : pmap :=
    match f with
      | Empty => m 
      | Branch d l r =>
        
        Branch (match d with
                  | Some x => Some x
                  | None => pmap_here m
                end) (pmap_union l (pmap_left m)) (pmap_union r (pmap_right m))
    end.

  Global Instance Map_pmap : Map positive T pmap :=
  { empty := pmap_empty
  ; add := pmap_insert
  ; remove := pmap_remove
  ; lookup := pmap_lookup
  ; union := pmap_union
  }.

End pmap.
