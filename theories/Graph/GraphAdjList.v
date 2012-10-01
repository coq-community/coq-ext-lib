Require Import List.
Require Import ExtLib.Graph.Graph.
Require Import ExtLib.Graph.BuildGraph.
Require Import ExtLib.FMaps.FMaps.
Require Import ExtLib.Decidables.Decidable.

Set Implicit Arguments.
Set Strict Implicit.

Section GraphImpl.
  Variable V : Type.
  Variable map : Type -> Type.
  Variable Map : Map V map.
  Variable RelDec_V : RelDec (@eq V).

  Definition adj_graph : Type :=
    map (list V).

  Definition verts (g : adj_graph) : list V :=
    keys g.

  Definition succs (g : adj_graph) (v : V) : list V :=
    match find v g with
      | None => nil
      | Some vs => vs
    end.

  Global Instance Graph_adj_graph : Graph V adj_graph :=
  { verticies := verts
  ; successors := succs
  }.

  Definition add_vertex (v : V) (g : adj_graph) : adj_graph :=
    if contains v g then g else add v nil g.

  (** TODO: Move this **)
  Fixpoint list_in_dec v (ls : list V) : bool :=
      match ls with
        | nil => false
        | l :: ls =>
          if eq_dec l v then true
          else list_in_dec v ls
      end.

  Definition add_edge (f t : V) (g : adj_graph) : adj_graph :=
    match find f g with
      | None =>
        add f (t :: nil) g
      | Some vs =>
        if list_in_dec t vs then g
        else add f (t :: vs) g
    end.

  Global Instance GraphBuilder_adj_graph : BuildGraph V adj_graph :=
  { emptyGraph := empty
  ; addVertex := add_vertex
  ; addEdge   := add_edge
  }.


End GraphImpl.

