Require Import List.
Require Import ExtLib.Graph.Graph.
Require Import ExtLib.Decidables.Decidable.

Set Implicit Arguments.
Set Strict Implicit.

Section GraphImpl.
  Variable V : Type.
  Variable RelDec_V : RelDec (@eq V).

  Definition adj_graph : Type :=
    list (V * list V).

  Definition verts (g : adj_graph) : list V :=
    List.map (@fst _ _) g.

  Fixpoint succs (g : adj_graph) (v : V) : list V :=
    match g with
      | nil => nil
      | (v', vs) :: g =>
        if eq_dec v v' then vs else succs g v
    end.

  Global Instance Graph_adj_graph : Graph V adj_graph :=
  { verticies := verts
  ; successors := succs
  }.
End GraphImpl.