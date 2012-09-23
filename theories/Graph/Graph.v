Set Implicit Arguments.
Set Strict Implicit.

Section Graph.
  Variable V : Type.
  Variable G : Type.

  Class Graph : Type :=
  { verticies  : G -> list V
  ; successors : G -> V -> list V
  }.
End Graph.

(*
Section GraphImpl.
  Require Import List.
  Require Import ExtLib.Decidables.Decidable.

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

Section GraphAlgos.
  Variable V : Type.
  Variable RelDec_V : RelDec (@eq V).
  Variable G : Type.
  
  Context {graph : Graph V G}.

  Section Traverse.
    Variable g : G.

    Fixpoint list_in_dec v (ls : list V) : bool :=
      match ls with
        | nil => false
        | l :: ls => 
          if eq_dec l v then true
          else list_in_dec v ls
      end.

    Require Import Monad.
    Require Import ExtLib.Monad.Folds.
    
    Section monadic.
      Variable m : Type -> Type.
      Context {Monad_m : Monad m} {MonadFix_m : MonadFix m}.

      Definition dfs : V -> list V -> m (list V) :=
        mfix_multi (V :: list V :: nil) (list V) (fun rec from seen => 
          if list_in_dec from seen 
          then ret seen 
          else 
            foldlM (fun v acc => 
              if list_in_dec v acc
              then ret acc
              else rec v acc) seen (successors g from)).

    End monadic.
  End Traverse.
End GraphAlgos.
*)