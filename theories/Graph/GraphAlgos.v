Require Import ExtLib.Monad.Monad.
Require Import ExtLib.Monad.Folds.
Require Import ExtLib.Graph.Graph.
Require Import ExtLib.Monad.GFixMonad.
Require Import ExtLib.Monad.IdentityMonad.
Require Import ExtLib.Decidables.Decidable.
Require Import List.

Set Implicit Arguments.
Set Strict Implicit.

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
    
    Section monadic.
      Variable m : Type -> Type.
      Context {Monad_m : Monad m} {MonadFix_m : MonadFix m}.

      Definition dfs' : V -> list V -> m (list V) :=
        mfix_multi (V :: list V :: nil) (list V) (fun rec from seen => 
          if list_in_dec from seen 
          then ret seen 
          else 
            foldlM (fun v acc => 
              if list_in_dec v acc
              then ret acc
              else rec v acc) seen (successors g from)).

    End monadic.

    Definition dfs (from : V) : list V :=
      let res := unIdent (runGFixT (m := ident) (dfs' from nil) (S (length (verticies g)))) in
      match res with
        | None => (** This should never happen! **)
          verticies g
        | Some v => v
      end.

  End Traverse.
End GraphAlgos.
      
  