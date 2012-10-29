Require Import List.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Reducible.

Set Implicit Arguments.
Set Strict Implicit.

Section keyed.
  Variable K : Type.
  Variable RD_K : RelDec (@eq K).

  Definition alist (T : Type) : Type := list (K * T).

  Definition alist_add V (k : K) (v : V) (m : alist V) : alist V :=
    (k, v) :: m.

  Definition alist_remove V (k : K) (m : alist V) : alist V :=
    filter (fun x => negb (eq_dec k (fst x))) m.

  Fixpoint alist_find V (k : K) (m : alist V) : option V :=
    match m with
      | nil => None
      | (k',v) :: ms =>
        if eq_dec k k' then
          Some v
        else
          alist_find k ms
    end.

  Global Instance DMap_alist : DMap K alist :=
  { empty  := fun _ => @nil _
  ; add    := alist_add
  ; remove := alist_remove
  ; lookup := alist_find
  }.

  Section fold.
    Import MonadNotation.
    Local Open Scope monad_scope.

    Variables V T : Type.
    Variable f : K -> V -> T -> T.

    Fixpoint fold_alist (acc : T) (map : alist V) : T :=
      match map with
        | nil => acc
        | (k,v) :: m =>
          let acc := f k v acc in
          fold_alist acc m
      end.
  End fold.

  Global Instance Foldable_alist V : Foldable (alist V) (K * V) :=
    fun _ f b => fold_alist (fun k v => f (k,v)) b.

End keyed.

(** Performance Test **)
(*
Module TEST.
  Definition m := alist nat nat.
  Instance Map_m : Map nat (alist nat).
    apply Map_alist. eauto with typeclass_instances.
  Defined.

  Definition z : m :=
    (fix fill n acc : m :=
      let acc := add n n acc in
      match n with
        | 0 => acc
        | S n => fill n acc
      end) 500 empty.

  Time Eval compute in
    let z := z in
    (fix find_all n : unit :=
      let _ := lookup n z in
      match n with
        | 0 => tt
        | S n => find_all n
      end) 500.
End TEST.
*)