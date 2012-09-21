Require Import ExtLib.FMaps.FMaps.
Require Import List.
Require Import Decidables.Decidable.

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

  Global Instance Map_alist : Map K alist :=
  { empty  := fun _ => @nil _
  ; add    := alist_add
  ; remove := alist_remove
  ; find   := alist_find
  }.

End keyed.
  