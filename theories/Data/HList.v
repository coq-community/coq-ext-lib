Require Import List.

Set Implicit Arguments.
Set Strict Implicit.

Section hlist.
  Variable iT : Type.
  Variable F : iT -> Type.

  Inductive hlist : list iT -> Type :=
  | Hnil  : hlist nil
  | Hcons : forall l ls, F l -> hlist ls -> hlist (l :: ls).

  Definition hlist_hd {a b} (hl : hlist (a :: b)) : F a :=
    match hl in hlist x return match x with
                                 | nil => unit
                                 | l :: _ => F l
                               end with
      | Hnil => tt
      | Hcons _ _ x _ => x
    end.

  Definition hlist_tl {a b} (hl : hlist (a :: b)) : hlist b :=
    match hl in hlist x return match x with
                                 | nil => unit
                                 | _ :: ls => hlist ls
                               end with
      | Hnil => tt
      | Hcons _ _ _ x => x
    end.

  Inductive member (a : iT) : list iT -> Type :=
  | MZ : forall ls, member a (a :: ls)
  | MN : forall l ls, member a ls -> member a (l :: ls).

  Fixpoint hlist_get ls a (m : member a ls) : hlist ls -> F a :=
    match m in member _ ls return hlist ls -> F a with
      | MZ _ => hlist_hd
      | MN _ _ r => fun hl => hlist_get r (hlist_tl hl)
    end.
  
  Fixpoint hlist_nth_error {ls} (hs : hlist ls) (n : nat) 
    : option (match nth_error ls n with
                | None => unit
                | Some x => F x
              end) :=
    match hs in hlist ls return option (match nth_error ls n with
                                          | None => unit
                                          | Some x => F x
                                        end)
      with
      | Hnil => None
      | Hcons l ls h hs => 
        match n as n return option (match nth_error (l :: ls) n with
                                      | None => unit
                                      | Some x => F x
                                    end)
          with
          | 0 => Some h
          | S n => hlist_nth_error hs n
        end
    end.

  Fixpoint hlist_nth (ls : list _) (h : hlist ls) (n : nat) :
    match nth_error ls n with
      | None => unit
      | Some t => F t
    end :=
    match h in hlist ls , n as n 
      return match nth_error ls n with
               | None => unit
               | Some t => F t
             end
      with
      | Hnil , 0 => tt
      | Hnil , S _ => tt
      | Hcons _ _ x _ , 0 => x
      | Hcons _ _ _ h , S n => hlist_nth h n
    end.

  Theorem hlist_nth_hlist_nth_error : forall ls h n x,
    @hlist_nth_error ls h n = Some x ->
    hlist_nth h n = x.
  Proof.

End hlist.

Arguments Hnil {_ _}.
Arguments Hcons {_ _ _ _} _ _.

Section hlist_map.
  Variable A : Type.
  Variable F : A -> Type.
  Variable G : A -> Type.
  Variable ff : forall x, F x -> G x.

  Fixpoint hlist_map (ls : list A) (hl : hlist F ls) {struct hl} : hlist G ls :=
    match hl in @hlist _ _ ls return hlist G ls with
      | Hnil => Hnil
      | Hcons _ _ hd tl => 
        Hcons (ff hd) (hlist_map tl)
    end.
End hlist_map.

Section hlist_fold.
  Variables T U V : Type. 
  Variables F : T -> Type. 
  Variable f : U -> forall t : T, F t -> U.

  Fixpoint hlist_fold ls (l : hlist F ls) {struct l} : U -> U :=
    match l in hlist _ ls return U -> U with
      | Hnil => fun acc => acc
      | Hcons _ _ fr hr => fun acc => hlist_fold hr (f acc fr)
    end. 
End hlist_fold.

Section hlist_fold2.
  Variables T U V : Type. 
  Variables F G : T -> Type. 
  Variable f : U -> forall t : T, F t -> G t -> U.

  Fixpoint hlist_fold2 ls (l : hlist F ls) {struct l} : hlist G ls -> U -> U :=
    match l in hlist _ ls return hlist G ls -> U -> U with
      | Hnil => fun _ acc => acc
      | Hcons _ _ fr hr => fun r acc =>
        hlist_fold2 hr (hlist_tl r) (f acc fr (hlist_hd r))
    end. 
End hlist_fold2.
