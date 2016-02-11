Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.POption.

Set Universe Polymorphism.

Section plist.
  Polymorphic Universe i.
  Variable T : Type@{i}.

  Polymorphic Inductive plist : Type@{i} :=
  | pnil
  | pcons : T -> plist -> plist.

  Polymorphic Fixpoint length (ls : plist) : nat :=
    match ls with
    | pnil => 0
    | pcons _ ls' => S (length ls')
    end.

  Polymorphic Fixpoint app (ls ls' : plist) : plist :=
    match ls with
    | pnil => ls'
    | pcons l ls => pcons l (app ls ls')
    end.

  Polymorphic Definition hd (ls : plist) : poption T :=
    match ls with
    | pnil => pNone
    | pcons x _ => pSome x
    end.

  Polymorphic Definition tl (ls : plist) : plist :=
    match ls with
    | pnil => ls
    | pcons _ ls => ls
    end.

  Polymorphic Fixpoint pIn (a : T) (l : plist) : Prop :=
    match l with
    | pnil => False
    | pcons b m => b = a \/ pIn a m
    end.

  Polymorphic Fixpoint anyb (p : T -> bool) (ls : plist) : bool :=
    match ls with
    | pnil => false
    | pcons l ls0 => if p l then true else anyb p ls0
    end.

  Polymorphic Fixpoint allb (p : T -> bool) (ls : plist) : bool :=
    match ls with
    | pnil => true
    | pcons l ls0 => if p l then anyb p ls0 else false
    end.

  Polymorphic Fixpoint nth_error (ls : plist) (n : nat) : poption T :=
    match n , ls with
    | 0 , pcons l _ => pSome l
    | S n , pcons _ ls => nth_error ls n
    | _ , _ => pNone
    end.

  Section folds.
    Polymorphic Universe j.
    Context {U : Type@{j}}.
    Variable f : T -> U -> U.

    Polymorphic Fixpoint fold_left (acc : U) (ls : plist) : U :=
      match ls with
      | pnil => acc
      | pcons l ls => fold_left (f l acc) ls
      end.

    Polymorphic Fixpoint fold_right (ls : plist) (rr : U) : U :=
      match ls with
      | pnil => rr
      | pcons l ls => f l (fold_right ls rr)
      end.
  End folds.

End plist.

Arguments pnil {_}.
Arguments pcons {_} _ _.
Arguments pIn {_} _ _.
Arguments anyb {_} _ _.
Arguments allb {_} _ _.
Arguments fold_left {_ _} _ _ _.
Arguments fold_right {_ _} _ _ _.
Arguments nth_error {_} _ _.

Section pmap.
  Polymorphic Universe i j.
  Context {T : Type@{i}}.
  Context {U : Type@{j}}.
  Variable f : T -> U.

  Polymorphic Fixpoint fmap_plist (ls : plist@{i} T) : plist@{j} U :=
    match ls with
    | pnil => pnil
    | pcons l ls => pcons (f l) (fmap_plist ls)
    end.
End pmap.

Polymorphic Definition Functor_plist@{i} : Functor@{i i} plist@{i} :=
{| fmap := @fmap_plist@{i i} |}.
Existing Instance Functor_plist.


Section applicative.
  Polymorphic Universe i j.

  Context {T : Type@{i}} {U : Type@{j}}.
  Polymorphic Fixpoint ap_plist
              (fs : plist@{i} (T -> U)) (xs : plist@{i} T)
    : plist@{j} U :=
    match fs with
    | pnil => pnil
    | pcons f fs => app@{j} _ (fmap_plist@{i j} f xs) (ap_plist fs xs)
    end.
End applicative.

Polymorphic Definition Applicative_plist@{i} : Applicative@{i i} plist@{i} :=
{| pure := fun _ val => pcons val pnil
 ; ap := @ap_plist
 |}.
