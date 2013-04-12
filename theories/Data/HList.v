Require Import List.
Require Import ExtLib.Structures.EqDep.

Set Implicit Arguments.
Set Strict Implicit.

Section hlist.
  Context {iT : Type}.
  Variable F : iT -> Type.

  Inductive hlist : list iT -> Type :=
  | HNil  : hlist nil
  | HCons : forall l ls, F l -> hlist ls -> hlist (l :: ls).

  Definition hlist_hd {a b} (hl : hlist (a :: b)) : F a :=
    match hl in hlist x return match x with
                                 | nil => unit
                                 | l :: _ => F l
                               end with
      | HNil => tt
      | HCons _ _ x _ => x
    end.

  Definition hlist_tl {a b} (hl : hlist (a :: b)) : hlist b :=
    match hl in hlist x return match x with
                                 | nil => unit
                                 | _ :: ls => hlist ls
                               end with
      | HNil => tt
      | HCons _ _ _ x => x
    end.

  Fixpoint hlist_app ll lr : hlist ll -> hlist lr -> hlist (ll ++ lr) :=
    match ll with
      | nil => fun _ x => x
      | _ :: _ => fun l r => HCons (hlist_hd l) (hlist_app (hlist_tl l) r)
    end.

  Lemma hlist_eta : forall ls (h : hlist ls),
    h = match ls as ls return hlist ls -> hlist ls with
          | nil => fun _ => HNil
          | a :: b => fun h => HCons (hlist_hd h) (hlist_tl h)
        end h.
  Proof.
    intros. destruct h; auto.
  Qed.


  Lemma hlist_nil_eta : forall (h : hlist nil), h = HNil.
  Proof.
    intros; rewrite (hlist_eta h); reflexivity.
  Qed.

  Lemma hlist_cons_eta : forall a b (h : hlist (a :: b)),
    h = HCons (hlist_hd h) (hlist_tl h).
  Proof.
    intros; rewrite (hlist_eta h); reflexivity.
  Qed.

  Inductive member (a : iT) : list iT -> Type :=
  | MZ : forall ls, member a (a :: ls)
  | MN : forall l ls, member a ls -> member a (l :: ls).

  Fixpoint hlist_get ls a (m : member a ls) : hlist ls -> F a :=
    match m in member _ ls return hlist ls -> F a with
      | MZ _ => hlist_hd
      | MN _ _ r => fun hl => hlist_get r (hlist_tl hl)
    end.

  Fixpoint hlist_nth {ls} (hs : hlist ls) (n : nat) 
    : option (match nth_error ls n with
                | None => unit
                | Some x => F x
              end) :=
    match hs in hlist ls return option (match nth_error ls n with
                                          | None => unit
                                          | Some x => F x
                                        end)
      with
      | HNil => None
      | HCons l ls h hs => 
        match n as n return option (match nth_error (l :: ls) n with
                                      | None => unit
                                      | Some x => F x
                                    end)
          with
          | 0 => Some h
          | S n => hlist_nth hs n
        end
    end.

End hlist.

Arguments HNil {_ _}.
Arguments HCons {_ _ _ _} _ _.
