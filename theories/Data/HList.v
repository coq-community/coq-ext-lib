Require Import List.
Require Import ExtLib.Structures.EqDep.

Set Implicit Arguments.
Set Strict Implicit.

Section hlist.
  Context {iT : Type}.
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

  Fixpoint hlist_app ll lr : hlist ll -> hlist lr -> hlist (ll ++ lr) :=
    match ll with
      | nil => fun _ x => x
      | _ :: _ => fun l r => Hcons (hlist_hd l) (hlist_app (hlist_tl l) r)
    end.

  Lemma hlist_eta : forall ls (h : hlist ls),
    h = match ls as ls return hlist ls -> hlist ls with
          | nil => fun _ => Hnil
          | a :: b => fun h => Hcons (hlist_hd h) (hlist_tl h)
        end h.
  Proof.
    intros. destruct h; auto.
  Qed.

  Lemma hlist_nil_eta : forall (h : hlist nil), h = Hnil.
  Proof.
    intros; rewrite (hlist_eta h); reflexivity.
  Qed.

  Lemma hlist_cons_eta : forall a b (h : hlist (a :: b)),
    h = Hcons (hlist_hd h) (hlist_tl h).
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

  Fixpoint hlist_nth ls (h : hlist ls) (n : nat) :
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
  
  Require Import ExtLib.Data.ListNth.
  Definition cast1 T (l l' : list T) n v := 
    (fun pf : nth_error l n = Some v => eq_sym (nth_error_weaken l' l n pf)).
  Definition cast2 T (l l' : list T) n :=
    (fun pf : nth_error l n = None => eq_sym (@nth_error_app_R _ l l' _ (nth_error_length_ge _ _ pf))).

  Require Import ExtLib.Tactics.EqDep.
  Require Import ExtLib.Data.Option.  

  Theorem hlist_nth_hlist_app (e : EqDec iT (@eq iT)) : forall l l' (h : hlist l) (h' : hlist l') n,
    hlist_nth (hlist_app h h') n = 
    match nth_error l n as k
      return nth_error l n = k ->
      match nth_error (l ++ l') n with
        | None => unit
        | Some t => F t
      end
      with
      | Some _ => fun pf => 
        match cast1 _ _ _ pf in _ = z ,
          eq_sym pf in _ = w 
          return match w with
                   | None => unit
                   | Some t => F t
                 end ->
          match z with
            | None => unit
            | Some t => F t
          end
          with
          | eq_refl , eq_refl => fun x => x
        end (hlist_nth h n)
      | None => fun pf => 
        match cast2 _ _ _ pf in _ = z 
          return match z with
                   | Some t => F t
                   | None => unit
                 end
          with 
          | eq_refl => hlist_nth h' (n - length l)
        end
    end eq_refl.
  Proof.
    induction h; simpl; intros.
    { destruct n; simpl in *; uip_all; simpl in *; uip_all; reflexivity. }
    { destruct n; simpl.
      { uip_all. simpl in e0. unfold value in *. uip_all; reflexivity. }
      { rewrite IHh. clear - e.
        repeat match goal with
                 | [ |- context [ @eq_refl _ ?X ] ] =>
                   generalize (@eq_refl _ X)
               end.
        generalize (cast1 ls l' n).
        generalize (cast1 (l :: ls) l' (S n)).
        generalize (cast2 ls l' n).
        generalize (cast2 (l :: ls) l' (S n)).
        generalize (hlist_nth h n).
        simpl in *.
        pattern (nth_error ls n). 
        destruct (nth_error ls n); simpl; intros.
        { clear - e. uip_all. clear - e. 
          rewrite (UIP_equal e0 e5). reflexivity. }
        { uip_all. clear - e.
          rewrite (UIP_equal e5 e6). reflexivity. } } }
  Qed.

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

Arguments hlist_map {_ _ _} _ {_} _.

