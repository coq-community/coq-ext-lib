Require Import ExtLib.Data.POption.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.Injection.

Set Universe Polymorphism.

Section poly.
  Polymorphic Universes Uv.

Record OneOf (ts : pmap Type@{Uv}) : Type@{Uv} := mkOneOf
{ index : positive
; value : match pmap_lookup_key ts index with
          | pNone => Empty_set
          | pSome T => T
          end
}.

Definition Into {ts} {T : Type} (n : positive)
           (pf : pmap_lookup_key ts n = pSome T)
: T -> OneOf ts :=
  match pf in _ = X return match X with
                           | pSome T => T
                           | pNone => Empty_set
                           end -> OneOf ts
  with
  | eq_refl => @mkOneOf ts n
  end.

Fixpoint asNth' {ts : pmap Type} (p p' : positive)
: match pmap_lookup_key ts p' with
    | pNone => Empty_set
    | pSome T => T
  end -> poption (match pmap_lookup_key ts p with
                   | pNone => Empty_set
                   | pSome T => T
                 end) :=
  match p as p , p' as p'
        return match pmap_lookup_key ts p' with
                 | pNone => Empty_set
                 | pSome T => T
               end -> poption (match pmap_lookup_key ts p with
                               | pNone => Empty_set
                               | pSome T => T
                               end)
  with
    | xH , xH => pSome
    | xI p , xI p' => asNth' p p'
    | xO p , xO p' => asNth' p p'
    | _ , _ => fun _ => pNone
  end.

Definition asNth {ts : pmap Type} (p : positive) (oe : OneOf ts)
: poption (match pmap_lookup_key ts p with
          | pNone => Empty_set
          | pSome T => T
          end) :=
  @asNth' ts p oe.(index ts) oe.(value ts).

Definition OutOf {ts} {T : Type} (n : positive)
           (pf : pmap_lookup_key ts n = pSome T)
: OneOf ts -> poption T :=
  match pf in _ = X
        return OneOf ts -> poption match X return Type@{Uv} with
                                   | pNone => Empty_set
                                   | pSome T => T
                                   end
  with
  | eq_refl => @asNth ts n
  end.

Lemma asNth'_get_lookup : forall p ts v, asNth' (ts:=ts) p p v = pSome v.
Proof.
  induction p; simpl; intros; auto.
Qed.

Theorem Outof_Into : forall ts T p pf v,
    @OutOf ts T p pf (@Into ts T p pf v) = pSome v.
Proof using.
  unfold OutOf, Into.
  intros.
  repeat rewrite (eq_Arr_eq pf).
  repeat rewrite (eq_Const_eq pf).
  repeat rewrite (eq_Const_eq (eq_sym pf)).
  unfold asNth. simpl.
  rewrite asNth'_get_lookup.
  { generalize dependent (pmap_lookup_key ts p).
    intros. subst. reflexivity. }
Qed.

Theorem asNth_eq
: forall ts p oe v,
    @asNth ts p oe = pSome v ->
    oe = {| index := p ; value := v |}.
Proof.
  unfold asNth.
  destruct oe; simpl.
  revert value0. revert index0. revert ts.
  induction p; destruct index0; simpl; intros;
  solve [ congruence | eapply IHp in H; inversion H; clear H IHp; subst; auto ].
Qed.

Section elim.
  Context {T : Type}.
  Variable F : T -> Type.

  Fixpoint pmap_elim (R : Type) (ts : pmap T) : Type :=
    match ts with
    | Empty => R
    | Branch pNone l r => pmap_elim (pmap_elim R r) l
    | Branch (pSome x) l r => F x -> pmap_elim (pmap_elim R r) l
    end.
End elim.

Definition OneOf_Empty (f : OneOf Empty) : False.
Proof.
  destruct f. rewrite pmap_lookup_key_Empty in *.
  intuition congruence.
Defined.



Global Instance Injective_OneOf m i1 i2 v1 v2
: Injective (@eq (OneOf m)
                 {| index := i1 ; value := v1 |}
                 {| index := i2 ; value := v2 |}) :=
{ result := exists pf : i2 = i1,
    v1 = match pf in _ = T return match pmap_lookup_key m T return Type@{Uv} with
                                  | pNone => Empty_set
                                  | pSome T => T
                                  end with
         | eq_refl => v2
         end
; injection :=
    fun H =>
      match H in _ = h
            return exists pf : index _ h = i1 ,
          v1 = match
            pf in (_ = T)
            return
            match pmap_lookup_key m T return Type@{Uv} with
            | pSome T0 => T0
            | pNone => Empty_set
            end
          with
          | eq_refl => value _ h
          end
      with
      | eq_refl => @ex_intro _ _ eq_refl eq_refl
      end
}.

End poly.
