Require Import Coq.Lists.List.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Data.Nat.

Set Implicit Arguments.
Set Strict Implicit.

Section AllB.
  Variable T : Type.
  Variable p : T -> bool.

  Fixpoint allb (ls : list T) : bool :=
    match ls with
      | nil => true
      | l :: ls =>
        if p l then allb ls else false
    end.

  Fixpoint anyb (ls : list T) : bool :=
    match ls with
      | nil => false
      | l :: ls =>
        if p l then true else anyb ls
    end.
End AllB.

Global Instance Foldable_list {T} : Foldable (list T) T :=
  fun _ f x ls => fold_left (fun x y => f y x) ls x.

Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Applicative.

Global Instance Traversable_list : Traversable list :=
{ mapT := fun F _ A B f =>
  List.fold_right (fun x acc => ap (ap (pure (@cons B)) (f x)) acc) (pure nil)
}.

Global Instance Monad_list : Monad list :=
{ ret  := fun _ x => x :: nil
; bind := fun _ _ x f =>
  List.fold_right (fun x acc => f x ++ acc) nil x
}.


Section list.
  Inductive R_list_len {T} : list T -> list T -> Prop :=
  | R_l_len : forall n m, length n < length m -> R_list_len n m.

  Theorem wf_R_list_len T : well_founded (@R_list_len T).
  Proof.
    constructor. intros.
    refine (@Fix _ _ wf_R_lt (fun n : nat => forall ls : list T, n = length ls -> Acc R_list_len ls)
      (fun x rec ls pfls => Acc_intro _ _)
      _ _ refl_equal).
    refine (
      match ls as ls return x = length ls -> forall z : list T, R_list_len z ls -> Acc R_list_len z with
        | nil => fun (pfls : x = 0) z pf => _
        | cons l ls => fun pfls z pf =>
          rec _ (match pf in R_list_len xs ys return x = length ys -> R_nat_lt (length xs) x with
                   | R_l_len n m pf' => fun pf_eq => match eq_sym pf_eq in _ = x return R_nat_lt (length n) x with
                                                     | refl_equal => R_lt pf'
                                                   end
                 end pfls) _ eq_refl
      end pfls).
    clear - pf; abstract (inversion pf; subst; simpl in *; inversion H).
  Defined.
End list.
