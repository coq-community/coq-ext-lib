Require Import Coq.Lists.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Generic.Func.
(** This module gives a representation of inductive types **)

Set Implicit Arguments.
Set Strict Implicit.

Inductive itype (ps : list Type) : Type :=
| Inj : Type -> itype ps
| Rec : hlist (fun x => x) ps -> itype ps
| Sum : itype ps -> itype ps -> itype ps
| Prod : itype ps -> itype ps -> itype ps
| Sig : forall T : Type, (T -> itype ps) -> itype ps
| Get : forall T : Type, member T ps -> (T -> itype ps) -> itype ps.

Fixpoint itypeD (ps : list Type) (i : itype ps) {struct i}
: (asFunc ps Type) -> asFunc ps Type :=
  match i return (asFunc ps Type) -> asFunc ps Type with
    | Get T pf f => fun F => @get ps _ _ pf (fun x => itypeD (f x) F)
    | Inj T => fun _ => const T
    | Rec h => fun F => F
    | Sig t f => fun F =>
                   @under _ _ (fun App => @sigT t (fun x' => App _ (itypeD (f x') F)))
    | Sum a b => fun F => combine sum ps (itypeD a F) (itypeD b F)
    | Prod a b => fun F => combine prod ps (itypeD a F) (itypeD b F)
  end%type.

(** Some Examples **)
(*
(** Vectors **)
Definition rfvec T : itype ((nat : Type) :: nil) :=
  @Get ((nat : Type) :: @nil Type) nat (MZ _ _)
       (fun x =>
          match x with
            | 0 => Inj _ unit
            | S n => Prod (Inj _ T) (Rec (Hcons n Hnil))
          end).

Definition rfvec' T : itype ((nat : Type) :: nil) :=
  Sum (@Get ((nat : Type) :: @nil Type) nat (MZ _ _)
            (fun x => Inj _ (x = 0)))
      (@Get ((nat : Type) :: @nil Type) nat (MZ _ _)
            (fun x => Sig (fun n : nat => Prod (Inj _ T) (Prod (Rec (Hcons n Hnil)) (Inj _ (x = S n)))))).
Eval simpl in fun T => itypeD (rfvec' T).


(** Nats **)
Definition rfnat := Sum (Inj nil unit) (Rec Hnil).

Definition inat :=
  Eval simpl in itypeD rfnat.

Definition i0 : inat :=
  @existT bool (fun x' => itypeD nil (if x' then Inj nil unit else Rec nil Hnil)
  nat) true tt.

Definition iS : nat -> inat :=
  @existT bool (fun x' => itypeD nil (if x' then Inj nil unit else Rec nil Hnil)
  nat) false.

Definition fold (i : nat) : inat :=
  match i with
    | 0 => i0
    | S n => iS n
  end.

Definition unfold (i : inat) : nat :=
  match i with
    | existT true _ => 0
    | existT false x => S x
  end.

Theorem fold_unfold : forall x, fold (unfold x) = x.
Proof.
  destruct x; simpl.
  destruct x; simpl.
  { simpl in *. destruct i. reflexivity. }
  { simpl in *. reflexivity. }
Qed.

Theorem unfold_fold : forall x, unfold (fold x) = x.
Proof.
  destruct x; simpl; reflexivity.
Qed.
*)