Require Import List.
Require Import String.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Core.RelDec.
(*Require Import Injection. *)

Open Scope string_scope.
Import MonadNotation ListNotations.
Open Scope monad_scope.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Module FunNotation.

  Notation "f $ x" := (f x)
    (at level 99, x at level 99, right associativity, only parsing).

  Notation "'begin' e1 'end'" := ((e1))
    (at level 0, only parsing).

End FunNotation.
Import FunNotation.

Definition deprecated_uncurry A B C (f:A -> B -> C) (x:A * B) : C := let (a,b) := x in f a b.

#[deprecated(since = "8.13", note = "Use standard library.")]
Notation uncurry := deprecated_uncurry.

Definition deprecated_curry  {A B C} (f : A * B -> C) (a : A) (b : B) : C := f (a, b).

#[deprecated(since = "8.13", note = "Use standard library.")]
Notation curry := deprecated_curry.

Lemma deprecated_uncurry_curry : forall A B C (f : A -> B -> C) a b,
    curry (uncurry f) a b = f a b.
Proof.
  unfold curry, uncurry.
  reflexivity.
Qed.

#[deprecated(since = "8.13", note = "Use standard library.")]
Notation uncurry_curry := deprecated_uncurry_curry.

Lemma deprecated_curry_uncurry : forall A B C (f : A * B -> C) ab,
    uncurry (curry f) ab = f ab.
Proof.
  unfold uncurry, curry.
  destruct ab.
  reflexivity.
Qed.

#[deprecated(since = "8.13", note = "Use standard library.")]
Notation curry_uncurry := deprecated_curry_uncurry.

Fixpoint deprecated_zip A B (xs:list A) (ys:list B) : list (A * B) :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x::xs, y::ys => (x,y)::deprecated_zip xs ys
  end
.

#[deprecated(note = "Use List.combine instead.")]
Notation zip := deprecated_zip.

Fixpoint deprecated_unzip A B (xys:list (A * B)) : list A * list B :=
match xys with
| [] => ([], [])
| (x,y)::xys => let (xs,ys) := deprecated_unzip xys in (x::xs,y::ys)
end.

#[deprecated(note = "Use List.split instead.")]
Notation unzip := deprecated_unzip.

Definition sum_tot {A} (x:A + A) : A := match x with inl a => a | inr a => a end.

Definition forEach A B (xs:list A) (f:A -> B) : list B := map f xs.

Definition lsingleton {A} (x:A) : list A := [x].

Definition firstf {A B C} (f:A->C) (xy:A*B) : C*B :=
let (x,y) := xy in (f x, y).

Definition secondf {A B C} (f:B->C) (xy:A*B) : A*C :=
let (x,y) := xy in (x, f y).

Fixpoint update {K V} {kRealDec:RelDec (@eq K)} x v l : list (K * V) :=
match l with
| [] => [(x,v)]
| (y,w)::l' => if eq_dec x y then (x,v)::l' else (y,w)::update x v l'
end.

Definition updateMany {K V} {kRealDec:RelDec (@eq K)}
  (ups:list (K * V)) (init:list (K * V)) : list (K * V) :=
    fold_right (uncurry update) init ups.
