Require Import Coq.Program.Syntax.
Require Import List.
Require Import String.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Folds.
Require Import ExtLib.Core.RelDec.
Require Import Injection.

Open Scope string_scope.
Import MonadNotation.
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

Definition compose A B C (g:B -> C) (f:A -> B) (x:A) : C := g (f x).

Definition uncurry A B C (f:A -> B -> C) (x:A * B) : C := let (a,b) := x in f a b.

Definition const A B (x:B) : A -> B := fun _ => x.

Fixpoint zip A B (xs:list A) (ys:list B) : list (A * B) :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x::xs, y::ys => (x,y)::zip xs ys
  end
.

Fixpoint unzip A B (xys:list (A * B)) : list A * list B :=
match xys with
| [] => ([], [])
| (x,y)::xys => let (xs,ys) := unzip xys in (x::xs,y::ys)
end.

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


Section monad.
  Context {m} {mMonad:Monad m}.

  Definition forEachM A {B} (xs:list A) (f:A -> m B) : m (list B) := mapM f xs.

  Definition firstfM {A B C} (fM:A -> m C) (xy:A*B) : m (C*B) :=
  let (x,y) := xy in x' <- fM x ;; ret (x', y)
  .

  Definition secondfM {A B C} (fM:B -> m C) (xy:A*B) : m (A*C) :=
  let (x,y) := xy in y' <- fM y ;; ret (x, y')
  .

End monad.

Section failure.
  Context {m} {mMonad:Monad m}.
  Context {e} {mMonadExc:MonadExc e m} {eInjection:Injection string e}.

  Definition failMsg {A} s : m A := raise (inject s).

  Definition lfirst A (l:list A) : m A :=
  match l with
  | [] => failMsg "lfirst of empty list"
  | x::_ => ret x
  end.

  Definition lrest A (l:list A) : m (list A) :=
  match l with
  | [] => failMsg "lrest of empty list"
  | _::xs => ret xs
  end .

  Fixpoint lookup K V {kRealDec:RelDec (@eq K)} (x:K) (l:list (K*V)) : m V :=
  match l with
  | [] => failMsg "lookup not in list"
  | (y,w)::l' => if eq_dec x y then ret w else lookup x l'
  end.

End failure.

