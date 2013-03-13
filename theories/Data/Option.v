Require Import Coq.Relations.Relations.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Proper.

Set Implicit Arguments.
Set Strict Implicit.

Global Instance Foldable_option {T} : Foldable (option T) T :=
  fun _ f d v => 
    match v with
      | None => d
      | Some x => f x d
    end.

Global Instance Traversable_option : Traversable option :=
{| mapT := fun F _ _ _ f o =>
  match o with
    | None => pure None
    | Some o => ap (pure (@Some _)) (f o)
  end
|}.

Section proper.
  Context {T : Type} {rT : relation T} {P : Proper rT}.

  Definition eqv_option (a b : option T) :=
    match a , b with
      | None , None => True
      | Some a , Some b => rT a b
      | _ , _ => False
    end.
  
  Global Instance Proper_option : Proper eqv_option :=
  { proper := fun o => match o with
                         | None => True
                         | Some x => proper x
                       end }.

  Global Instance PReflexive_eqv_option (R : PReflexive rT) : PReflexive eqv_option.
  Proof. intro; destruct x; simpl; eauto. Qed.

  Global Instance PSymmetric_eqv_option (R : PSymmetric rT) : PSymmetric eqv_option.
  Proof. intro; destruct x; destruct y; simpl; eauto. Qed.

  Global Instance PTransitive_eqv_option (R : PTransitive rT) : PTransitive eqv_option.
  Proof.
    intro; destruct x; destruct y; destruct z; simpl; eauto; intros; try contradiction. 
  Qed.
  
End proper.