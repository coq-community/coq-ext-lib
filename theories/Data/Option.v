Require Import Coq.Relations.Relations.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Data.Fun.

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

Section type.
  Variable T : Type.
  Variable tT : type T.

  Definition eqv_option rT (a b : option T) :=
    match a , b with
      | None , None => True
      | Some a , Some b => rT a b
      | _ , _ => False
    end.

  Global Instance type_option : type (option T) :=
  { equal := eqv_option equal 
  ; proper := fun x => match x with
                         | None => True
                         | Some y => proper y
                       end }.

  Variable tTOk : typeOk tT.

  Global Instance typeOk_option : typeOk type_option.
  Proof.
    constructor.
    { destruct x; destruct y; simpl; auto; try contradiction; intros.
      unfold proper in *. simpl in *.
      destruct tTOk.
      eapply only_proper in H. intuition. }
    { red. destruct x; simpl; auto. intro. eapply preflexive; [ | eapply H ]. eapply equiv_prefl; auto. }
    { red. destruct x; destruct y; simpl; auto. intros.
      destruct tTOk. apply equiv_sym. auto. }
    { red. destruct x; destruct y; destruct z; intros; try contradiction; auto.
      simpl in *. destruct tTOk.
      etransitivity; eauto. }
  Qed.

  Global Instance proper_Some : proper (@Some T).
  Proof. compute; auto. Qed.

  Global Instance proper_None : proper (@None T).
  Proof. compute; auto. Qed.

End type.

Require EquivDec.

Global Instance EqDec_option (T : Type) (EDT : EquivDec.EqDec T (@eq T)) : EquivDec.EqDec (option T) (@eq _).
Proof.
  red. unfold Equivalence.equiv, RelationClasses.complement. intros.
  change (x = y -> False) with (x <> y).
  decide equality. apply EDT.
Qed.
