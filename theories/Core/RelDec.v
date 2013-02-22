Require Import Tactics.Consider.
Require Import Bool.

Set Implicit Arguments.
Set Strict Implicit.

Class RelDec (T : Type) (equ : T -> T -> Prop) : Type :=
{ rel_dec : T -> T -> bool }.

Arguments rel_dec {_} {equ} {_} _ _.

Class RelDec_Correct T (equ : T -> T -> Prop) (ED : RelDec equ) : Prop :=
{ rel_dec_correct : forall x y : T, rel_dec x y = true <-> equ x y }.

Notation "a ?[ r  ]  b" := (@rel_dec _ r _ a b) (at level 30, b at next level).

Definition eq_dec {T : Type} {ED : RelDec (@eq T)} := rel_dec.

Section neg_rel_dec_correct.
  Context {T} {R:T -> T -> Prop} {RD:RelDec R} {RDC:RelDec_Correct RD}.

  Definition neg_rel_dec_correct : forall {x y}, ~R x y <-> rel_dec x y = false.
  Proof. intros x y. destruct (bool_dec (rel_dec x y) true) ; constructor ; intros ;
    repeat
      match goal with
      | [ |- ~ _ ] => unfold not ; intros
      | [ H1 : ?P, H2 : ~?P |- _ ] => specialize (H2 H1) ; contradiction
      | [ H1 : ?P = true, H2 : ?P = false |- _ ] => rewrite H1 in H2 ; discriminate
      | [ H1 : ?P <> true |- ?P = false ] => apply not_true_is_false ; exact H1
      | [ H1 : ?rel_dec ?a ?b = true, H2 : ~?R ?a ?b |- _ ] =>
          apply rel_dec_correct in H1
      | [ H1 : ?rel_dec ?a ?b = false, H2 : ?R ?a ?b |- _ ] =>
          apply rel_dec_correct in H2
      end.
  Qed.
End neg_rel_dec_correct.

Section rel_dec_p.
  Context {T} {R:T -> T -> Prop} {RD:RelDec R} {RDC:RelDec_Correct RD}.

  Definition rel_dec_p (x:T) (y:T) : {R x y} + {~R x y}.
  Proof. destruct (bool_dec (rel_dec x y) true) as [H | H].
    apply rel_dec_correct in H ; eauto.
    apply not_true_is_false in H ; apply neg_rel_dec_correct in H ; eauto.
  Qed.

  Definition neg_rel_dec_p (x:T) (y:T) : {~R x y} + {R x y}.
  Proof. destruct (rel_dec_p x y) ; [ right | left ] ; auto. Qed.
End rel_dec_p.

Global Instance Reflect_RelDec_Correct T (equ : T -> T -> Prop) (ED : RelDec equ) {_ : RelDec_Correct ED} x y : Reflect (rel_dec x y) (equ x y) (~equ x y).
Proof.
  apply iff_to_reflect.
  apply rel_dec_correct.
Qed.

Theorem rel_dec_eq_true : forall T (eqt : T -> T -> Prop) (r : RelDec eqt) (rc : RelDec_Correct r) x y,
  eqt x y -> rel_dec x y = true.
Proof.
  intros. consider (rel_dec x y); auto.
Qed.

Theorem rel_dec_neq_false : forall T (eqt : T -> T -> Prop) (r : RelDec eqt) (rc : RelDec_Correct r) x y,
  ~eqt x y -> rel_dec x y = false.
Proof.
  intros. consider (rel_dec x y); auto.
  intros; exfalso; auto.
Qed.

(** Base Instances **)
Global Instance RelDec_eq_unit : RelDec (@eq unit) :=
{ rel_dec := fun _ _ => true }.
Global Instance RelDec_Correct_eq_unit : RelDec_Correct RelDec_eq_unit.
  constructor. destruct x; destruct y; auto; simpl. intuition.
Qed.

Global Instance RelDec_eq_bool : RelDec (@eq bool) :=
{ rel_dec := fun x y => match x , y with
                          | true , true
                          | false , false => true
                          | _ , _=> false
                        end }.
Global Instance RelDec_Correct_eq_bool : RelDec_Correct RelDec_eq_bool.
  constructor. destruct x; destruct y; auto; simpl; intuition.
Qed.

Require Import Arith.
Global Instance RelDec_eq_nat : RelDec (@eq nat) :=
{ rel_dec := EqNat.beq_nat }.


Section PairParam.
  Variable T : Type.
  Variable eqT : T -> T -> Prop.
  Variable U : Type.
  Variable eqU : U -> U -> Prop.

  Variable EDT : RelDec eqT.
  Variable EDU : RelDec eqU.

  Global Instance RelDec_equ_pair : RelDec (fun x y => eqT (fst x) (fst y) /\ eqU (snd x) (snd y)) :=
  { rel_dec := fun x y =>
    if rel_dec (fst x) (fst y) then
      rel_dec (snd x) (snd y)
    else false }.

  Variable EDCT : RelDec_Correct EDT.
  Variable EDCU : RelDec_Correct EDU.

  Global Instance RelDec_Correct_equ_pair : RelDec_Correct RelDec_equ_pair.
  Proof.
    constructor; destruct x; destruct y; split; simpl in *; intros;
      repeat match goal with
               | [ H : context [ rel_dec ?X ?Y ] |- _ ] =>
                 consider (rel_dec X Y); intros; subst
               | [ |- context [ rel_dec ?X ?Y ] ] =>
                 consider (rel_dec X Y); intros; subst
             end; intuition.
  Qed.
End PairParam.

Section PairEq.
  Variable T : Type.
  Variable U : Type.

  Variable EDT : RelDec (@eq T).
  Variable EDU : RelDec (@eq U).

  (** Specialization for equality **)
  Global Instance RelDec_eq_pair : RelDec (@eq (T * U)) :=
  { rel_dec := fun x y =>
    if rel_dec (fst x) (fst y) then
      rel_dec (snd x) (snd y)
    else false }.

  Variable EDCT : RelDec_Correct EDT.
  Variable EDCU : RelDec_Correct EDU.

  Global Instance RelDec_Correct_eq_pair : RelDec_Correct RelDec_eq_pair.
  Proof.
    constructor; destruct x; destruct y; split; simpl in *; intros;
      repeat match goal with
               | [ H : context [ rel_dec ?X ?Y ] |- _ ] =>
                 consider (rel_dec X Y); intros; subst
               | [ |- context [ rel_dec ?X ?Y ] ] =>
                 consider (rel_dec X Y); intros; subst
             end; congruence.
  Qed.
End PairEq.

Section OptionEq.
  Variable T : Type.
  Variable EDT : RelDec (@eq T).

  (** Specialization for equality **)
  Global Instance RelDec_eq_option : RelDec (@eq (option T)) :=
  { rel_dec := fun x y =>
    match x , y with
      | None , None => true
      | Some x , Some y => eq_dec x y
      | _ , _ => false
    end }.

  Variable EDCT : RelDec_Correct EDT.

  Global Instance RelDec_Correct_eq_option : RelDec_Correct RelDec_eq_option.
  Proof.
    constructor; destruct x; destruct y; split; simpl in *; intros; try congruence;
      f_equal; try match goal with
                     | [ H : context [ eq_dec ?X ?Y ] |- _ ] =>
                       consider (eq_dec X Y)
                     | [ |- context [ eq_dec ?X ?Y ] ] =>
                       consider (eq_dec X Y)
                   end; auto; congruence.
  Qed.

End OptionEq.

Section SumEq.
  Variable T : Type.
  Variable U : Type.

  Variable EDT : RelDec (@eq T).
  Variable EDU : RelDec (@eq U).

  (** Specialization for equality **)
  Global Instance RelDec_eq_sum : RelDec (@eq (T + U)) :=
  { rel_dec := fun x y =>
    match x , y with
      | inl x , inl y => eq_dec x y
      | inr x , inr y => eq_dec x y
      | _ , _ => false
    end }.

  Variable EDCT : RelDec_Correct EDT.
  Variable EDCU : RelDec_Correct EDU.

  Global Instance RelDec_Correct_eq_sum : RelDec_Correct RelDec_eq_sum.
  Proof.
    constructor; destruct x; destruct y; split; simpl in *; intros; try congruence;
      f_equal; try match goal with
                     | [ H : context [ eq_dec ?X ?Y ] |- _ ] =>
                       consider (eq_dec X Y)
                     | [ |- context [ eq_dec ?X ?Y ] ] =>
                       consider (eq_dec X Y)
                   end; auto; congruence.
  Qed.

End SumEq.

Section ListEq.
  Variable T : Type.
  Variable EDT : RelDec (@eq T).

  Fixpoint list_eq (ls rs : list T) : bool :=
    match ls , rs with
      | nil , nil => true
      | cons l ls , cons r rs =>
        if l ?[ eq ] r then list_eq ls rs else false
      | _ , _ => false
    end.

  (** Specialization for equality **)
  Global Instance RelDec_eq_list : RelDec (@eq (list T)) :=
  { rel_dec := list_eq }.

  Variable EDCT : RelDec_Correct EDT.

  Global Instance RelDec_Correct_eq_list : RelDec_Correct RelDec_eq_list.
  Proof.
    constructor; induction x; destruct y; split; simpl in *; intros;
      repeat match goal with
               | [ H : context [ rel_dec ?X ?Y ] |- _ ] =>
                 consider (rel_dec X Y); intros; subst
               | [ |- context [ rel_dec ?X ?Y ] ] =>
                 consider (rel_dec X Y); intros; subst
             end; intuition; try congruence.
    eapply IHx in H0. subst; auto. eapply IHx. inversion H; eauto.
  Qed.

End ListEq.
