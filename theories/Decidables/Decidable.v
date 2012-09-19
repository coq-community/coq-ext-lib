Require Import Tactics.Consider.

Set Implicit Arguments.
Set Strict Implicit.

Class RelDec (T : Type) (equ : T -> T -> Prop) : Type :=
{ rel_dec : T -> T -> bool }.

Class RelDec_Correct T (equ : T -> T -> Prop) (ED : RelDec equ) : Prop :=
{ rel_dec_correct : forall x y : T, rel_dec x y = true <-> equ x y }.

Definition eq_dec {T : Type} {ED : RelDec (@eq T)} := rel_dec.

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
End PairEq.
