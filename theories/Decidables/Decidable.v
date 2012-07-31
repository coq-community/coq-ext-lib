Set Implicit Arguments.
Set Strict Implicit.

Class RelDec (T : Type) (equ : T -> T -> Prop) : Type :=
{ rel_dec : T -> T -> bool }.

Class RelDec_Correct T (equ : T -> T -> Prop) (ED : RelDec equ) : Prop :=
{ rel_dec_correct : forall x y : T, rel_dec x y = true <-> equ x y }.

Definition eq_dec (T : Type) (ED : RelDec (@eq T)) := rel_dec.

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