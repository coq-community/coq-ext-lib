Set Implicit Arguments.
Set Strict Implicit.

Class EquivDec (T : Type) (equ : T -> T -> Prop) : Type :=
{ equiv_dec : T -> T -> bool }.

Class EquivDec_Correct T (equ : T -> T -> Prop) (ED : EquivDec equ) : Prop :=
{ equiv_dec_correct : forall x y : T, equiv_dec x y = true <-> equ x y }.

Definition eq_dec (T : Type) (ED : EquivDec (@eq T)) := equiv_dec.

(** Base Instances **)
Global Instance EquivDec_eq_unit : EquivDec (@eq unit) := 
{ equiv_dec := fun _ _ => true }.

Global Instance EquivDec_eq_bool : EquivDec (@eq bool) := 
{ equiv_dec := fun x y => match x , y with 
                            | true , true
                            | false , false => true
                            | _ , _=> false
                          end }.

Section PairParam.
  Variable T : Type.
  Variable eqT : T -> T -> Prop.
  Variable U : Type.
  Variable eqU : U -> U -> Prop.

  Variable EDT : EquivDec eqT.
  Variable EDU : EquivDec eqU.

  Global Instance EquivDec_equ_pair : EquivDec (fun x y => eqT (fst x) (fst y) /\ eqU (snd x) (snd y)) :=
  { equiv_dec := fun x y => 
    if equiv_dec (fst x) (fst y) then
      equiv_dec (snd x) (snd y)
    else false }.
End PairParam.