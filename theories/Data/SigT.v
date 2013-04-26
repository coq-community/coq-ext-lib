Require Import EquivDec.
Require Import ExtLib.Structures.EqDep.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.EqDep.

Set Implicit Arguments.
Set Strict Implicit.

Global Instance Injective_existT T (F : T -> Type) (ED : EqDec _ (@eq T)) a b d 
  : Injective (existT F a b = existT F a d) | 1 :=
  { result := b = d }.
abstract (eauto using inj_pair2).
Defined.

Global Instance Injective_existT_dif T (F : T -> Type) (ED : EqDec _ (@eq T)) a b c d 
  : Injective (existT F a b = existT F c d) | 2 :=
  { result := exists pf : c = a, 
    b = match pf in _ = t return F t with
          | eq_refl => d
        end }.
abstract (inversion 1; subst; exists eq_refl; auto).
Defined.
