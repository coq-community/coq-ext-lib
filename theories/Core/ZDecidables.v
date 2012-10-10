Require Import ZArith.
Require Import ExtLib.Core.RelDec.

Set Implicit Arguments.
Set Strict Implicit.

Global Instance RelDec_zlt : RelDec (Z.lt) :=
{ rel_dec := Z.ltb }.

Global Instance RelDec_zle : RelDec (Z.le) :=
{ rel_dec := Z.leb }.

Global Instance RelDec_zgt : RelDec (Z.gt) :=
{ rel_dec := Z.gtb }.

Global Instance RelDec_zge : RelDec (Z.ge) :=
{ rel_dec := Z.geb }.

Global Instance RelDec_Correct_zlt : RelDec_Correct RelDec_zlt.
Proof.
  constructor. simpl. intros.
  generalize (Zlt_cases x y).
  destruct ((x <? y)%Z); intros; intuition; congruence.
Qed.

Global Instance RelDec_Correct_zle : RelDec_Correct RelDec_zle.
Proof.
  constructor. simpl. intros.
  generalize (Zle_cases x y).
  destruct ((x <=? y)%Z); intros; intuition; congruence.
Qed.

Global Instance RelDec_Correct_zgt : RelDec_Correct RelDec_zgt.
Proof.
  constructor. simpl. intros.
  generalize (Zgt_cases x y).
  destruct ((x >? y)%Z); intros; intuition; congruence.
Qed.

Global Instance RelDec_Correct_zge : RelDec_Correct RelDec_zge.
Proof.
  constructor. simpl. intros.
  generalize (Zge_cases x y).
  destruct ((x >=? y)%Z); intros; intuition; congruence.
Qed.
