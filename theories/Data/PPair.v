Require Import ExtLib.Core.RelDec.

Set Printing Universes.
Set Primitive Projections.

Section pair.
  Polymorphic Universes i j.
  Context {T : Type@{i}} {U : Type@{j}}.

  Polymorphic Inductive ppair : Type :=
  | pprod : T -> U -> ppair.

  Polymorphic Definition fst (p : ppair) :=
    match p with
    | pprod t _ => t
    end.

  Polymorphic Definition snd (p : ppair) :=
    match p with
    | pprod _ u => u
    end.

End pair.

Arguments ppair _ _.
Arguments fst {_ _} _.
Arguments snd {_ _} _.

Section PProdEq.
  Context {T U : Type}.
  Context {EDT : RelDec (@eq T)}.
  Context {EDU : RelDec (@eq U)}.
  Context {EDCT : RelDec_Correct EDT}.
  Context {EDCU : RelDec_Correct EDU}.

  Definition ppair_eqb (p1 p2 : @ppair T U) : bool :=
    fst p1 ?[ eq ] fst p2 && snd p1 ?[ eq ] snd p2.

  (** Specialization for equality **)
  Global Instance RelDec_eq_ppair : RelDec (@eq (@ppair T U)) :=
  { rel_dec := ppair_eqb }.

  Global Instance RelDec_Correct_eq_ppair : RelDec_Correct RelDec_eq_ppair.
  Proof.
    constructor. intros p1 p2. destruct p1, p2. simpl.
    unfold ppair_eqb. simpl.
    rewrite Bool.andb_true_iff.
    repeat rewrite rel_dec_correct.
    split; intuition congruence.
  Qed.

End PProdEq.