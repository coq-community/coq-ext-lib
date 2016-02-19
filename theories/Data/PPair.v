Require Import ExtLib.Core.RelDec.

Set Printing Universes.
Set Primitive Projections.
Set Universe Polymorphism.
Section pair.
  Polymorphic Universes i j.
  Variable (T : Type@{i}) (U : Type@{j}).

  Polymorphic Inductive ppair : Type@{max (i, j)} :=
  | pprod : T -> U -> ppair.

  Polymorphic Definition pfst (p : ppair) :=
    match p with
    | pprod t _ => t
    end.

  Polymorphic Definition psnd (p : ppair) :=
    match p with
    | pprod _ u => u
    end.

End pair.

Arguments ppair _ _.
Arguments pprod {_ _} _ _.
Arguments pfst {_ _} _.
Arguments psnd {_ _} _.

Section PProdEq.
  Polymorphic Universes i j.
  Context {T : Type@{i}} {U : Type@{j}}.
  Context {EDT : RelDec (@eq T)}.
  Context {EDU : RelDec (@eq U)}.
  Context {EDCT : RelDec_Correct EDT}.
  Context {EDCU : RelDec_Correct EDU}.

  Polymorphic Definition ppair_eqb (p1 p2 : ppair T U) : bool :=
    pfst p1 ?[ eq ] pfst p2 && psnd p1 ?[ eq ] psnd p2.

  (** Specialization for equality **)
  Global Polymorphic Instance RelDec_eq_ppair : RelDec (@eq (@ppair T U)) :=
  { rel_dec := ppair_eqb }.

  Global Polymorphic Instance RelDec_Correct_eq_ppair : RelDec_Correct RelDec_eq_ppair.
  Proof.
    constructor. intros p1 p2. destruct p1, p2. simpl.
    unfold ppair_eqb. simpl.
    rewrite Bool.andb_true_iff.
    repeat rewrite rel_dec_correct.
    split; intuition congruence.
  Qed.

End PProdEq.