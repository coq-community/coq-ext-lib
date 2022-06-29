Require Coq.Classes.EquivDec.
Require Import ExtLib.Structures.EqDep.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.EqDep.

Set Implicit Arguments.
Set Strict Implicit.
Set Printing Universes.

(** For backwards compatibility with hint locality attributes. *)
Set Warnings "-unsupported-attributes".

Section injective.
  Variable T : Type.
  Variable F : T -> Type.
  Variable ED : EquivDec.EqDec _ (@eq T).

  Global Instance Injective_existT a b d
    : Injective (existT F a b = existT F a d) | 1.
  refine {| result := b = d |}.
  abstract (eauto using inj_pair2).
  Defined.

  Global Instance Injective_existT_dif a b c d
  : Injective (existT F a b = existT F c d) | 2.
  refine {| result := exists pf : c = a,
            b = match pf in _ = t return F t with
                  | eq_refl => d
                end |}.
  abstract (inversion 1; subst; exists eq_refl; auto).
  Defined.
End injective.

Lemma eq_sigT_rw
: forall T U F (a b : T) (pf : a = b) s,
    match pf in _ = x return @sigT U (F x) with
    | eq_refl => s
    end =
    @existT U (F b) (projT1 s)
            match pf in _ = x return F x (projT1 s) with
            | eq_refl => (projT2 s)
            end.
Proof. destruct pf. destruct s; reflexivity. Qed.

#[global]
Hint Rewrite eq_sigT_rw : eq_rw.
