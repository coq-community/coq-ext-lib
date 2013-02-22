Require Import List.
Require Import Bool.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Consider.

Set Implicit Arguments.
Set Strict Implicit.

Class Logic (P : Type) : Type :=
{ Tr : P
; Fa : P
; And : P -> P -> P
; Or : P -> P -> P
; Impl : P -> P -> P
}.

(** TODO: This doesn't handle substructural logics because of the
 **       quantification over G in all the laws.
 **)
Class LogicLaws (P : Type) (L : Logic P) : Type :=
{ (** Entails P Q ==> P |- Q **)
  Entails : list P -> P -> Prop
; Assumption : forall G P, In P G -> Entails G P
; Tr_True : forall G, Entails G Tr
; Fa_False : forall G, Entails (Fa :: nil) G

; ImplI : forall G P Q, Entails (P :: G) Q -> Entails G (Impl P Q)
; ImplE : forall G P Q, Entails (P :: Impl P Q :: G) Q

; AndI : forall G P Q, Entails G P -> Entails G Q -> Entails G (And P Q)
; AndEL : forall G P Q, Entails G (And P Q) -> Entails G P
; AndER : forall G P Q, Entails G (And P Q) -> Entails G Q

; OrIL : forall G P Q, Entails G P -> Entails G (Or P Q)
; OrIR : forall G P Q, Entails G Q -> Entails G (Or P Q)
; OrE : forall G P Q R, Entails (P :: G) R -> Entails (Q :: G) R -> Entails (Or P Q :: G) R
}.

Hint Resolve Tr_True Fa_False ImplI ImplE AndI AndEL AndER OrIL OrIR OrE : logic.

Class Quant (P : Type) : Type :=
{ All : forall (T : Type), (T -> P) -> P
; Ex  : forall (T : Type), (T -> P) -> P
}.

Class QuantLaws P (Q: Quant P) (L : Logic P) (LL : LogicLaws L) : Type :=
{ AllI : forall T G (Pr : T -> P), Entails G (All Pr) -> forall x, Entails G (Pr x)
; AllE : forall T G (Pr : T -> P), (forall x, Entails G (Pr x)) -> Entails G (All Pr)

; ExI : forall T G (Pr : T -> P), Entails G (All Pr) -> exists x, Entails G (Pr x)
; ExE : forall T G (Pr : T -> P), (exists x, Entails G (Pr x)) -> Entails G (All Pr)
}.

(** Automation **)
Section PropLogic.
  Variable P : Type.
  Variable L : Logic P.

  Inductive prop_exp : Type :=
  | PTr
  | PFa 
  | PAnd  : prop_exp -> prop_exp -> prop_exp
  | POr   : prop_exp -> prop_exp -> prop_exp
  | PImpl : prop_exp -> prop_exp -> prop_exp.

  Fixpoint pdenote (p : prop_exp) : P :=
    match p with
      | PTr => Tr
      | PFa => Fa
      | PAnd l r => And (pdenote l) (pdenote r)
      | POr l r => Or (pdenote l) (pdenote r)
      | PImpl l r => Impl (pdenote l) (pdenote r)
    end.

  Fixpoint eq_prop_exp (p q : prop_exp) : bool :=
    match p , q with
      | PTr , PTr 
      | PFa , PFa => true
      | PAnd p' q' , PAnd p'' q''
      | POr p' q' , POr p'' q''
      | PImpl p' q' , PImpl p'' q'' => eq_prop_exp p' p'' && eq_prop_exp q' q''
      | _ , _ => false
    end.

  Global Instance RelDec_eq_prop_exp : RelDec (@eq prop_exp) :=
  { rel_dec := eq_prop_exp }.

  Global Instance RelDecOk_eq_prop_exp : RelDec_Correct RelDec_eq_prop_exp.
  Proof.
    constructor. induction x; destruct y; simpl in *; firstorder; 
    repeat match goal with
             | [ H : _ && _ = true |- _ ] => apply andb_true_iff in H; destruct H
             | [ |- _ && _ = true ] => apply andb_true_iff
             | [ H : forall x, _ |- _ ] => solve [ eapply H; eauto ]
             | [ |- ?X _ _ = ?X _ _ ] => f_equal 
             | [ H : ?X _ _ = ?X _ _ |- _ ] => (inversion H; clear H; subst); []
             | [ |- _ ] => progress intuition
           end; try congruence.
  Qed.

  Fixpoint find (p : prop_exp) (g : list prop_exp) : bool :=
    match g with
      | nil => false
      | a :: b => 
        if a ?[ eq ] p then true else find p b
    end.

  Fixpoint rtauto (g : list prop_exp) (p : prop_exp) : bool :=
    match p with
      | PTr => true
      | PFa => find p g
      | PAnd l r => rtauto g l && rtauto g r
      | POr l r => rtauto g l || rtauto g r
      | PImpl l r => find p g || find r g
    end.

  Variable LL : LogicLaws L.

  Lemma find_In : forall p g,
    find p g = true -> In p g.
  Proof.
    Opaque rel_dec.
    induction g; simpl in *; intros; try congruence.
    consider (a ?[ eq ] p); intros; subst.
    left. reflexivity. right; auto.
  Qed.

  Theorem find_sound : forall p g,
    find p g = true ->
    Entails (map pdenote g) (pdenote p).
  Proof.
    intros. eapply find_In in H.
    eapply Assumption. clear - H.
    induction g; simpl in *; auto.
    destruct H. subst; auto.
    right; auto.
  Qed.

  Lemma pdenote_In : forall g p, 
    In p g -> In (pdenote p) (map pdenote g).
  Proof.
    clear. induction g; simpl in *; intros; auto.
    destruct H; subst; auto.
  Qed.
    
  Theorem rtauto_sound : forall p g, 
    rtauto g p = true ->
    Entails (map pdenote g) (pdenote p).
  Proof.
    induction p; intros; simpl in H; intros; try solve [ congruence | simpl in *; eauto with logic | eapply find_sound; eauto ].
    apply andb_true_iff in H. simpl. intuition.
    apply orb_true_iff in H. simpl. intuition.
    apply orb_true_iff in H. destruct H. eapply find_sound; auto.
    simpl. apply ImplI. 
    change (pdenote p1 :: map pdenote g) with (map pdenote (p1 :: g)).
    eapply Assumption. right. apply find_In in H. eapply pdenote_In; auto.
  Qed.

  Require Import ExtLib.Tactics.Reify.

  Global Instance  Reflect_Tr : ClassReify pdenote Tr := { reify := PTr ; reify_sound := refl_equal }.
  Global Instance  Reflect_Fa : ClassReify pdenote Fa := { reify := PFa ; reify_sound := refl_equal }.
  Global Instance  Reflect_And p q (Rp : ClassReify pdenote p) (Rq : ClassReify pdenote q) : ClassReify pdenote (And p q) := 
  { reify := PAnd (@reify _ _ _ _ Rp) (@reify _ _ _ _ Rq)
  ; reify_sound := _ }.
  simpl. f_equal; eapply reify_sound.
  Defined.
  Global Instance  Reflect_Or p q (Rp : ClassReify pdenote p) (Rq : ClassReify pdenote q) : ClassReify pdenote (Or p q) := 
  { reify := POr (@reify _ _ _ _ Rp) (@reify _ _ _ _ Rq)
  ; reify_sound := _ }.
  simpl. f_equal; eapply reify_sound.
  Defined.
  Global Instance  Reflect_Impl p q (Rp : ClassReify pdenote p) (Rq : ClassReify pdenote q) : ClassReify pdenote (Impl p q) := 
  { reify := PImpl (@reify _ _ _ _ Rp) (@reify _ _ _ _ Rq)
  ; reify_sound := _ }.
  simpl. f_equal; eapply reify_sound.
  Defined.

  Theorem rtauto_sound_refl : forall p g (Rp : ClassReify pdenote p) (Rg : ClassReify (map pdenote) g),
    rtauto (@reify _ _ _ _ Rg) (@reify _ _ _ _ Rp) = true -> Entails g p.
  Proof.
    intros.
    eapply rtauto_sound in H. 
    rewrite <- reify_sound with (ClassReify := Rp).
    rewrite <- reify_sound with (ClassReify := Rg).
    assumption.
  Qed.
  
  Goal Entails (Fa :: nil) Fa.
  Proof.
    eapply rtauto_sound_refl. vm_compute. reflexivity.
  Qed.

End PropLogic.
