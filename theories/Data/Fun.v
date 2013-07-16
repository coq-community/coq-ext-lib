Require Import Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Data.PreFun.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Logic.
Require Import ExtLib.Structures.CoFunctor.
Require Import ExtLib.Structures.Monoid.

Set Implicit Arguments.
Set Strict Implicit.

Global Instance proper_id (T : Type) {tT : type T} : proper (fun x => x).
Proof.
  repeat red; intros. apply H.
Qed.


Section functors.
  Variable A : Type.
  
  Instance FunFunctor A : Functor (Fun A) :=
  { fmap _A _B g f x := g (f x)
  }.

  Local Instance Functor_Fun : Functor (Fun A) :=
  { fmap _A _B g f x := g (f x) }.

  Local Instance CoFunctor_Fun T : CoFunctor (fun x => x -> T) :=
  {| cofmap := fun _ _ g f => fun x => f (g x) |}.

  Local Instance Functor_functor F G (fF : Functor F) (fG : Functor G) : Functor (fun x => F (G x)) :=
  {| fmap := fun _ _ g => @fmap F _ _ _ (@fmap G _ _ _ g) |}.

  Local Instance CoFunctor_functor F G (fF : Functor F) (fG : CoFunctor G) : CoFunctor (fun x => F (G x)) :=
  {| cofmap := fun _ _ g => @fmap F _ _ _ (@cofmap G _ _ _ g) |}.

  Local Instance Functor_cofunctor F G (fF : CoFunctor F) (fG : Functor G) : CoFunctor (fun x => F (G x)) :=
  {| cofmap := fun _ _ g => @cofmap F _ _ _ (@fmap G _ _ _ g) |}.

  Local Instance CoFunctor_cofunctor F G (fF : CoFunctor F) (fG : CoFunctor G) : Functor (fun x => F (G x)) :=
  {| fmap := fun _ _ g => @cofmap F _ _ _ (@cofmap G _ _ _ g) |}.

End functors.

Section MonadicLogic.
  Variables (T P : Type).
  Context {L : Logic P}.

  Global Instance Logic_Fun : Logic (T -> P) :=
  { Entails g p := forall x, Entails (List.map (fun p => p x) g) (p x)
  ; Tr       := fun _ => Tr
  ; Fa       := fun _ => Fa
  ; And  p q := fun x => And (p x) (q x)
  ; Or   p q := fun x => Or (p x) (q x)
  ; Impl p q := fun x => Impl (p x) (q x)
  }.
  
  Context {LL : LogicLaws L}.

  Global Instance LogicLaws_Over : LogicLaws Logic_Fun.
  Proof.
    constructor; simpl; intros; 
    try (solve [ apply Tr_True | apply Fa_False 
               | eapply ImplI; eauto
               | eapply ImplE; eauto 
               | eapply AndI; eauto 
               | eapply AndEL; eauto 
               | eapply AndER; eauto 
               | eapply OrIL; eauto
               | eapply OrIR; eauto 
               | eapply OrE; eauto 
        ]).
    eapply Assumption.
    eapply List.in_map_iff. eexists. intuition.
  Qed.
End MonadicLogic.

Section MonadicLogic_dep.
  Variable T : Type.
  Variable P : T -> Type.
  Context {L : forall t, Logic (P t)}.

  Global Instance Logic_DOver : Logic (forall t : T, P t) :=
  { Entails g p := forall x, Entails (List.map (fun p => p x) g) (p x)
  ; Tr       := fun _ => Tr
  ; Fa       := fun _ => Fa
  ; And  p q := fun x => And (p x) (q x)
  ; Or   p q := fun x => Or (p x) (q x)
  ; Impl p q := fun x => Impl (p x) (q x)
  }.
  
  Context {LL : forall t, LogicLaws (L t)}.

  Global Instance LogicLaws_DOver : LogicLaws Logic_DOver.
  Proof.
    constructor; simpl; intros; 
    try (solve [ apply Tr_True | apply Fa_False 
               | eapply ImplI; eauto
               | eapply ImplE; eauto 
               | eapply AndI; eauto 
               | eapply AndEL; eauto 
               | eapply AndER; eauto 
               | eapply OrIL; eauto
               | eapply OrIR; eauto 
               | eapply OrE; eauto 
               ]).
    eapply Assumption.
    eapply List.in_map_iff. eexists. intuition.
  Qed.
End MonadicLogic_dep.

Instance Quant_Fun (T U : Type) (Q : Quant U) : Quant (T -> U) :=
{| All := fun V P => fun (t : T) => All (fun x : V => P x t)
 ; Ex  := fun V P => fun (t : T) => Ex (fun x : V => P x t)
 |}.

Definition Monoid_compose T : Monoid (T -> T) :=
{| monoid_plus g f x := g (f x)
 ; monoid_unit x := x
|}.

Export PreFun.
