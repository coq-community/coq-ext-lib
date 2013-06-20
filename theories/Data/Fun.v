Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Logic.

Set Implicit Arguments.
Set Strict Implicit.

Definition Fun A B := A -> B.

Instance FunFunctor A : Functor (Fun A) :=
{ fmap _A _B g f x := g (f x)
}.

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
