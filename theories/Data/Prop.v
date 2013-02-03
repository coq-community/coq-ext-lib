Require Import ExtLib.Structures.Logic.

Instance Logic_Prop : Logic Prop :=
{ Tr       := True
; Fa       := False
; And  p q := p /\ q
; Or   p q := p \/ q
; Impl p q := p -> q
}.

Definition LogicLaws_Prop : LogicLaws Logic_Prop.
refine (
{| Entails g p := List.fold_right Basics.impl p g
|}); try solve [ unfold Basics.impl; simpl in *; firstorder; try (induction G; simpl in *; firstorder) ].
induction G; simpl in *; intros; auto. contradiction.
destruct H. subst. red. clear. intros. induction G; simpl in *; auto.
red. auto.
red. eauto.
Qed.

Existing Instance LogicLaws_Prop.

Section MonadicLogic.
  Variables (T P : Type).
  Context {L : Logic P}.

  Instance Logic_Over : Logic (T -> P) :=
  { Tr       := fun _ => Tr
  ; Fa       := fun _ => Fa
  ; And  p q := fun x => And (p x) (q x)
  ; Or   p q := fun x => Or (p x) (q x)
  ; Impl p q := fun x => Impl (p x) (q x)
  }.
  
  Context {LL : LogicLaws L}.

  Instance LogicLaws_Over : LogicLaws Logic_Over.
  refine (
    {| Entails g p := forall x, Entails (List.map (fun p => p x) g) (p x)
     |}); simpl; intros; 
  try solve [ apply Tr_True | apply Fa_False 
            | eapply ImplI; eauto
            | eapply ImplE; eauto 
            | eapply AndI; eauto 
            | eapply AndEL; eauto 
            | eapply AndER; eauto 
            | eapply OrIL; eauto
            | eapply OrIR; eauto 
            | eapply OrE; eauto 
            ].
  eapply Assumption.
  eapply List.in_map_iff. eexists. intuition.
  Qed.
End MonadicLogic.
