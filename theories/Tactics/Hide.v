(* The names of the tactics here come from the 2013 distribution 
of Software Foundations (SF). The implementations are different, though:
1) The hiding mechanism is SF was not fully reliable:
 tactics that compute on hypotheses could unhide stuff
2) Hiding in SF was always reversible. Here, unhiding only works
when proving a Prop. We can change
the return type to [Type]. But then hiding hypothesis can make
things unprovable by introducing universe constraints.
*)

Inductive Hidden (P:Type) : Prop:=
| hidden (p:P): Hidden P.

Ltac show_hyp H :=
  destruct H as [H].

Ltac hide_hyp H :=
  apply hidden in H.

Ltac show_hyps :=
  repeat match goal with
           H: Hidden _ |- _ => show_hyp H end.
