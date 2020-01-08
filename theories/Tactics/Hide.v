(* caution: hiding a non-proof may be irreversible. We can change
the return type to [Type]. But then hiding hypothesis can make
things unprovable by introducing universe constraints *)
Inductive Hidden (P:Type) : Prop:=
| hidden (p:P): Hidden P.

Ltac show_hyp H :=
  destruct H as [H].

Ltac hide_hyp H :=
  apply hidden in H.

Ltac show_hyps :=
  repeat match goal with
           H: Hidden _ |- _ => show_hyp H end.
