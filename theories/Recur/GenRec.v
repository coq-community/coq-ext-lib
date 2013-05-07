Set Implicit Arguments.
Set Strict Implicit.

Fixpoint guard A (R : A -> A -> Prop) (n : nat) (wfR : well_founded R)
  {struct n}: well_founded R :=
  match n with
    | 0 => wfR
    | S n => fun x => Acc_intro x (fun y _ => guard n (guard n wfR) y)
  end.
