Require Import ExtLib.Tactics.Consider.

Set Implicit Arguments.
Set Strict Implicit.

Ltac forward :=
  let check X :=
    match X with
      | match _ with _ => _ end => fail 1
      | if _ then _ else _ => fail 1
      | _ => idtac
    end
  in
  repeat match goal with
           | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
             check X; 
             (consider X; try congruence); [ intros ]
           | [ H : context [ if ?X then _ else _ ] |- _ ] =>
             check X; 
             (consider X; try congruence); [ intros ]
         end.
