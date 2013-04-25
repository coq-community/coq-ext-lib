Require Import ExtLib.Structures.EqDep.

Ltac notVar X :=
  match X with
    | _ _ => idtac
    | _ _ _ => idtac
    | _ _ _ _ => idtac
    | _ _ _ _ _ => idtac
    | _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
  end.

Ltac uip_all :=
  repeat match goal with
           | [ H : _ = _ |- _ ] => rewrite H
           | [ |- context [ match ?X in _ = t return _ with 
                              | refl_equal => _ 
                            end ] ] => notVar X; generalize X
           | [ |- context [ eq_rect_r _ _ ?X ] ] => notVar X; generalize X
         end;
  intros;
    repeat match goal with
             | [ H : ?X = ?X |- _ ] => rewrite (UIP_refl H) in *
           end.
