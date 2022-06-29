From ExtLib Require Import
     Monad
     OptionMonad
     StateMonad.

(** [Monad_stateT] is not in context, so this definition fails *)
Fail Definition foo : stateT unit option unit :=
  ret tt.

(** Use [Existing Instance] to bring the Local [Monad_stateT] instance into context *)
#[global] Existing Instance Monad_stateT.

(** Now the definition succeeds *)
Definition foo : stateT unit option unit :=
  ret tt.
