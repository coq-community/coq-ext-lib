(* State monad example adapted from https://wiki.haskell.org/State_Monad

 Example use of State monad
 Passes a string of dictionary {a,b,c}
 Game is to produce a number from the string.
 By default the game is off, a C toggles the
 game on and off. A 'a' gives +1 and a b gives -1.
 E.g
 'ab'    = 0
 'ca'    = 1
 'cabca' = 0
 State = game is on or off & current score
       = (Bool, Int)
 *)

Require Import Coq.ZArith.ZArith_base Coq.Strings.String.
Require Import ExtLib.Data.Monads.StateMonad ExtLib.Structures.Monads.

Section StateGame.

  Import MonadNotation.
  Local Open Scope Z_scope.
  Local Open Scope char_scope.
  Local Open Scope monad_scope.

  Definition GameValue : Type := Z.
  Record GameState : Type := mkGameState {on:bool; score:Z}.

  Context {m : Type -> Type}.
  Context {Monad_m: Monad m}.
  Context {State_m: MonadState GameState m}.

  Fixpoint playGame (s: string) {struct s}: m GameValue :=
    match s with
    |  EmptyString =>
       v <- get ;; ret (score v)
    |  String x xs =>
       v <- get ;;
         match x, (on v) with
         | "a", true =>  put {| on := on v ; score := (score v) + 1 |}
         | "b", true => put {| on := on v ; score := (score v) - 1 |}
         | "c", _ =>   put {| on := negb (on v) ; score := score v |}
         |  _, _  =>   put v
         end ;; playGame xs
    end.

  Definition startState: GameState := {| on:=false; score:=0 |}.

End StateGame.

Definition main : GameValue :=
  evalState (playGame "abcaaacbbcabbab") startState.

(* The following should return '2%Z' *)
Compute main.
