Require Import BinNat.
Require Import ExtLib.Programming.Show.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Structures.CoMonad.

Global Instance Show_N : Show N :=
{ show := fun n => 
  match n with
    | N0 => show_exact "0"
    | Npos p => show p
  end }.

Section iter.
  Context {m : Type -> Type}.
  Context {CM : CoMonad m}.
  Context {T : Type}.

  Definition Niter (f : m T -> T) (n : N) : m T -> T :=
    match n with
      | N0 => coret
      | Npos p => Piter f p 
    end.

End iter.


