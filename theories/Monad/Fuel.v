Require Import Monad.
Require Import OptionMonad.
Require Import Undefined.
Require Import Fun.

Set Implicit Arguments.
Set Strict Implicit.

Import MonadNotationX.
Import FunNotation.

Module GasError.
  Class HasGasError e := { gasError : e}.
  Instance UnitHasGasError : HasGasError unit := { gasError := tt }.
End GasError.

Import GasError.

Inductive fuel (m:Type->Type) A := mkFuel { unFuel : nat -> m A }.
Implicit Arguments mkFuel [m A].

Section FuelFix.
  Context {m} {e} {mError:MonadExc e m} {eHasGasError:HasGasError e}.

  Fixpoint fuelFix' {A B:Type}
    (ff:(A -> fuel m B) -> (A -> fuel m B)) (k:nat) (a:A) {struct k} : m B :=
      match k with
      | O => raise gasError
      | S k' => unFuel (ff (fun a' => mkFuel (fun _k => fuelFix' ff k' a'))
                           a)
                       k'
      end
  .

  Definition fuelFix {A B:Type}
    (ff:(A -> fuel m B) -> (A -> fuel m B)) (a:A) : fuel m B :=
      mkFuel (fun k => fuelFix' ff k a)
  .

  Instance FuelFixMonad : MonadFix (fuel m) :=
    { mfix _A _B := fuelFix }
  .

End FuelFix.