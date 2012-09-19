Require Import Monad.
Require Import OptionMonad.
Require Import Fun.
Require Import ReaderMonad.
Require Import Functor.

Set Implicit Arguments.
Set Strict Implicit.

Import FunctorNotation.
Import MonadNotation.
Import FunNotation.

Open Local Scope monad.

Class HasGasError e := { gasError : e}.
Instance UnitHasGasError : HasGasError unit := { gasError := tt }.

Inductive fuel (m:Type->Type) A := mkFuel { unFuel : readerT nat m A }.

Definition mkFuelReaderT {m} {A} : (nat -> m A) -> fuel m A :=
  @mkFuel _ _ <$> @mkReaderT _ _ _.

Definition unFuelReaderT {m} {A} : fuel m A -> (nat -> m A) :=
  @runReaderT _ _ _ <$> @unFuel _ _.

Instance FuelMonad {m} {mMonad:Monad m} : Monad (fuel m) :=
{ ret _A x := mkFuel (ret x)
; bind _A c _B f := mkFuel (
    x <- unFuel c ;;
    unFuel (f x)
  )
}.

Instance FuelZero {m} {mMonad:Monad m} {mZero:Zero m} : Zero (fuel m) :=
{ zero _A := mkFuel zero}.

Section FuelFix.
  Context {m} {e} {mMonad:Monad m} {mError:MonadExc e m} {eHasGasError:HasGasError e}.

  Fixpoint fuelFix' {A B:Type}
    (ff:(A -> fuel m B) -> (A -> fuel m B)) (k:nat) (a:A) {struct k} : m B :=
      match k with
      | O => raise gasError
      | S k' => unFuelReaderT
                  (ff (fun a' => mkFuelReaderT (fun _k => fuelFix' ff k' a'))
                      a)
                  k'
      end
  .

  Definition fuelFix {A B:Type}
    (ff:(A -> fuel m B) -> (A -> fuel m B)) (a:A) : fuel m B :=
      mkFuelReaderT (fun k => fuelFix' ff k a)
  .

  Global Instance FuelFixMonad : MonadFix (fuel m) :=
    { mfix _A _B := fuelFix }
  .
End FuelFix.

Instance FuelTrans {m} {mMonad:Monad m} : MonadT (fuel m) m :=
{ lift _A aM := mkFuel (lift aM) }.

Instance FuelMonadExc {E} {m} {mMonad:Monad m} {ME : MonadExc E m}
  : MonadExc E (fuel m) :=
{ raise := fun v _ => lift (raise v)
; catch := fun _ c h => mkFuelReaderT (fun s => catch (unFuelReaderT c s) (fun x => unFuelReaderT (h x) s))
}.

Instance FuelReader {r} {m} {mMonad:Monad m} {mReader:Reader r m}
  : Reader r (fuel m) :=
{ ask := lift ask
; local f _A c := mkFuelReaderT (fun k => local f (unFuelReaderT c k))
}.
