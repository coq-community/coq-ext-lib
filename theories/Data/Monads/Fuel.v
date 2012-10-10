Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Monads.ReaderMonad.
Require Import Fun.
Require Import Injection.
Require Import ExtLib.Structures.Functor.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Import FunctorNotation.
Import MonadNotation.
Import FunNotation.

Inductive gasError := GasError.

Inductive fuel (m:Type->Type) A := mkFuel { unFuel : readerT nat m A }.

Definition mkFuelReaderT {m} {A} : (nat -> m A) -> fuel m A := mkFuel <$> mkReaderT.

Definition unFuelReaderT {m} {A} : fuel m A -> (nat -> m A) := runReaderT <$> unFuel.

Instance FuelMonad {m} {mMonad:Monad m} : Monad (fuel m) :=
{ ret _A x := mkFuel (ret x)
; bind _A c _B f := mkFuel (
    x <- unFuel c ;;
    unFuel (f x)
  )
}.

Instance FuelZero {m} {mMonad:Monad m} {mZero:MonadZero m} : MonadZero (fuel m) :=
{ mzero _A := mkFuel mzero}.

Section FuelFix.
  Context {m} {mMonad:Monad m}.
  Context {e} {mError:MonadExc e m} {eInject:Injection gasError e}.

  Fixpoint fuelFix' {A B:Type}
    (ff:(A -> fuel m B) -> (A -> fuel m B)) (k:nat) (a:A) {struct k} : m B :=
      match k with
      | O => raise (inject GasError)
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
{ raise := fun _ v => lift (raise v)
; catch := fun _ c h => mkFuelReaderT (fun s => catch (unFuelReaderT c s) (fun x => unFuelReaderT (h x) s))
}.

Instance FuelReader {r} {m} {mMonad:Monad m} {mReader:MonadReader r m}
  : MonadReader r (fuel m) :=
{ ask := lift ask
; local f _A c := mkFuelReaderT (fun k => local f (unFuelReaderT c k))
}.

Instance FuelPlus {m} {mMonad:Monad m} {mPlus:MonadPlus m} : MonadPlus (fuel m) :=
{ mplus _A _B mA mB := mkFuel (mplus (unFuel mA) (unFuel mB)) }.
