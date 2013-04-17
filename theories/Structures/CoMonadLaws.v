Require Import Coq.Relations.Relations.
Require Import ExtLib.Structures.CoMonad.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Data.Fun.

Set Implicit Arguments.
Set Strict Implicit.

Section Laws.
  Variable m : Type -> Type.
  Variable CM : CoMonad m.

  Variable meq : forall T (rT : relation T), relation (m T).
  Variable Proper_m : forall T (rT : relation T) (pT : Proper rT), Proper (meq rT).

  Class CoMonadLaws : Type :=
  { cobind_coret : forall T (rT : relation T) (pT : Proper rT) (a : m T),
    proper a ->
    meq rT (cobind a coret) a
  ; coret_cobind : forall T U (rT : relation T) (rU : relation U)
    (pT : Proper rT) (pU : Proper rU) 
    (a : m T) (f : m T -> U), 
    proper a -> proper f ->
    rU (coret (cobind a f)) (f a)
  ; cobind_assoc : forall T U V (rT : relation T) (rU : relation U) (rV : relation V)
    (pT : Proper rT) (pU : Proper rU) (pV : Proper rV)
    (a : m T) (b : m T -> U) (c : m U -> V),
    proper a -> proper b -> proper c ->
    meq rV (cobind (cobind a b) c) (cobind a (fun x => c (cobind x b)))
    
  ; coret_proper : forall T (rT : relation T) (pT : Proper rT) (a : m T),
    proper a -> proper (coret a)
  ; cobind_proper : forall T U (rT : relation T) (rU : relation U)
    (pT : Proper rT) (pU : Proper rU) 
    (rT : relation T) (pT : Proper rT) (a : m T) (b : m T -> U),
    proper a -> proper b -> proper (cobind a b)

  ; coret_respectful : forall T (rT : relation T) (pT : Proper rT) (a b : m T),
    proper a -> proper b ->
    meq rT a b ->
    rT (coret a) (coret b)
  ; cobind_respectful : forall T U (rT : relation T) (rU : relation U)
    (pT : Proper rT) (pU : Proper rU) 
    (rT : relation T) (pT : Proper rT) (c c' : m T) (f g : m T -> U),
    meq rT c c' ->
    (forall a b, proper a -> proper b -> meq rT a b -> rU (f a) (g b)) ->
    meq rU (cobind c f) (cobind c' g)
  }.
End Laws.