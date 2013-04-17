Require Import Coq.Relations.Relations.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.FunctorRelations.
Require Import ExtLib.Structures.MonadLaws.
Require Import ExtLib.Structures.Proper.

Set Implicit Arguments.
Set Strict Implicit.

Section demo.
  Variable m : Type -> Type.
  Context {M : Monad m}.
  Variable meq : forall {T}, relation T -> relation (m T).
  Existing Class Proper.
  Variable Proper_meq : forall T (rT : relation T), Proper rT -> Proper (meq rT).
  Context {ML : MonadLaws M meq Proper_meq}.
  Variable FPEquiv_meq : FPEquivalence m meq Proper_meq.

  Import MonadNotation.
  Local Open Scope monad_scope.
(*
  Add Parametric Relation meq : 
*)  

  Goal 
    meq (@eq nat) 
        (bind (ret 1) (fun x =>
         bind (ret 2) (fun y =>
         ret (x + y))))
        (ret 3).
  Proof.
    eapply ptransitive. eapply FPP_trans. eapply FPE_preorder.
    instantiate (1 := Proper_meq). apply FPEquiv_meq.
    
    rewrite bind_of_return.
    