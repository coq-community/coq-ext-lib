Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.FunctorRelations.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Unit.

Set Implicit Arguments.
Set Strict Implicit.

Section MonadLaws.
  Variable m : Type -> Type.
  Variable M : Monad m.

  (** This <= relation is a computational <= relation based on the ideas
   ** of domain theory. It generalizes the usual equivalence relation by,
   ** enabling the relation to talk about computations that are "more defined"
   ** than others.
   **
   ** This generalization is done to support the fixpoint law.
   **)
  Variable meq : forall {T}, type T -> type (m T).

(*
  (** This states when an element is a proper element under an equivalence
   ** relation.
   **)
  Variable Proper_m : forall T, Proper T -> Proper (m T).
*)

  Class MonadLaws : Type :=
  { bind_of_return : forall A B (eA : type A) (eB : type B),
    typeOk eA -> typeOk eB ->
    forall (a:A) (f:A -> m B),
    proper a -> proper f ->
    equal (bind (ret a) f) (f a)
  ; return_of_bind : forall A (eA : type A), 
    typeOk eA ->
    forall (aM:m A) (f:A -> m A),
    (forall x, equal (f x) (ret x)) ->
    proper aM ->
    equal (bind aM f) aM
  ; bind_associativity :
    forall A B C (eA : type A) (eB : type B) (eC : type C),
      typeOk eA -> typeOk eB -> typeOk eC ->
      forall (aM:m A) (f:A -> m B) (g:B -> m C),
      proper aM -> 
      proper f -> 
      proper g ->
      equal (bind (bind aM f) g) (bind aM (fun a => bind (f a) g))

  ; ret_respectful :> forall A (eA : type A), typeOk eA ->
    proper ret
  ; bind_respectful :> forall A B (eA : type A) (eB : type B), 
    typeOk eA -> typeOk eB ->
    proper (@bind m _ A B)
  }.

  Class MonadTLaws (n : Type -> Type) (Pn : forall T (R : type T), type (n T)) (nM : Monad n) (MT : MonadT m n) : Type :=
  { lift_ret  : forall T (eT : type T),
    typeOk eT ->
    forall x : T,
    proper x ->
    equal (lift (ret x)) (ret x)
  ; lift_bind : forall T U (eT : type T) (eU : type U),
    typeOk eT -> typeOk eU ->
    forall (c : n T) (f : T -> n U),
    proper c -> proper f ->
    equal (lift (bind c f)) (bind (lift c) (fun x => lift (f x)))
  ; lift_proper : forall T (tT : type T), typeOk tT -> proper lift
  }.

  Class MonadStateLaws s (tS : type s) (tokS : typeOk tS) (MS : MonadState s m) : Type :=
  { get_put : equal (bind get put) (ret tt)
  ; get_proper :> proper get
  ; put_proper :> proper put
  }.

  Class MonadReaderLaws S (tS : type S) (tokS : typeOk tS) (MS : MonadReader S m) : Type :=
  { ask_local : forall f, proper f ->
    equal (local f ask) (bind ask (fun x => ret (f x)))
  ; local_local : forall T (eA : type T),
    typeOk eA ->
    forall (s s' : S -> S) (c : m T),
      proper s -> proper s' -> proper c ->
    equal (local s (local s' c)) (local (fun x => s' (s x)) c)
  }.

  Class MonadZeroLaws (MZ : MonadZero m) : Type :=
  { bind_zero : forall A B (tA : type A) (tB : type B),
    typeOk tA -> typeOk tB ->
    forall (f : A -> m B),
    proper f ->
    equal (bind mzero f) mzero
  ; zero_proper :> forall A (rA : type A), typeOk rA ->
    proper mzero
  }.

  Class MonadFixLaws (MF : MonadFix m) : Type :=
  { mleq : forall T, relation T -> relation (m T)
  ; mfix_monotonic : forall T U (rT : type T) (rU : type U),
    typeOk rT -> typeOk rU ->
    forall (F : (T -> m U) -> T -> m U),
    respectful equal (mleq equal) (mfix F) (F (mfix F))
  ; mfix_proper :> forall T U (rT : type T) (rU : type U),
    typeOk rT -> typeOk rU ->
    proper (@mfix _ _ T U)
  }.

End MonadLaws.


(*
Hint Rewrite bind_of_return bind_associativity using (eauto with typeclass_instances) : monad_rw.
(* Hint Rewrite lift_ret lift_bind get_put ask_local local_local bind_zero : monad_rw. *)

Ltac monad_norm :=
  let tc := solve [ eauto with typeclass_instances ] in
  let tac :=
    repeat (eapply bind_respectful_hd; [ tc | tc | ]);
    repeat (eapply bind_respectful_tl; [ tc | tc | intros ]);
    repeat (rewrite return_of_bind; [ tc | tc | intros ]);
    try (autorewrite with monad_rw; intros)
  in
  try ( unfold liftM, liftM2 in * ) ;
  repeat progress tac.
*)
