Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Proper.
Require Import Equivalence.

Set Implicit Arguments.
Set Strict Implicit.

Section MonadLaws.
  Variable m : Type -> Type.
  Variable M : Monad m.

  (** This states when an element is a proper element under an equivalence
   ** relation.
   **)
  Variable Proper_m : forall T, Proper T -> Proper (m T).

  (** This <= relation is a computational <= relation based on the ideas
   ** of domain theory. It generalizes the usual equivalence relation by,
   ** enabling the relation to talk about computations that are "more defined"
   ** than others.
   **
   ** This generalization is done to support the fixpoint law.
   **)
  Variable mleq : forall {T}, (T -> T -> Prop) -> m T -> m T -> Prop.

  Class MonadOrder : Type :=
  { me_refl   : forall T {P : Proper T} (e : T -> T -> Prop),
    PReflexive e -> PReflexive (mleq e)
  ; me_trans  : forall T {P : Proper T} (e : T -> T -> Prop),
    PTransitive e -> PTransitive (mleq e)
  }.

  Section meq.
    Context {T : Type} (leq : T -> T -> Prop) (P : Proper T).

    Definition meq (a b : m T) :  Prop :=
      mleq leq a b /\ mleq leq b a.

    Variable MO : MonadOrder.

    Global Instance PReflexive_meq {_ : PReflexive leq} : PReflexive meq.
    Proof.
      split; eapply me_refl; eauto.
    Qed.

    Global Instance PSymmetric_meq : PSymmetric meq.
    Proof.
      unfold meq; split; intuition; intuition.
    Qed.

    Global Instance PTransitive_meq {_ : PTransitive leq} : PTransitive meq.
    Proof.
      split; unfold meq in *; intuition.
      { eapply me_trans; [ | | | | eassumption | eassumption ]; eauto. }
      { eapply me_trans; [ | | | | eassumption | eassumption ]; eauto. }
    Qed.
  End meq.

  Instance Proper_arrow {A B : Type} {Pa : Proper A} {Pb : Proper B} : Proper (A -> B) :=
  { proper := fun f => forall x, proper x -> proper (f x) }.

  (** TODO: The real question is whether all of these [eX] relations
   ** need to be reflexive and transitive. They don't seem to need to be
   ** for option monad, but the proofs would be more automatable if they
   ** were b/c I'd be able to rewrite.
   **)
  (** Should anything here mention meq? It seems like everything should be mleq **)
  Class MonadLaws : Type :=
  { morder :> MonadOrder
  ; bind_of_return : forall A B (a:A) (f:A -> m B) (eB : B -> B -> Prop),
    meq eB (bind (ret a) f) (f a)
  ; return_of_bind : forall A (PA : Proper A) (aM:m A) (f:A -> m A) (eA : A -> A -> Prop),
    PReflexive eA -> proper aM -> proper f ->
    (forall x, meq eA (f x) (ret x)) -> meq eA (bind aM f) aM
  ; bind_associativity :
    forall A B C (PA : Proper A) (Pb : Proper B) (PC : Proper C) (aM:m A) (f:A -> m B) (g:B -> m C) (eC : C -> C -> Prop),
      PReflexive eC -> PTransitive eC -> proper aM -> proper f -> proper g ->
      meq eC (bind (bind aM f) g) (bind aM (fun a => bind (f a) g))

  ; ret_respectful : forall A (P : Proper A) (eA : A -> A -> Prop), 
    forall x y, eA x y -> mleq eA (ret x) (ret y)
    
  ; bind_respectful_hd_leq : forall A B c c' (f : A -> m B) (eA : A -> A -> Prop) (eB : B -> B -> Prop),
    mleq eA c c' ->
    mleq eB (bind c f) (bind c' f)
  ; bind_respectful_tl_leq : forall A B (PB : Proper B) (f g : A -> m B) (eB : B -> B -> Prop),
    PReflexive eB ->
    (forall a, mleq eB (f a) (g a)) ->
    forall c, mleq eB (bind c f) (bind c g)

  ; ret_proper : forall T (P : Proper T) (x : T), proper x -> proper (ret x) 
  ; bind_proper : forall A B (Pa : Proper A) (Pb : Proper B) c (f : A -> m B),
    proper c -> proper f -> proper (bind c f)
  }.

(**
  Section meq_respectful.
    Variable ml : MonadLaws.

    Theorem ret_respectful : forall A (P : Proper A) (eA : A -> A -> Prop), 
      PReflexive 
      forall x y, eA x y -> meq (mleq) eA (ret x) (ret y).


  Theorem bind_respectful_hd : forall A B c c' (f : A -> m B)
    (eA : A -> A -> Prop) (eB : B -> B -> Prop),
    meq eA c c' ->
    meq eB (bind c f) (bind c' f).
  Proof.
    intros; intuition. destruct H; split; eapply bind_respectful_hd_leq; eauto.
  Qed.

  Theorem bind_respectful_tl : forall A B (f g : A -> m B) (eB : B -> B -> Prop),
    Reflexive eB ->
    (forall a, meq eB (f a) (g a)) ->
    forall c, meq eB (bind c f) (bind c g).
  Proof.
    intros; intuition. split; eapply bind_respectful_tl_leq; eauto; intros; edestruct H0; eauto.
  Qed.
**)

(*
  Class MonadTLaws (n : Type -> Type) (nM : Monad n) (MT : MonadT m n) : Type :=
  { lift_ret  : forall T (x : T) (eT : T -> T -> Prop),
    Reflexive eT -> Transitive eT ->
    meq eT (lift (ret x)) (ret x)
  ; lift_bind : forall T U (c : n T) (f : T -> n U) (eU : U -> U -> Prop),
    Reflexive eU -> Transitive eU ->
    meq eU (lift (bind c f)) (bind (lift c) (fun x => lift (f x)))
  }.

  Class MonadStateLaws s (MS : MonadState s m) : Type :=
  { get_put : forall eA,
    meq eA (bind get put) (ret tt)
  ; put_get : forall A (eA : A -> A -> Prop),
    forall x f, meq eA (bind (put x) (fun _ => bind get f))
                       (bind (put x) (fun _ => f x))
  }.

  Class MonadReaderLaws S (MS : MonadReader S m) : Type :=
  { ask_local : forall f eA,
    meq eA (local f ask) (bind ask (fun x => ret (f x)))
  ; local_local : forall T (s s' : S -> S) (c : m T) eA,
    meq eA (local s (local s' c)) (local (fun x => s' (s x)) c)
  }.
*)

  Class MonadZeroLaws (MZ : MonadZero m) : Type :=
  { bind_zero :
    forall A B c eB, meq eB (@bind _ M _ _ (@mzero _ _ A) c) (@mzero _ _ B)
  }.

  Class MonadFixLaws (MF : MonadFix m) : Type :=
  { mfix_monotonic : forall T U (PT : Proper T) (PU : Proper U) 
    (F : (T -> m U) -> T -> m U),
    proper F ->
    forall x, mleq (@eq _) (mfix F x) (F (mfix F) x)
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