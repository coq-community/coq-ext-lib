Require Import Coq.Relations.Relations.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Data.Fun.

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
  Variable mleq : forall {T}, (T -> T -> Prop) -> m T -> m T -> Prop.

  (** This states when an element is a proper element under an equivalence
   ** relation.
   **)
  Variable Proper_m : forall T (R : T -> T -> Prop), Proper R -> Proper (mleq R).

  Class MonadOrder : Type :=
  { me_refl   : forall T (e : T -> T -> Prop) {P : Proper e}, 
    PReflexive e -> PReflexive (mleq e)
  ; me_trans  : forall T (e : T -> T -> Prop) {P : Proper e},
    PTransitive e -> PTransitive (mleq e)
  }.

  (** TODO: The real question is whether all of these [eX] relations
   ** need to be reflexive and transitive. They don't seem to need to be
   ** for option monad, but the proofs would be more automatable if they
   ** were b/c I'd be able to rewrite.
   **)
  (** Should anything here mention meq? It seems like everything should be mleq **)

  Class MonadLaws : Type :=
  { bind_of_return : forall A B (a:A) (f:A -> m B) (eA : relation A) (eB : relation B) (Pa : Proper eA) (Pb : Proper eB),
    PReflexive eA -> PReflexive eB -> PTransitive eB ->
    proper a -> proper f ->
    mleq eB (bind (ret a) f) (f a)
  ; return_of_bind : forall A (eA : relation A) (PA : Proper eA) (aM:m A) (f:A -> m A),
    PTransitive eA -> PReflexive eA -> proper aM -> proper f ->
    (forall x, mleq eA (f x) (ret x)) ->
    mleq eA (bind aM f) aM
  ; bind_associativity :
    forall A B C (eA : relation A) (eB : relation B) (eC : relation C) 
      (PA : Proper eA) (Pb : Proper eB) (PC : Proper eC)
      (aM:m A) (f:A -> m B) (g:B -> m C),
      PReflexive eA -> PReflexive eB -> PTransitive eB -> PReflexive eC -> PTransitive eC ->
      proper aM -> 
      proper f -> 
      proper g ->
      mleq eC (bind (bind aM f) g) (bind aM (fun a => bind (f a) g))

  ; ret_respectful_leq : forall A (eA : relation A) (P : Proper eA),
    forall x y, eA x y -> mleq eA (ret x) (ret y)
  ; bind_respectful_leq : forall A B (c c' : m A) (f g : A -> m B) 
    (eA : relation A) (eB : relation B) (Pa : Proper eA) (Pb : Proper eB),
    mleq eA c c' ->
    (forall a b, proper a -> proper b -> eA a b -> mleq eB (f a) (g b)) ->
    mleq eB (bind c f) (bind c' g)

  ; ret_proper : forall T (rT : relation T) (P : Proper rT) (x : T),
    PReflexive rT -> proper x -> proper (ret x) 
  ; bind_proper : forall A B (rA : relation A) (rB : relation B) 
    (Pa : Proper rA) (Pb : Proper rB) c (f : A -> m B),
    PReflexive rA -> PReflexive rB -> PTransitive rB ->
    proper c -> proper f -> proper (bind c f)
  }.


(*

  Section meq.
    Context {T : Type} (leq : T -> T -> Prop) (P : Proper leq).

    Definition meq (a b : m T) :  Prop :=
      mleq leq a b /\ mleq leq b a.

    Variable MO : MonadOrder.

    Global Instance Proper_meq : Proper meq :=
    { proper := fun r => proper r }.

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
  Section meq_respectful.
    Variable ml : MonadLaws.

    Theorem ret_respectful : forall A (eA : relation A) (P : Proper eA),
      PSymmetric eA ->
      forall x y, proper x -> proper y -> eA x y -> meq eA (ret x) (ret y).
    Proof.
      intros. unfold meq. intuition; eapply ret_respectful_leq; eauto.
    Qed.

    Theorem bind_respectful_hd : forall A B (eA : relation A) (eB : relation B)
      (Pa : Proper eA) (Pb : Proper eB) c c' 
      (f : A -> m B),
      proper c -> proper c' -> proper f ->
      meq eA c c' ->
      meq eB (bind c f) (bind c' f).
    Proof.
      intros; intuition. unfold meq in *; intuition; eapply bind_respectful_hd_leq; eauto.
    Qed.

    Theorem bind_respectful_tl : forall A B (eA : relation A) (eB : relation B)
      (Pa : Proper eA) (Pb : Proper eB) 
      (f g : A -> m B),
      proper f -> proper g -> 
      (forall a, proper a -> meq eB (f a) (g a)) ->
      forall c, proper c -> meq eB (bind c f) (bind c g).
    Proof.
      intros; intuition. unfold meq in *; intuition; eapply bind_respectful_tl_leq; eauto;
      firstorder.
    Qed.
  End meq_respectful.
*)

(*
  Class MonadTLaws (n : Type -> Type) (Pn : forall T (R : relation T), Proper R -> Proper (n T)) (nM : Monad n) (MT : MonadT m n) : Type :=
  { lift_ret  : forall T (x : T) (eT : T -> T -> Prop) (Pt : Proper eT),
    PReflexive eT -> PTransitive eT ->
    proper x ->
    mleq eT (lift (ret x)) (ret x)
  ; lift_bind : forall T U (c : n T) (f : T -> n U) (eT : relation T) (eU : relation U)
    (Pu : Proper eU) (Pt : Proper eT),
    PReflexive eU -> PTransitive eU ->
    proper c -> proper f ->
    mleq eU (lift (bind c f)) (bind (lift c) (fun x => lift (f x)))
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
    forall A B c eB, mleq eB (@bind _ M _ _ (@mzero _ _ A) c) (@mzero _ _ B)
  ; zero_proper : forall A (rA : relation A) (Pa : Proper rA), 
    proper mzero
  }.

  Class MonadFixLaws (MF : MonadFix m) : Type :=
  { mfix_monotonic : forall T U (rT : relation T) (rU : relation U)
    (PT : Proper rT) (PU : Proper rU) 
    (F : (T -> m U) -> T -> m U),
    @proper _ _ (Proper_fun (Proper_fun _ _) (Proper_fun _ _)) F ->
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