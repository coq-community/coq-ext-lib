Require Import Coq.Program.Basics.
Require Import ExtLib.Relations.Equiv.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.CoMonad.

Set Implicit Arguments.
Set Strict Implicit.

Local Open Scope program_scope. (* for compose notation *)

Section CoMonadLaws.

  Variable m : Type -> Type.

  Variable Rm : forall a, Equiv a -> Equiv (m a).
  Local Existing Instance Rm.

  Instance Equiv_Fun (A B : Type) `{Equiv A} `{Equiv B} : Equiv (A -> B) :=
    (equiv ==> equiv)%signature.
  Class CoMonadLaws
        `{F : Functor m}
        `{C: CoMonad m}
  : Type :=
  { extend_extract: forall (A:Type) `{Equiv A},
      ext_equiv (A:=m A) (B:=m A)
        (extend extract)
        id
  ; extract_extend: forall (A B:Type) {f} `{Equiv A} `{Equiv B},
      ext_equiv
        (extract ∘ extend (A:=A) (B:=B) f)
        f
  ; extend_extend:forall (A B:Type) `{Equiv A} {f g},
      ext_equiv
        (extend (A:=B) (B:=A) f ∘ extend (A:=A) g)
        (extend (f ∘ extend g))
  ; extract_duplicate : forall (A : Type) `{Equiv A},
      ext_equiv
        (extract ∘ duplicate)
        id
  ; fmap_extract_duplicate : forall (A : Type) `{Equiv A},
      ext_equiv
        (fmap extract ∘ duplicate) (@id (m A))
  ; duplicate_duplicate : forall (A : Type) `{Equiv A},
      ext_equiv
        (duplicate ∘ duplicate)
        (fmap duplicate ∘ duplicate)
  ; Proper_extract : forall {A} `{Equiv A},
      Proper (equiv ==> equiv) (@extract m _ A)
  ; Proper_extend : forall {A B} `{Equiv A} `{Equiv B},
        Proper ((equiv) ==> (equiv) ==> equiv) (@extend m _ A B)
  ; Proper_duplicate : forall A `{Equiv A},
      Proper equiv (@duplicate m _ A)
  }.

  Section from_extendOk.
    Context {Fm : Functor m}.
    Variable doExtract : forall {A}, m A -> A.
    Variable doExtend : forall {A B}, (m A -> B) -> m A -> m B.

    Let Cm : CoMonad m := (from_extend m doExtract doExtend).
    Local Existing Instance Cm.

    Hypothesis Hextend_extract: forall (A:Type) `{Equiv A},
      ext_equiv (A:=m A) (B:=m A)
        (doExtend (@doExtract _))
        id.
    Hypothesis Hextract_extend: forall (A B:Type) {f} `{Equiv A} `{Equiv B},
      ext_equiv
        (@doExtract _ ∘ doExtend (A:=A) (B:=B) f)
        f.
    Hypothesis Hextend_extend:forall (A B:Type) `{Equiv A} {f g},
      ext_equiv
        (doExtend (A:=B) (B:=A) f ∘ doExtend (A:=A) g)
        (doExtend (f ∘ doExtend g)).

    Theorem from_extendOk : @CoMonadLaws Fm Cm.
    Proof.
      constructor; try assumption.
      { simpl. unfold ext_equiv. red. intros.
        change (fun c : m A => doExtend (fun x0 : m A => x0) c)
          with (doExtend (fun x0 : m A => x0)).
        generalize (fun f => @Hextract_extend (m A) (m A) f _ _).
        unfold compose. simpl. intros.
        (** TODO: It is necessary to have Transitivity, and maybe more. *)


End CoMonadLaws.
