Require Import Coq.Program.Basics.
Require Import ExtLib.Relations.Equiv.
Require Import ExtLib.Structures.CoMonad.

Set Implicit Arguments.
Set Strict Implicit.

Local Open Scope program_scope. (* for compose notation *)

Section CoMonadLaws.

  Class CoMonadMorphisms
        (m : Type -> Type)
        `{C: CoMonad m}
  : Type :=
    {
      (*
      extract_proper:
        Proper ((equiv) ==> (equiv) ==> (equiv)) extract;
      extend_proper:
        Proper ((equiv) ==> (equiv) ==> (ext_equiv) ==> (equiv)  ==> (equiv)) extract;
       *)
    }.

  Class CoMonadLaws
        (m : Type -> Type)
        `{C: CoMonad m}
        `{@CoMonadMorphisms m C} : Type :=
    {
      extend_extract: forall (A:Type) `{Equiv (m A)},
        ext_equiv
          (extend extract)
          id ;

      extract_extend: forall (A B:Type) {f} `{Equiv (m A)} `{Equiv B},
          ext_equiv
            (extract ∘ extend (A:=A) (B:=B) f)
            f;

      extend_extend:forall (A B:Type) `{Equiv (m A)} {f g},
          ext_equiv
            (extend (A:=B) (B:=A) f ∘ extend (A:=A) g)
            (extend (f ∘ extend g))
    }.

End CoMonadLaws.
