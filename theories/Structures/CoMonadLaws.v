Require Import Coq.Program.Basics.
Require Import ExtLib.Structures.CoMonad.

Set Implicit Arguments.
Set Strict Implicit.

Local Open Scope program_scope.

Section CoMonadLaws.
  Variable m : Type -> Type.
  Variable C : CoMonad m.

  Class CoMonadLaws :=
    {
      extend_extract: forall (A B:Type),
        extend (B:=A) extract = id ;

      extract_extend: forall (A B:Type) {f},
          extract ∘ extend (A:=A) (B:=B) f = f;

      extend_extend:forall (A B:Type) {f g},
          extend (A:=B) (B:=A) f ∘ extend (A:=A) g = extend (f ∘ extend g)
    }.

End CoMonadLaws.
