Require Import Monad.

Set Implicit Arguments.
Set Strict Implicit.

Section Ident.
  Definition ident (t : Type) : Type := t.

  Global Instance Monad_ident : Monad ident :=
  { ret  := fun _ v => v
  ; bind := fun _ c1 _ c2 => c2 c1
  }.

End Ident.