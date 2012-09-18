Require Import Monad.

Set Implicit Arguments.
Set Strict Implicit.

Section Ident.
  Inductive ident A := mkIdent { unIdent : A }.

  Global Instance Monad_ident : Monad ident :=
  { ret  := fun _ v => mkIdent v
  ; bind := fun _ c _ f => f (unIdent c)
  }.

End Ident.