Require Import List.
Require Import Monad.
Require Import Monad.Folds.

Set Implicit Arguments.
Set Strict Implicit.

Module FunNotation.

  Notation "f $ x" := (f x)
    (at level 99, x at level 99, right associativity, only parsing).

  Notation "'begin' e1 'end'" := ((e1))
    (at level 0, only parsing).

End FunNotation.

Definition compose A B C (g:B -> C) (f:A -> B) (x:A) : C := g (f x).

Definition forEach A B (xs:list A) (f:A -> B) : list B := map f xs.

Definition forEachM {m} {M:Monad m} {A B} (xs:list A) (f:A -> m B) : m (list B) :=
  mapM f xs.

Section MonadFixDefs.
  Context {m} {mFix:MonadFix m}.

  Definition mfix2 {A B C}
    (ff:(A -> B -> m C) -> (A -> B -> m C)) (a:A) (b:B) : m C :=
      let ff' fabp (abp:A*B) :=
        let (a,b) := abp in
        let fab a b := fabp (a,b) in
        ff fab a b
      in
      mfix ff' (a,b)
  .

  Definition mfix3 {A B C D}
    (ff:(A -> B -> C -> m D) -> (A -> B -> C -> m D))
    (a:A) (b:B) (c:C) : m D :=
      let ff' fabcp (abcp:A*B*C) :=
        let (abp,c) := abcp in
        let (a,b) := abp in
        let fabc a b c := fabcp (a,b,c) in
        ff fabc a b c
      in
      mfix ff' (a,b,c)
  .
End MonadFixDefs.

