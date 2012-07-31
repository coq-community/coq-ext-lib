Section Equiv.
  Variable T : Type.
  Variable equ : T -> T -> Prop.
  
  Variable op : T -> T -> T.

  
  Class Commutative : Prop :=
    { Comm : forall a b, equ (op a b) (op b a)
    }.

  Class Associative : Prop :=
    { Assoc : forall a b c, equ (op a (op b c)) (op (op a b) c)
    }.

  Definition SemiGroup := Associative.

  Variable ident : T.

  Class LeftIdent : Prop :=
    { LIdent : forall a, equ (op ident a) a
    }.

  Class RightIdent : Prop :=
    { RIdent : forall a, equ (op a ident) a
    }.

  Class Monoid : Prop :=
    { MonoidSemiGroup :> Associative
    ; MonoidLeftIdent :> LeftIdent
    ; MonoidRightIdent :> RightIdent
    }.

  Class Group : Prop :=
    { GroupMonoid :> Monoid
    ; GroupInv : forall a, exists b, equ (op a b) ident
    }.

  Class GroupDec (G : Group) : Type :=
    { group_inv : T -> T
    ; group_invOkL : forall x, equ (op (group_inv x) x) ident
    ; group_invOkR : forall x, equ (op x (group_inv x)) ident
    }.

  Existing Class SemiGroup.
  Typeclasses Transparent SemiGroup.

  

  Goal forall (G : Group) a b c,
    equ (op a (op b c)) (op (op a b) c).
    Require Import Coq.Setoids.Setoid.
    intros.  eapply Assoc.

End Equiv.
  