Section bin_op.
  Context {T : Type}.
  Variable op : T -> T -> T.
  Variable equ : T -> T -> Prop.

  Class Associative : Type :=
  { assoc : forall a b c, equ (op (op a b) c) (op a (op b c)) }.
  
  Class Commutative : Type :=
  { commut : forall a b, equ (op a b) (op b a) }.
  
End bin_op.
