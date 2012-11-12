Require Import List.

Fixpoint asFunc (domain : list Type) (range : Type) : Type :=
  match domain with
    | nil => range
    | d :: ds => d -> asFunc ds range
  end.

Fixpoint asTuple (domain : list Type) : Type :=
  match domain with
    | nil => unit
    | d :: ds => prod d (asTuple ds)
  end.

Fixpoint applyF {domain : list Type} {range : Type}
  : asFunc domain range -> asTuple domain -> range :=
  match domain as domain 
    return asFunc domain range -> asTuple domain -> range
    with
    | nil => fun x _ => x
    | d :: ds => fun f x_xs => applyF (f (fst x_xs)) (snd x_xs)
  end.
