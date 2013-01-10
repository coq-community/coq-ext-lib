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

Fixpoint const {D R} (r : R) : asFunc D R :=
  match D with
    | nil => r
    | _ :: D => fun _ => const r
  end.

Fixpoint uncurry {D R} {struct D} : (asTuple D -> R) -> asFunc D R :=
  match D as D return (asTuple D -> R) -> asFunc D R with
    | nil => fun x => x tt
    | d :: D => fun f d => uncurry (fun x => f (d, x))
  end.

Fixpoint curry {D R} {struct D} : asFunc D R -> (asTuple D -> R) :=
  match D as D return asFunc D R -> (asTuple D -> R) with
    | nil => fun x _ => x
    | d :: D => fun f x => curry (f (fst x)) (snd x)
  end.
