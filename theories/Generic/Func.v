Require Import Coq.Lists.List.

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

Require Import ExtLib.Data.HList.

Fixpoint get (domain : list Type) (range : Type) T (m : member T domain)
: (T -> asFunc domain range) -> asFunc domain range :=
  match m in member _ domain
        return (T -> asFunc domain range) -> asFunc domain range
  with
    | MZ _ => fun F x => F x x
    | MN _ _ m => fun F x => @get _ _ _ m (fun y => F y x)
  end.

Section combine.
  Context {T U V : Type}.
  Variable (join : T -> U -> V).

  Fixpoint combine (domain : list Type) {struct domain}
  : asFunc domain T -> asFunc domain U -> asFunc domain V :=
    match domain as domain
          return asFunc domain T -> asFunc domain U -> asFunc domain V
    with
      | nil => fun A B => join A B
      | d :: ds => fun A B => fun x => @combine ds (A x) (B x)
    end.
End combine.

Fixpoint under (domain : list Type) (range : Type)
         {struct domain}
: ((forall U, asFunc domain U -> U) -> range)
  -> asFunc domain range :=
  match domain as domain
        return ((forall U, asFunc domain U -> U) -> range)
               -> asFunc domain range
  with
    | nil => fun F => F (fun _ x => x)
    | d :: ds => fun F x =>
                   under ds range (fun App => F (fun U f => App U (f x)))
  end%type.