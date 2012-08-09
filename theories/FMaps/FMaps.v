(** First-class finite maps **)

Class Map (K V : Type) (T : Type) : Type :=
{ In       : K -> T -> Prop
; MapsTo   : K -> V -> T -> Prop
; add      : K -> V -> T -> T
; remove   : K -> T -> T
; find     : K -> T -> option V
}.




