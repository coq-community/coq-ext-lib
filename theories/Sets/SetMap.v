Require Import ExtLib.FMaps.FMaps.
Require Import ExtLib.Sets.Sets.

Set Implicit Arguments.
Set Strict Implicit.

(** Canonical instance, a set is the same as a map where the values
 ** are unit
 **)
Section SetFromMap.
  Variable T : Type.
  Variable R : T -> T -> Prop.

  Variable m : Type -> Type.
  Variable Map_T : Map T m.

  Global Instance CSet_map : @CSet (m unit) T R :=
  { empty := FMaps.empty
  ; contains := fun k m => match lookup k m with
                             | None => false
                             | Some _ => true
                           end
  ; add := fun k m => FMaps.add k tt m
  ; remove := fun k m => FMaps.remove k m
  }.
End SetFromMap.