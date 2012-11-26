Require Import BinPos.
Require Import ExtLib.Programming.Show.

Global Instance Show_positive : Show positive :=
{ show p := show (Pos.to_nat p) }.