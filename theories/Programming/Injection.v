Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Class Injection (x : Type) (t : Type) := inject : x -> t.
(*
Class Projection x t := { project : t -> x ; pmodify : (x -> x) -> (t -> t) }.
*)

#[global]
Instance Injection_refl {T : Type} : Injection T T :=
{ inject := @id T }.

#[global]
Instance Injection_ascii_string : Injection ascii string :=
  { inject a := String a EmptyString }.
#[global]
Instance Injection_ascii_string_cons : Injection ascii (string -> string) :=
  { inject := String }.
