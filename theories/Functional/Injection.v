Set Implicit Arguments.
Set Maximal Implicit Insertion.

Class Injection x t := { inject : x -> t }.
Class Projection x t := { project : t -> x ; pmodify : (x -> x) -> (t -> t) }.
