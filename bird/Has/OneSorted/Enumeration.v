(* bad *)
From Maniunfold Require Export
  Init.

Class HasEnum (A : Type) : Type := enum : list A.

Typeclasses Transparent HasEnum.
