(* bad *)
From Maniunfold Require Export
  Init.

Class HasFn (A B : Type) : Type := fn : A -> B.

Typeclasses Transparent HasFn.
