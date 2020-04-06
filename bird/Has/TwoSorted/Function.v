From Maniunfold Require Export
  Init.

(* Function, mapping, morphism. *)

Class HasFn (A B : Type) : Type := fn : A -> B.

Typeclasses Transparent HasFn.
