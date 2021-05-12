From Maniunfold Require Export
  Init.

(** Predicate, propositional function. *)

Class HasPred (A : Type) : Type := pred : A -> Prop.

Typeclasses Transparent HasPred.
