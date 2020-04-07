From Maniunfold Require Export
  Init.

(** Isomorphism, equivalence, bijection. *)

Class HasIso (A B : Type) : Type := iso : (A -> B) * (B -> A).

Typeclasses Transparent HasIso.
