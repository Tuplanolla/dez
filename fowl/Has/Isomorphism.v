(** Isomorphism, Proof-Irrelevant Equivalence, Bijection *)

From Maniunfold Require Export
  Init.

Class HasIso (A B : Type) : Type := iso : (A -> B) * (B -> A).

Typeclasses Transparent HasIso.
