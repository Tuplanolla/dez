From Maniunfold Require Export
  Init.

(** Proof irrelevance, homotopical contractibility. *)

Class HasPrfIrrel (A : Type) : Type := prf_irrel : forall x y : A, x = y.

Hint Mode HasPrfIrrel ! : typeclass_instances.

Typeclasses Transparent HasPrfIrrel.
