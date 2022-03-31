(** * Semigroup Structure *)

From DEZ.Is Require Export
  Equivalence Associative Proper.

(** ** Semigroup *)

Class IsSemigrp (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) : Prop := {
  semigrp_is_equiv :> IsEquiv X;
  semigrp_is_assoc :> IsAssoc X k;
  semigrp_is_proper :> IsProper (X ==> X ==> X) k;
}.
