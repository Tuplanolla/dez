(** * Semigroup Structure *)

From DEZ.Is Require Export
  Equivalence Associative Proper.

(** ** Semigroup *)

Class IsSemigrp (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop := {
  is_eq :> IsEq X;
  is_assoc :> IsAssoc X k;
  is_proper :> IsProper (X ==> X ==> X) k;
}.
