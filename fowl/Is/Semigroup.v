(** * Semigroup Structure *)

From DEZ.Is Require Export
  Equivalence Associative.

(** ** Semigroup *)

Class IsSemigrp (A : Type) (R : A -> A -> Prop) (k : A -> A -> A) : Prop := {
  is_eq :> IsEq R;
  is_assoc :> IsAssoc R k;
}.
