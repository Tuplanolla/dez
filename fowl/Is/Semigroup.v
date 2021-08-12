(** * Algebraic Structure *)

From DEZ.Is Require Export
  Magma Associative.

(** ** Semigroup *)

Class IsSemigrp (A : Type) (k : A -> A -> A) : Prop := {
  is_mag :> IsMag eq k;
  is_assoc :> IsAssoc k;
}.
