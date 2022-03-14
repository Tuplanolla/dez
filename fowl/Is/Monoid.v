(** * Monoidal Structure *)

From DEZ.Is Require Export
  Semigroup Unital Associative.

(** ** Monoid *)

Class IsMon (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop := {
  mon_is_semigrp :> IsSemigrp X k;
  mon_is_unl_elem :> IsUnlElem X x k;
}.
