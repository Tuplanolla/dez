(** * Monoidal Structure *)

From DEZ.Is Require Export
  Semigroup Unital.

(** ** Monoid *)

Class IsMon (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop := {
  is_semigrp :> IsSemigrp X k;
  is_unl_l_r :> IsUnlLR X x k;
}.
