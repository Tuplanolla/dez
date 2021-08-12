(** * Monoidal Structure *)

From DEZ.Is Require Export
  Semigroup Unital.

(** ** Monoid *)

Class IsMon (A : Type) (x : A) (k : A -> A -> A) : Prop := {
  is_semigrp :> IsSemigrp k;
  is_unl_l_r :> IsUnlLR x k;
}.
