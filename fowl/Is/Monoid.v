(** * Monoidal Structure *)

From DEZ.Is Require Export
  Semigroup Unital.

(** ** Monoid *)

Class IsMon (A : Type) (R : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop := {
  is_semigrp :> IsSemigrp R k;
  is_unl_l_r :> IsUnlLR R x k;
}.
