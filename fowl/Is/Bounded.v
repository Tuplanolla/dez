(** * Boundedness *)

From DEZ Require Export
  Init.

(** * Lower Bound *)

Class IsLowerBnd (A : Type) (x : A) (R : A -> A -> Prop) : Prop :=
  lower_bnd (y : A) : R x y.

(** * Upper Bound *)

Class IsUpperBnd (A : Type) (x : A) (R : A -> A -> Prop) : Prop :=
  upper_bnd (y : A) : R y x.
