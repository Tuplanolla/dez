(** * Boundedness *)

From DEZ Require Export
  Init.

(** * Lower Bound *)

Class IsLowerBnd (A : Type) (x : A) (X : A -> A -> Prop) : Prop :=
  lower_bnd (y : A) : X x y.

(** * Upper Bound *)

Class IsUpperBnd (A : Type) (x : A) (X : A -> A -> Prop) : Prop :=
  upper_bnd (y : A) : X y x.
