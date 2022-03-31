(** * Boundedness *)

From DEZ Require Export
  Init.

(** ** Lower Bound *)

Class IsLowerBnd (A : Type) (X : A -> A -> Prop) (x : A) : Prop :=
  lower_bnd (y : A) : X x y.

(** ** Upper Bound *)

Class IsUpperBnd (A : Type) (X : A -> A -> Prop) (x : A) : Prop :=
  upper_bnd (y : A) : X y x.
