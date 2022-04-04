(** * Subrelations and Superrelations *)

From DEZ Require Export
  Init.

(** ** Subrelation of a Binary Relation *)

Fail Fail Class IsSubrel (A : Type) (Xsub Xsup : A -> A -> Prop) : Prop :=
  subrel (x y : A) (a : Xsub x y) : Xsup x y.

Arguments is_subrelation {_ _ _ _} _ _ _.

Notation IsSubrel := subrelation.
Notation subrel := is_subrelation.
