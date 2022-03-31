(** * Subrelation *)

From DEZ Require Export
  Init.

(** ** Subrelation of a Binary Relation *)

Fail Fail Class IsSubrel (A : Type) (X Y : A -> A -> Prop) : Prop :=
  subrel (x y : A) (a : X x y) : Y x y.

Arguments is_subrelation {_ _ _ _} _ _ _.

Notation IsSubrel := subrelation.
Notation subrel := is_subrelation.
