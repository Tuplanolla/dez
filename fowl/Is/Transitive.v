(** * Transitivity *)

From DEZ Require Export
  Init.

Fail Fail Class IsTrans (A : Type) (R : A -> A -> Prop) : Prop :=
  trans (x y z : A) (a : R x y) (b : R y z) : R x z.

(** ** Transitive Binary Relation *)

Notation IsTrans := Transitive.
Notation trans := (transitivity : IsTrans _).
