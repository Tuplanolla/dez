(** * Transitivity *)

From DEZ Require Export
  Init.

(** ** Transitive Binary Relation *)

Fail Fail Class IsTrans (A : Type) (R : A -> A -> Prop) : Prop :=
  trans (x y z : A) (a : R x y) (b : R y z) : R x z.

Notation IsTrans := Transitive.
Notation trans := (transitivity : IsTrans _).
