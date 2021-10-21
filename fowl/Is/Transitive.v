(** * Transitivity *)

From DEZ Require Export
  Init.

(** ** Transitive Binary Relation *)

Fail Fail Class IsTrans (A : Type) (X : A -> A -> Prop) : Prop :=
  trans (x y z : A) (a : X x y) (b : X y z) : X x z.

Notation IsTrans := Transitive.
Notation trans := (transitivity : IsTrans _).
