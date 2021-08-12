(** * Symmetry *)

From DEZ Require Export
  Init.

Fail Fail Class IsSym (A : Type) (R : A -> A -> Prop) : Prop :=
  sym (x y : A) (a : R x y) : R y x.

(** ** Symmetric Binary Relation *)

Notation IsSym := Symmetric.
Notation sym := (symmetry : IsSym _).
