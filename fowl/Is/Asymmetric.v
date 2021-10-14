(** * Asymmetry *)

From DEZ Require Export
  Init.

(** ** Asymmetric Binary Relation *)

Fail Fail Class IsAsym (A : Type) (R : A -> A -> Prop) : Prop :=
  asym (x y : A) (a : R x y) (b : R y x) : 0.

Notation IsAsym := Asymmetric.
Notation asym := (asymmetry : IsAsym _).
