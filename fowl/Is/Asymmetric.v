(** * Asymmetry *)

From DEZ Require Export
  Init.

(** ** Asymmetric Binary Relation *)

Fail Fail Class IsAsym (A : Type) (X : A -> A -> Prop) : Prop :=
  asym (x y : A) (a : X x y) (b : X y x) : 0.

Notation IsAsym := Asymmetric.
Notation asym := (asymmetry : IsAsym _).
