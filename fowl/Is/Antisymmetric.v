(** * Antisymmetry *)

From DEZ Require Export
  Init.

(** ** Antisymmetric Binary Relation *)

Fail Fail Class IsAntisym (A : Type) (R S : A -> A -> Prop) : Prop :=
  antisym (x y : A) (a : S x y) (b : S y x) : R x y.

Notation IsAntisym R S := (Antisymmetric _ R S).
Notation antisym := (@antisymmetry _ _ _ _ _ : IsAntisym _ _).
