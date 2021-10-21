(** * Antisymmetry *)

From DEZ Require Export
  Init.

(** ** Antisymmetric Binary Relation *)

Fail Fail Class IsAntisym (A : Type) (X Y : A -> A -> Prop) : Prop :=
  antisym (x y : A) (a : Y x y) (b : Y y x) : X x y.

Notation IsAntisym X Y := (Antisymmetric _ X Y).
Notation antisym := (@antisymmetry _ _ _ _ _ : IsAntisym _ _).
