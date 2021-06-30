(** * Injectivity of a Function *)

From Maniunfold Require Export
  Init.

Class IsInj (A B : Type) (f : A -> B) : Prop :=
  inj (x y : A) (a : f x = f y) : x = y.
