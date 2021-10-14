(** * Injectivity *)

From DEZ Require Export
  Init.

(** ** Injective Function *)

Class IsInj (A B : Type) (R : B -> B -> Prop) (S : A -> A -> Prop)
  (f : A -> B) : Prop :=
  inj (x y : A) (a : R (f x) (f y)) : S x y.
