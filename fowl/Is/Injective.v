(** * Injectivity *)

From DEZ Require Export
  Init.

(** ** Injective Function *)

Class IsInj (A B : Type) (f : A -> B) : Prop :=
  inj (x y : A) (a : f x = f y) : x = y.
