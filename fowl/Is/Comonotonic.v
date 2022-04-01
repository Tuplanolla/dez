(** * Comonotonicity *)

From DEZ Require Export
  Init.

(** ** Comonotonic Unary Function *)

Class IsComonoUnFn (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Prop :=
  comono_un_fn (x y : A) (a : Y (f x) (f y)) : X x y.
