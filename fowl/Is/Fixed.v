(** * Fixed Points *)

From DEZ Require Export
  Init.

(** ** Fixed Point of a Unary Operation *)

Class IsFixed (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) : Prop :=
  fixed : X (f x) x.
