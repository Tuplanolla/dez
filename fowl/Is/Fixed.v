(** * Fixed Points *)

From DEZ Require Export
  Init.

(** ** Fixed Point of a Function *)

Class IsFixed (A : Type) (x : A) (f : A -> A) : Prop :=
  fixed : f x = x.
