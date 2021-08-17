(** * Fixed Points *)

From DEZ Require Export
  Init.

(** ** Fixed Point of a Function *)

Class IsFixed2 (A B : Type) (R : B -> A -> Prop) (x : A) (f : A -> B) : Prop :=
  fixed : R (f x) x.

Class IsFixed (A : Type) (R : A -> A -> Prop) (x : A) (f : A -> A) : Prop :=
  is_fixed_2 :> IsFixed2 R x f.
