(** * Fixed Points *)

From DEZ Require Export
  Init.

(** ** Fixed Point of a Function *)

Class IsFixed2 (A B : Type) (X : B -> A -> Prop) (x : A) (f : A -> B) : Prop :=
  fixed : X (f x) x.

Class IsFixed (A : Type) (X : A -> A -> Prop) (x : A) (f : A -> A) : Prop :=
  is_fixed_2 :> IsFixed2 X x f.
