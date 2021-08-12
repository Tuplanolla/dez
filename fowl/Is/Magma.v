(** * Algebraic Structure *)

From DEZ.Is Require Export
  Equivalence.

(** ** Groupoid *)
(** ** Magma *)

Class IsMag (A : Type) (R : A -> A -> Prop) (k : A -> A -> A) : Prop :=
  is_eq :> IsEq R.
