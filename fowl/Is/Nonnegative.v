(** * Nonnegativity *)

From DEZ Require Export
  Init.

(** ** Nonnegative Form *)

Class IsNonnegForm (A B : Type) (X : A -> A -> Prop)
  (x : A) (s : B -> B -> A) : Prop :=
  nonneg_form (a b : B) : X x (s a b).
