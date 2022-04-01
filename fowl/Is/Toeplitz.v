(** * Toeplitzity *)

From DEZ Require Export
  Init.

(** ** Toeplitz Form *)

Class IsToeplitzForm (A B : Type) (X : A -> A -> Prop)
  (x : A) (s : B -> B -> A) : Prop :=
  toeplitz_form (a : B) : X (s a a) x.
