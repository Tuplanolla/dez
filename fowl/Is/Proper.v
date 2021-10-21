(** * Respectfulness *)

From DEZ Require Export
  Init.

(** ** Respectful Morphism *)

Fail Fail Class IsProper (A : Type) (X : A -> A -> Prop) : Prop :=
  proper (x : A) : X x x.

Notation IsProper := Proper.
Notation proper := (proper_prf : IsProper _ _).
