(** * Respectfulness *)

From DEZ Require Export
  Init.

(** ** Respectful Morphism *)

Fail Fail Class IsProper (A : Type) (R : A -> A -> Prop) : Prop :=
  proper (x : A) : R x x.

Notation IsProper := Proper.
Notation proper := (proper_prf : IsProper _ _).
