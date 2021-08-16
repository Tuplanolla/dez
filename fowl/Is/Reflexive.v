(** * Reflexivity *)

From DEZ Require Export
  Init.

(** ** Reflexive Binary Relation *)

Fail Fail Class IsRefl (A : Type) (R : A -> A -> Prop) : Prop :=
  refl (x : A) : R x x.

Notation IsRefl := Reflexive.
Notation refl := (reflexivity : IsRefl _).
