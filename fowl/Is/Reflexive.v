(** * Reflexivity *)

From DEZ Require Export
  Init.

Fail Fail Class IsRefl (A : Type) (R : A -> A -> Prop) : Prop :=
  refl (x : A) : R x x.

(** ** Reflexive Binary Relation *)

Notation IsRefl := Reflexive.
Notation refl := (reflexivity : IsRefl _).
