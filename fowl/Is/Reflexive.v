(** * Reflexivity *)

From DEZ Require Export
  Init.

(** ** Reflexive Binary Relation *)

Fail Fail Class IsRefl (A : Type) (X : A -> A -> Prop) : Prop :=
  refl (x : A) : X x x.

Notation IsRefl := Reflexive.
Notation refl := (reflexivity : IsRefl _).
