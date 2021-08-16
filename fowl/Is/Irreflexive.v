(** * Irreflexivity *)

From DEZ Require Export
  Init.

(** ** Irreflexive Binary Relation *)

Fail Fail Class IsIrrefl (A : Type) (R : A -> A -> Prop) : Prop :=
  irrefl (x : A) : ~ R x x.

Notation IsIrrefl := Irreflexive.
Notation irrefl := (irreflexivity : IsIrrefl _).
