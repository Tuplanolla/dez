(** * Irreflexivity *)

From DEZ Require Export
  Init.

(** ** Irreflexive Binary Relation *)

Fail Fail Class IsIrrefl (A : Type) (X : A -> A -> Prop) : Prop :=
  irrefl (x : A) : ~ X x x.

Notation IsIrrefl := Irreflexive.
Notation irrefl := (irreflexivity : IsIrrefl _).
