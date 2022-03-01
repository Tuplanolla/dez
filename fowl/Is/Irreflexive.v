(** * Irreflexivity *)

From DEZ Require Export
  Init.

(** ** Irreflexive Binary Relation *)

Fail Fail Class IsIrrefl (A : Type) (X : A -> A -> Prop) : Prop :=
  irrefl (x : A) (a : X x x) : 0.

Arguments irreflexivity {_ _ _} _ _.

Notation IsIrrefl := Irreflexive.
Notation irrefl := irreflexivity.
