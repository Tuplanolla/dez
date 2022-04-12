(** * Irreflexivity *)

From Coq Require Import
  Classes.RelationClasses.
From DEZ Require Export
  Init.

(** ** Irreflexive Binary Relation *)

Fail Fail Class IsIrrefl (A : Type) (X : A -> A -> Prop) : Prop :=
  irrefl (x : A) (a : X x x) : 0.

Arguments Irreflexive {_} _.
Arguments irreflexivity {_ _ _} _ _.

Notation IsIrrefl := Irreflexive.
Notation irrefl := irreflexivity.
