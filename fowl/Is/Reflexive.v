(** * Reflexivity *)

From Coq Require Import
  Classes.RelationClasses.
From DEZ Require Export
  Init.

(** ** Reflexive Binary Relation *)

Fail Fail Class IsRefl (A : Type) (X : A -> A -> Prop) : Prop :=
  refl (x : A) : X x x.

Arguments Reflexive {_} _.
Arguments reflexivity {_ _ _} _.

Notation IsRefl := Reflexive.
Notation refl := reflexivity.
