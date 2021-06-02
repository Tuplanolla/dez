(** * Irreflexivity of a Binary Relation *)

From Maniunfold.Has Require Export
  OneSortedBinaryRelation.
From Maniunfold.ShouldHave Require Import
  OneSortedBinaryRelationNotations.

Fail Fail Class IsIrrefl (A : Type) (R : HasBinRel A) : Prop :=
  irrefl (x : A) : ~ (x ~~ x).

Notation IsIrrefl := Irreflexive.
Notation irrefl := (irreflexivity : IsIrrefl _).
