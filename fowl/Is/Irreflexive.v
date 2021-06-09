(** * Irreflexivity of a Binary Relation *)

From Maniunfold.Has Require Export
  BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Fail Fail Class IsIrrefl (A : Type) (R : HasBinRel A) : Prop :=
  irrefl (x : A) : ~ (x ~~ x).

Notation IsIrrefl R := (Irreflexive R).
Notation irrefl := (irreflexivity : IsIrrefl _).
