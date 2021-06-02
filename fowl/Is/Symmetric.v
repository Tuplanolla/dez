(** * Symmetry of a Binary Relation *)

From Maniunfold.Has Require Export
  OneSortedBinaryRelation.
From Maniunfold.ShouldHave Require Import
  OneSortedBinaryRelationNotations.

Fail Fail Class IsSym (A : Type) (R : HasBinRel A) : Prop :=
  sym (x y : A) (a : x ~~ y) : y ~~ x.

Notation IsSym := Symmetric.
Notation sym := (symmetry : IsSym _).
