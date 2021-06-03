(** * Asymmetry of a Binary Relation *)

From Maniunfold.Has Require Export
  OneSortedBinaryRelation.
From Maniunfold.ShouldHave Require Import
  OneSortedBinaryRelationNotations.

Fail Fail Class IsAsym (A : Type) (R : HasBinRel A) : Prop :=
  asym (x y : A) (a : x ~~ y) (b : y ~~ x) : 0.

Notation IsAsym := Asymmetric.
Notation asym := (asymmetry : IsAsym _).
