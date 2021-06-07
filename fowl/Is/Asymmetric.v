(** * Asymmetry of a Binary Relation *)

From Maniunfold.Has Require Export
  BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Fail Fail Class IsAsym (A : Type) (R : HasBinRel A) : Prop :=
  asym (x y : A) (a : x ~~ y) (b : y ~~ x) : 0.

Notation IsAsym := Asymmetric.
Notation asym := (asymmetry : IsAsym _).
