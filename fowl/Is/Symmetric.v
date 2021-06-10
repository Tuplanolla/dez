(** * Symmetry of a Binary Relation *)

From Maniunfold.Has Require Export
  BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Fail Fail Class IsSym (A : Type) (R : HasBinRel A) : Prop :=
  sym (x y : A) (a : x ~~ y) : y ~~ x.

Notation IsSym := Symmetric.
Notation sym := (symmetry : IsSym _).
