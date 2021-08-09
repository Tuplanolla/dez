(** * Symmetry of a Binary Relation *)

From DEZ.Has Require Export
  BinaryRelation.
From DEZ.ShouldHave Require Import
  BinaryRelationNotations.

Fail Fail Class IsSym (A : Type) (HR : HasBinRel A) : Prop :=
  sym (x y : A) (a : x ~ y) : y ~ x.

Notation IsSym := Symmetric.
Notation sym := (symmetry : IsSym _).
