(** * Asymmetry of a Binary Relation *)

From DEZ.Has Require Export
  BinaryRelation.
From DEZ.ShouldHave Require Import
  BinaryRelationNotations.

Fail Fail Class IsAsym (A : Type) (HR : HasBinRel A) : Prop :=
  asym (x y : A) (a : x ~ y) (b : y ~ x) : 0.

Notation IsAsym := Asymmetric.
Notation asym := (asymmetry : IsAsym _).
