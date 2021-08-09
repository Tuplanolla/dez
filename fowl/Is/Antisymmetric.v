(** * Antisymmetry of a Binary Relation *)

From DEZ.Has Require Export
  BinaryRelation.
From DEZ.ShouldHave Require Import
  BinaryRelationNotations.

Fail Fail Class IsAntisym (A : Type) (HR : HasBinRel A) : Prop :=
  antisym (x y : A) (a : x ~ y) (b : y ~ x) : x = y.

Notation IsAntisym := (Antisymmetric _ _=_).
Notation antisym := (@antisymmetry _ _ _ _ _ : IsAntisym _).
