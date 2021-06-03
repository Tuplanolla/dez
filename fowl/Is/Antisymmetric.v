(** * Antisymmetry of a Binary Relation *)

From Maniunfold.Has Require Export
  OneSortedBinaryRelation.
From Maniunfold.ShouldHave Require Import
  OneSortedBinaryRelationNotations.

Fail Fail Class IsAntisym (A : Type) (R : HasBinRel A) : Prop :=
  antisym (x y : A) (a : x ~~ y) (b : y ~~ x) : x = y.

Notation IsAntisym := (Antisymmetric _ _=_).
Notation antisym := (@antisymmetry _ _ _ _ _ : IsAntisym _).
