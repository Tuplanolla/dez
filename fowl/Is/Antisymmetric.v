(** * Antisymmetry of a Binary Relation *)

From Maniunfold.Has Require Export
  BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Fail Fail Class IsAntisym (A : Type) (R : HasBinRel A) : Prop :=
  antisym (x y : A) (a : x ~~ y) (b : y ~~ x) : x = y.

Notation IsAntisym R := (Antisymmetric _ _=_ R).
Notation antisym := (@antisymmetry _ _ _ _ _ : IsAntisym _).
