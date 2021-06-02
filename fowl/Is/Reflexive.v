(** * Reflexivity of a Binary Relation *)

From Maniunfold.Has Require Export
  OneSortedBinaryRelation.
From Maniunfold.ShouldHave Require Import
  OneSortedBinaryRelationNotations.

Fail Fail Class IsRefl (A : Type) (R : HasBinRel A) : Prop :=
  refl (x : A) : x ~~ x.

Notation IsRefl := Reflexive.
Notation refl := (reflexivity : IsRefl _).
