(** * Reflexivity of a Binary Relation *)

From Maniunfold.Has Require Export
  BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Fail Fail Class IsRefl (A : Type) (R : HasBinRel A) : Prop :=
  refl (x : A) : x ~~ x.

Notation IsRefl R := (Reflexive R).
Notation refl := (reflexivity : IsRefl _).
