(** * Reflexivity of a Binary Relation *)

From Maniunfold.Has Require Export
  BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Fail Fail Class IsRefl (A : Type) (HR : HasBinRel A) : Prop :=
  refl (x : A) : x ~~ x.

Notation IsRefl := Reflexive.
Notation refl := (reflexivity : IsRefl _).
