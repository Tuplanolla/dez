(** * Reflexivity of a Binary Relation *)

From DEZ.Has Require Export
  BinaryRelation.
From DEZ.ShouldHave Require Import
  BinaryRelationNotations.

Fail Fail Class IsRefl (A : Type) (HR : HasBinRel A) : Prop :=
  refl (x : A) : x ~ x.

Notation IsRefl := Reflexive.
Notation refl := (reflexivity : IsRefl _).
