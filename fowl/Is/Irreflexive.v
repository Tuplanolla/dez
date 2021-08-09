(** * Irreflexivity of a Binary Relation *)

From DEZ.Has Require Export
  BinaryRelation.
From DEZ.ShouldHave Require Import
  BinaryRelationNotations.

Fail Fail Class IsIrrefl (A : Type) (HR : HasBinRel A) : Prop :=
  irrefl (x : A) : ~ (x ~ x).

Notation IsIrrefl := Irreflexive.
Notation irrefl := (irreflexivity : IsIrrefl _).
