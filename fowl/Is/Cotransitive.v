(** * Cotransitivity of a Binary Relation *)

From DEZ.Has Require Export
  BinaryRelation.
From DEZ.ShouldHave Require Import
  BinaryRelationNotations.

Class IsCotrans (A : Type) (HR : HasBinRel A) : Prop :=
  cotrans (x y z : A) (a : x ~ z) : x ~ y \/ y ~ z.
