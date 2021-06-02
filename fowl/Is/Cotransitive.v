(** * Cotransitivity of a Binary Relation *)

From Maniunfold.Has Require Export
  OneSortedBinaryRelation.
From Maniunfold.ShouldHave Require Import
  OneSortedBinaryRelationNotations.

Class IsCotrans (A : Type) (R : HasBinRel A) : Prop :=
  cotrans (x y z : A) (a : x ~~ z) : x ~~ y \/ y ~~ z.
