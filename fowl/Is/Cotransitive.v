(** * Cotransitivity of a Binary Relation *)

From Maniunfold.Has Require Export
  BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Class IsCotrans (A : Type) (HR : HasBinRel A) : Prop :=
  cotrans (x y z : A) (a : x ~~ z) : x ~~ y \/ y ~~ z.
