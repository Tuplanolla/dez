(** * Connexity of a Binary Relation *)

From Maniunfold.Has Require Export
  OneSortedBinaryRelation.
From Maniunfold.ShouldHave Require Import
  OneSortedBinaryRelationNotations.

Class IsConnex (A : Type) (R : HasBinRel A) : Prop :=
  connex (x y : A) : x ~~ y \/ y ~~ x.
