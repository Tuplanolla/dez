(** * Connexity or Connectedness or Totality of a Binary Relation *)

From Maniunfold.Has Require Export
  BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Class IsConnex (A : Type) (R : HasBinRel A) : Prop :=
  connex (x y : A) : x ~~ y \/ y ~~ x.
