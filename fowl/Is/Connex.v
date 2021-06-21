(** * Connexity or Connectedness or Totality of a Binary Relation *)

From Maniunfold.Has Require Export
  BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

(** This has the same shape as [le_ge_cases]. *)

Class IsConnex (A : Type) (HR : HasBinRel A) : Prop :=
  connex (x y : A) : x ~ y \/ y ~ x.
