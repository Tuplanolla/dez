(** * Strict Connexity or Strong Connectedness or Completeness of a Binary Relation *)

From DEZ.Has Require Export
  BinaryRelation.
From DEZ.ShouldHave Require Import
  BinaryRelationNotations.

(** This has the same shape as [lt_trichotomy]. *)

Class IsStrConnex (A : Type) (HR : HasBinRel A) : Prop :=
  str_connex (x y : A) : x ~ y \/ x = y \/ y ~ x.
