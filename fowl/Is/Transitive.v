(** * Transitivity of a Binary Relation *)

From DEZ.Has Require Export
  BinaryRelation.
From DEZ.ShouldHave Require Import
  BinaryRelationNotations.

Fail Fail Class IsTrans (A : Type) (HR : HasBinRel A) : Prop :=
  trans (x y z : A) (a : x ~ y) (b : y ~ z) : x ~ z.

Notation IsTrans := Transitive.
Notation trans := (transitivity : IsTrans _).
