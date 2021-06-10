(** * Transitivity of a Binary Relation *)

From Maniunfold.Has Require Export
  BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Fail Fail Class IsTrans (A : Type) (R : HasBinRel A) : Prop :=
  trans (x y z : A) (a : x ~~ y) (b : y ~~ z) : x ~~ z.

Notation IsTrans := Transitive.
Notation trans := (transitivity : IsTrans _).
