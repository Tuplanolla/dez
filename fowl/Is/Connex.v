(* bad *)
From Maniunfold.Has Require Export
  OneSortedBinaryRelation.
From Maniunfold.ShouldHave Require Import
  OneSortedBinaryRelationNotations.

Class IsConnex (A : Type) `(HasBinRel A) : Prop :=
  connex : forall x y : A, x ~~ y \/ y ~~ x.
