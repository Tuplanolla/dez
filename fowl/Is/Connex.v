(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Class IsConnex (A : Type) `(HasBinRel A) : Prop :=
  connex : forall x y : A, x ~~ y \/ y ~~ x.
