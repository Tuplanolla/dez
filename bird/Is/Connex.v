From Maniunfold.Has Require Export
  OneSorted.BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Class IsConnex {A : Type} (A_has_bin_rel : HasBinRel A) : Prop :=
  connex : forall x y : A, x ~~ y \/ y ~~ x.
