(** * Deflationarity or Regressivity of a Function *)

From Maniunfold.Has Require Export
  OrderRelation.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations.

Class IsDeflate (A : Type) (R : HasOrdRel A) (f : A -> A) : Prop :=
  deflate (a : A) : f a <= a.
