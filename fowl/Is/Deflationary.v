(** * Deflationarity or Regressivity of a Function *)

From Maniunfold.Has Require Export
  OrderRelations.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations.

Class IsDeflate (A : Type) (HR : HasOrdRel A) (f : A -> A) : Prop :=
  deflate (a : A) : f a <= a.
