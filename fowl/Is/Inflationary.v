(** * Inflationarity or Progressivity of a Function *)

From Maniunfold.Has Require Export
  OrderRelations.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations.

Class IsInflate (A : Type) (HR : HasOrdRel A) (f : A -> A) : Prop :=
  inflate (a : A) : a <= f a.
