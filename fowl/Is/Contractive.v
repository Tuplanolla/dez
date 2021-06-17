(** * Contractivity or Shortness of a Function *)

From Maniunfold.Has Require Export
  Distance OrderRelations.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations.

Class IsContract (A B C : Type)
  (HR : HasOrdRel C) (HdA : HasDist A C) (HdB : HasDist B C)
  (f : A -> B) : Prop :=
  expand (x y : A) : dist (f x) (f y) <= dist x y.
