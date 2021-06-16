(** * Contractivity or Shortness of a Function *)

From Maniunfold.Has Require Export
  Distance OrderRelations.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations.

Class IsContract (A B C : Type)
  (R : HasOrdRel C) (dA : HasDist A C) (dB : HasDist B C)
  (f : A -> B) : Prop :=
  expand (x y : A) : dist (f x) (f y) <= dist x y.
