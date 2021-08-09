(** * Contractivity or Shortness of a Function *)

From DEZ.Has Require Export
  Distance OrderRelations.
From DEZ.ShouldHave Require Import
  OrderRelationNotations.

Class IsContract (A B C : Type)
  (HR : HasOrdRel C) (HdA : HasDist C A) (HdB : HasDist C B)
  (f : A -> B) : Prop :=
  contract (x y : A) : dist (f x) (f y) <= dist x y.
