(** * Lower and Upper Bound *)

From Maniunfold.Has Require Export
  OrderRelations.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations.

Class IsLowerBnd (A : Type) (x : A) (HR : HasOrdRel A) : Prop :=
  lower_bnd (y : A) : x <= y.

Class IsUpperBnd (A : Type) (x : A) (HR : HasOrdRel A) : Prop :=
  upper_bnd (y : A) : y <= x.
