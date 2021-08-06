(** * Triangle Inequality *)

From Maniunfold.Has Require Export
  OrderRelations BinaryOperation Distance.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations AdditiveNotations.

Class IsTriangle (A B : Type)
  (HR : HasOrdRel A) (Hk : HasBinOp A) (Hd : HasDist A B) : Prop :=
  triangle (x y z : B) : dist x z <= dist x y + dist y z.
