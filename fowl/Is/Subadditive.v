(** * Subadditivity or Triangle Inequality *)

From DEZ.Has Require Export
  OrderRelations Operations Distances.
From DEZ.Supports Require Import
  OrderNotations AdditiveNotations.

Class IsSubadd (A B : Type)
  (HR : HasOrdRel A) (Hk : HasBinOp A) (Hd : HasDist A B) : Prop :=
  subadd (x y z : B) : dist x z <= dist x y + dist y z.
