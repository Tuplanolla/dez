(** * Deflationarity or Regressivity of a Function and a Binary Operation *)

From DEZ.Has Require Export
  OrderRelations BinaryOperation.
From DEZ.ShouldHave Require Import
  OrderRelationNotations AdditiveNotations.

Class IsDefl (A : Type) (HR : HasOrdRel A) (f : A -> A) : Prop :=
  defl (x : A) : f x <= x.

Class IsDeflBinOpL (A : Type) (HR : HasOrdRel A) (Hk : HasBinOp A) : Prop :=
  defl_bin_op_l (x y : A) : x + y <= y.

Class IsDeflBinOpR (A : Type) (HR : HasOrdRel A) (Hk : HasBinOp A) : Prop :=
  defl_bin_op_r (x y : A) : x + y <= x.
