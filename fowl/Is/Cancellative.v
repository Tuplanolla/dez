(** * Cancellativity of a Binary Operation *)

From Maniunfold.Has Require Export
  BinaryOperation.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

(** This has the same shape as [mul_reg_l] and
    a different shape from [add_reg_l]. *)

Class IsCancelL (A : Type) (Hk : HasBinOp A) : Prop :=
  cancel_l (x y z : A) (a : x + z = y + z) : x = y.

(** This has the same shape as [mul_reg_r]. *)

Class IsCancelR (A : Type) (Hk : HasBinOp A) : Prop :=
  cancel_r (x y z : A) (a : z + x = z + y) : x = y.

Class IsCancelLR (A : Type) (Hk : HasBinOp A) : Prop := {
  is_cancel_l :> IsCancelL _+_;
  is_cancel_r :> IsCancelR _+_;
}.
