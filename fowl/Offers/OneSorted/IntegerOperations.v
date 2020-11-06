From Coq Require Import
  ZArith.ZArith.
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation TwoSorted.LeftAction.
From Maniunfold.Offers Require Export
  OneSorted.PositiveOperations.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Section Context.

Context (A : Type) `(HasBinOp A) `(HasNullOp A) `(HasUnOp A).

Definition z_op (n : Z) (x : A) : A :=
  match n with
  | Z0 => 0
  | Zpos p => positive_op p x
  | Zneg p => - positive_op p x
  end.

Global Instance Z_A_has_l_act : HasLAct Z A := z_op.

End Context.

Arguments z_op {_ _ _ _} !_ _.
