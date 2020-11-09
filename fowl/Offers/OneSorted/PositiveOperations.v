From Coq Require Import
  PArith.PArith.
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation TwoSorted.LeftAction.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Section Context.

Context (A : Type) `(HasBinOp A).

Import Pos.

Definition positive_op (n : positive) (x : A) : A :=
  iter_op _+_ n x.

Global Arguments positive_op _ _ /.

Global Instance positive_A_has_l_act : HasLAct positive A := positive_op.

End Context.
