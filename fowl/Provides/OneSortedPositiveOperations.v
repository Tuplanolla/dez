From Coq Require Import
  PArith.PArith.
From DEZ.Has Require Export
  Action.
From DEZ.Is Require Export
  Semigroup.
From DEZ.Supports Require Import
  OneSortedAdditiveNotations.

Section Context.

Context (A : Type) (Hk : HasBinOp A) `(IsSemigrp A).

Import Pos.

Definition positive_op (n : positive) (x : A) : A :=
  iter_op _+_ n x.

Global Instance positive_A_has_act_l : HasActL positive A := positive_op.

End Context.

Arguments positive_op {_} _ !_ _.
