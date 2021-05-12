From Coq Require Import
  PArith.PArith.
From Maniunfold.Has Require Export
  TwoSortedLeftAction.
From Maniunfold.Is Require Export
  OneSortedSemigroup.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

Section Context.

Context (A : Type) `{IsSgrp A}.

Import Pos.

Definition positive_op (n : positive) (x : A) : A :=
  iter_op _+_ n x.

Global Instance positive_A_has_l_act : HasLAct positive A := positive_op.

End Context.

Arguments positive_op {_} _ !_ _.
