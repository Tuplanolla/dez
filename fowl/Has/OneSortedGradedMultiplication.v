From Maniunfold.Has Require Export
  OneSortedBinaryOperation OneSortedGradedBinaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

(** Graded multiplication.
    See [Has.OneSortedMultiplication]. *)

Class HasGrdMul (A : Type) (P : A -> Type) `(HasBinOp A) : Type :=
  grd_mul : forall i j : A, P i -> P j -> P (i + j).

Typeclasses Transparent HasGrdMul.

Section Context.

Context (A : Type) (P : A -> Type) `(HasGrdMul A P).

Global Instance P_has_grd_bin_op : HasGrdBinOp P bin_op := grd_mul.

End Context.
