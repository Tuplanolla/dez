From Maniunfold.Has Require Export
  BinaryOperation GradedBinaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

(** Graded addition.
    See [Has.OneSortedAddition]. *)

Class HasGrdAdd (A : Type) (P : A -> Type) `(HasBinOp A) : Type :=
  grd_add : forall i j : A, P i -> P j -> P (i + j).

Typeclasses Transparent HasGrdAdd.

Section Context.

Context (A : Type) (P : A -> Type) `(HasGrdAdd A P).

Global Instance P_has_grd_bin_op : HasGrdBinOp P bin_op := grd_add.

End Context.
