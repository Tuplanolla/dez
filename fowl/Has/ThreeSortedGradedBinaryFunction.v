From Maniunfold.Has Require Export
  OneSortedBinaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

(** Graded binary function.
    See [Has.ThreeSortedBinaryFunction]. *)

Class HasGrdBinFn (A : Type) (P Q R : A -> Type) `(HasBinOp A) : Type :=
  grd_bin_fn : forall i j : A, P i -> Q j -> R (i + j).

Typeclasses Transparent HasGrdBinFn.
