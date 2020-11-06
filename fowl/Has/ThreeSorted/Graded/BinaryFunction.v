From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

(** Graded binary function.
    See [Has.ThreeSorted.BinaryFunction]. *)

Class HasGrdBinFn (A : Type) (P Q R : A -> Type) `(HasBinOp A) : Type :=
  grd_bin_fn : forall i j : A, P i -> Q j -> R (i + j).

Typeclasses Transparent HasGrdBinFn.
