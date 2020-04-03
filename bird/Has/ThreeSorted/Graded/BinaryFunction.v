From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class HasGrdBinFn {A : Type} (P Q R : A -> Type)
  {A_has_bin_op : HasBinOp A} : Type :=
  grd_bin_fn : forall i j : A, P i -> Q j -> R (i + j).

Typeclasses Transparent HasGrdBinFn.
