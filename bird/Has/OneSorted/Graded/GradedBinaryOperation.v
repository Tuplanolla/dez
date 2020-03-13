From Maniunfold.Has Require Export
  BinaryOperation.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Class HasGrdBinOp {A : Type} (P : A -> Type)
  {has_bin_op : HasBinOp A} : Type :=
  grd_bin_op : forall i j : A, P i -> P j -> P (i + j).

Typeclasses Transparent HasGrdBinOp.
