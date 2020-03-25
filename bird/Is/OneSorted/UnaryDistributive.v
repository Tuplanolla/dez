From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.UnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class IsUnDistr {A : Type}
  (A_has_bin_op : HasBinOp A) (A_has_un_op : HasUnOp A) : Prop :=
  un_distr : forall x y : A, - (x + y) = - x + - y.
