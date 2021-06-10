From Maniunfold.Has Require Export
  OneSortedUnaryOperation TwoSortedRightAction.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations TwoSortedMultiplicativeNotations.

Local Open Scope grp_scope.
Local Open Scope r_mod_scope.

Class IsTwoRBinComm (A B : Type)
  `(HasUnOp B) `(HasRAct A B) : Prop :=
  two_r_bin_comm : forall (x : B) (a : A), - (x * a) = (- x) * a.
