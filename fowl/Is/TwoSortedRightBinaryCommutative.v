From Maniunfold.Has Require Export
  OneSortedUnaryOperation Action.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations TwoSortedMultiplicativeNotations.

Local Open Scope grp_scope.
Local Open Scope r_mod_scope.

Class IsTwoRBinComm (A B : Type)
  `(HasUnOp B) `(HasActR A B) : Prop :=
  two_r_bin_comm : forall (x : B) (a : A), - (x * a) = (- x) * a.
