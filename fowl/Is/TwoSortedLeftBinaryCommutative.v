From Maniunfold.Has Require Export
  OneSortedUnaryOperation TwoSortedLeftAction.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations TwoSortedMultiplicativeNotations.

Local Open Scope grp_scope.
Local Open Scope l_mod_scope.

Class IsTwoLBinComm (A B : Type)
  `(HasUnOp B) `(HasLAct A B) : Prop :=
  two_l_bin_comm : forall (a : A) (x : B), - (a * x) = a * (- x).
