From Maniunfold.Has Require Export
  OneSorted.UnaryOperation TwoSorted.LeftAction.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations TwoSorted.MultiplicativeNotations.

Local Open Scope l_mod_scope.

Class IsTwoLBinComm (A B : Type)
  `(HasUnOp B) `(HasLAct A B) : Prop :=
  two_l_bin_comm : forall (a : A) (x : B), - (a * x) = a * (- x).
