From Maniunfold.Has Require Export
  OneSorted.UnaryOperation TwoSorted.RightAction.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations TwoSorted.MultiplicativeNotations.

Local Open Scope r_mod_scope.

Class IsTwoRBinComm (A B : Type)
  `(HasUnOp B) `(HasRAct A B) : Prop :=
  two_r_bin_comm : forall (x : B) (a : A), - (x * a) = (- x) * a.
