From Maniunfold.Has Require Export
  OneSorted.UnaryOperation TwoSorted.RightAction.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations TwoSorted.MultiplicativeNotations.

Local Open Scope r_act_scope.

Class IsTwoRBinComm (A B : Type)
  (B_has_un_op : HasUnOp B) (A_B_has_r_act : HasRAct A B) : Prop :=
  two_r_bin_comm : forall (x : B) (a : A), - (x * a) = (- x) * a.
