From Maniunfold.Has Require Export
  OneSorted.UnaryOperation TwoSorted.LeftAction.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations TwoSorted.MultiplicativeNotations.

Local Open Scope l_act_scope.

Class IsTwoLBinComm (A B : Type)
  (B_has_un_op : HasUnOp B) (A_B_has_l_act : HasLAct A B) : Prop :=
  two_l_bin_comm : forall (a : A) (x : B), - (a * x) = a * (- x).
