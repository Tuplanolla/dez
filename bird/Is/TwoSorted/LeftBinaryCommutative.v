From Maniunfold.Has Require Export
  OneSorted.LeftUnaryOperation TwoSorted.RightAction.
From Maniunfold.ShouldHave Require Import
  TwoSorted.AdditiveNotations.

Class IsTwoLBinComm (A B : Type)
  (B_has_l_un_op : HasLUnOp B) (A_B_has_r_act : HasRAct A B) : Prop :=
  two_l_bin_comm : forall (x : B) (a : A), L- (x R+ a) = (L- x) R+ a.
