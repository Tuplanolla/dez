From Maniunfold.Has Require Export
  OneSorted.RightUnaryOperation TwoSorted.LeftAction.
From Maniunfold.ShouldHave Require Import
  TwoSorted.AdditiveNotations.

Class IsTwoRBinComm (A B : Type)
  (B_has_r_un_op : HasRUnOp B) (A_B_has_l_act : HasLAct A B) : Prop :=
  two_r_bin_comm : forall (a : A) (x : B), R- (a L+ x) = a L+ (R- x).
