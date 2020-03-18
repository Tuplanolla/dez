From Maniunfold.Has Require Export
  OneSorted.RightUnaryOperation TwoSorted.LeftAction.
From Maniunfold.ShouldHave Require Import
  TwoSorted.AdditiveNotations.

Class IsRExtBinComm {A B : Type}
  (B_has_r_un_op : HasRUnOp B) (A_B_has_l_act : HasLAct A B) : Prop :=
  r_ext_bin_comm : forall (a : A) (x : B), R- (a L+ x) = a L+ (R- x).
