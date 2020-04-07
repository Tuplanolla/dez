(* bad *)
From Maniunfold.Has Require Export
  OneSorted.UnaryOperation TwoSorted.RightAction.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations TwoSorted.AdditiveNotations.

Class IsTwoLBinComm (A B : Type)
  (B_has_un_op : HasUnOp B) (A_B_has_r_act : HasRAct A B) : Prop :=
  two_l_bin_comm : forall (x : B) (a : A), - (x R+ a) = (- x) R+ a.
