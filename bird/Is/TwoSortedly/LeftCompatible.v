From Maniunfold.Has Require Export
  OneSorted.BinaryOperation TwoSorted.LeftAction.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Class IsLCompat {A B : Type}
  (A_has_bin_op : HasBinOp A) (A_B_has_l_act : HasLAct A B) : Prop :=
  l_compat : forall (a b : A) (x : B), a L+ (b L+ x) = (a + b) L+ x.
