From Maniunfold.Has Require Export
  BinaryOperation RightAction.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations TwoSorted.AdditiveNotations.

Class IsRCompat (A B : Type)
  (A_has_bin_op : HasBinOp A) (A_B_has_r_act : HasRAct A B) : Prop :=
  r_compat : forall (a b : A) (x : B), x R+ (a + b) = (x R+ a) R+ b.
