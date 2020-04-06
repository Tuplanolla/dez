(* bad *)
From Maniunfold.Has Require Export
  OneSorted.RightNullaryOperation TwoSorted.RightAction.
From Maniunfold.ShouldHave Require Import
  TwoSorted.AdditiveNotations.

Class IsTwoRUnl (A B : Type)
  (A_has_r_null_op : HasRNullOp A) (A_B_has_r_act : HasRAct A B) : Prop :=
  two_r_unl : forall x : B, x R+ R0 = x.
