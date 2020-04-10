(* bad *)
From Maniunfold.Has Require Export
  OneSorted.NullaryOperation TwoSorted.RightAction.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations TwoSorted.AdditiveNotations.

Local Open Scope r_act_scope.

Class IsTwoRUnl (A B : Type)
  (A_has_null_op : HasNullOp A) (A_B_has_r_act : HasRAct A B) : Prop :=
  two_r_unl : forall x : B, x + 0 = x.
