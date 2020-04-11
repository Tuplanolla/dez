(* bad *)
From Maniunfold.Has Require Export
  OneSorted.NullaryOperation TwoSorted.LeftAction.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations TwoSorted.AdditiveNotations.

Local Open Scope l_mod_scope.

Class IsTwoLUnl (A B : Type)
  (A_has_null_op : HasNullOp A) (A_B_has_l_act : HasLAct A B) : Prop :=
  two_l_unl : forall x : B, 0 + x = x.
