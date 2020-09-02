(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation TwoSorted.LeftAction.
From Maniunfold.ShouldHave Require Import
  TwoSorted.MultiplicativeNotations.

Local Open Scope l_mod_scope.

Class IsLCompat (A B : Type)
  (A_has_bin_op : HasBinOp A) (A_B_has_l_act : HasLAct A B) : Prop :=
  l_compat : forall (a b : A) (x : B), a * (b * x) = (a * b) * x.
