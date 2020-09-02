(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation TwoSorted.RightAction.
From Maniunfold.ShouldHave Require Import
  TwoSorted.MultiplicativeNotations.

Local Open Scope r_mod_scope.

Class IsRCompat (A B : Type)
  (A_has_bin_op : HasBinOp A) (A_B_has_r_act : HasRAct A B) : Prop :=
  r_compat : forall (x : B) (a b : A), x * (a * b) = (x * a) * b.
