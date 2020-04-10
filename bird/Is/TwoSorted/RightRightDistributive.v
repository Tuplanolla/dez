(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Addition TwoSorted.RightAction.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations TwoSorted.MultiplicativeNotations.

Local Open Scope r_act_scope.

Class IsTwoRRDistr (A B : Type)
  (B_has_add : HasAdd B) (A_B_has_r_act : HasRAct A B) : Prop :=
  two_r_r_distr : forall (a : A) (x y : B), (x + y) * a = x * a + y * a.
