(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Addition TwoSorted.RightAction.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations TwoSorted.MultiplicativeNotations.

Local Open Scope r_act_scope.

Class IsTwoRLDistr (A B : Type)
  (A_has_add : HasAdd A) (B_has_add : HasAdd B)
  (A_B_has_r_act : HasRAct A B) : Prop :=
  two_r_l_distr : forall (a b : A) (x : B), x * (a + b) = x * a + x * b.
