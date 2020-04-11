(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Addition TwoSorted.LeftAction.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations TwoSorted.MultiplicativeNotations.

Local Open Scope l_mod_scope.

Class IsTwoLRDistr (A B : Type)
  (A_has_add : HasAdd A) (B_has_add : HasAdd B)
  (A_B_has_l_act : HasLAct A B) : Prop :=
  two_l_r_distr : forall (a b : A) (x : B), (a + b) * x = a * x + b * x.
