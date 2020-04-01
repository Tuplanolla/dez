From Maniunfold.Has Require Export
  OneSorted.Addition TwoSorted.RightAction.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations TwoSorted.MultiplicativeNotations.

Class IsTwoRLDistr (A B : Type)
  (A_has_add : HasAdd A) (B_has_add : HasAdd B)
  (A_B_has_r_act : HasRAct A B) : Prop :=
  two_r_l_distr : forall (a b : A) (x : B), x R* (a + b) = x R* a + x R* b.
