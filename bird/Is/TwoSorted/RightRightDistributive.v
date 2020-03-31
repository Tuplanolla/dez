From Maniunfold.Has Require Export
  OneSorted.Addition TwoSorted.RightAction.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations TwoSorted.MultiplicativeNotations.

Class IsTwoRRDistr {A B : Type}
  (A_has_add : HasAdd B) (A_B_has_r_act : HasRAct A B) : Prop :=
  two_r_r_distr : forall (a : A) (x y : B), (x + y) R* a = x R* a + y R* a.
