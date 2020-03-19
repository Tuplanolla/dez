From Maniunfold.Has Require Export
  OneSorted.Addition TwoSorted.LeftAction.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations TwoSorted.MultiplicativeNotations.

Class IsTwoLLDistr {A B : Type}
  (A_has_add : HasAdd B) (A_B_has_l_act : HasLAct A B) : Prop :=
  two_l_l_distr : forall (a : A) (x y : B), a L* (x + y) = a L* x + a L* y.
