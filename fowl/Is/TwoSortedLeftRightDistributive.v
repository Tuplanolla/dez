(* bad *)
From Maniunfold.Has Require Export
  OneSortedAddition TwoSortedLeftAction.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations TwoSortedMultiplicativeNotations.

Local Open Scope grp_scope.
Local Open Scope l_mod_scope.

Class IsTwoLRDistr (A B : Type)
  `(HasAdd A) `(HasAdd B)
  `(HasLAct A B) : Prop :=
  two_l_r_distr : forall (a b : A) (x : B), (a + b) * x = a * x + b * x.
