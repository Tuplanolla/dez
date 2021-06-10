(* bad *)
From Maniunfold.Has Require Export
  OneSortedAddition TwoSortedRightAction.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations TwoSortedMultiplicativeNotations.

Local Open Scope grp_scope.
Local Open Scope r_mod_scope.

Class IsTwoRRDistr (A B : Type)
  `(HasAdd B) `(HasRAct A B) : Prop :=
  two_r_r_distr : forall (a : A) (x y : B), (x + y) * a = x * a + y * a.
