(* bad *)
From Maniunfold.Has Require Export
  OneSortedAddition TwoSortedRightAction.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations TwoSortedMultiplicativeNotations.

Local Open Scope r_mod_scope.

Class IsTwoRLDistr (A B : Type)
  `(HasAdd A) `(HasAdd B)
  `(HasRAct A B) : Prop :=
  two_r_l_distr : forall (a b : A) (x : B), x * (a + b) = x * a + x * b.
