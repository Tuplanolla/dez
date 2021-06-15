(* bad *)
From Maniunfold.Has Require Export
  OneSortedAddition Action.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations TwoSortedMultiplicativeNotations.

Local Open Scope grp_scope.
Local Open Scope r_mod_scope.

Class IsTwoRLDistr (A B : Type)
  `(HasAdd A) `(HasAdd B)
  `(HasActR A B) : Prop :=
  two_r_l_distr : forall (a b : A) (x : B), x * (a + b) = x * a + x * b.
