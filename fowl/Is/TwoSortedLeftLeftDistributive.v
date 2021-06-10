(* bad *)
From Maniunfold.Has Require Export
  OneSortedAddition TwoSortedLeftAction.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations TwoSortedMultiplicativeNotations.

Local Open Scope grp_scope.
Local Open Scope l_mod_scope.

Class IsTwoLLDistr (A B : Type)
  `(HasAdd B) `(HasLAct A B) : Prop :=
  two_l_l_distr : forall (a : A) (x y : B), a * (x + y) = a * x + a * y.
