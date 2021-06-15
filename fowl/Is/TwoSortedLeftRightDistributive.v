(* bad *)
From Maniunfold.Has Require Export
  Addition Action.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations TwoSortedMultiplicativeNotations.

Local Open Scope ring_scope.
Local Open Scope l_mod_scope.

Class IsTwoLRDistr (A B : Type)
  `(HasAdd A) `(HasAdd B)
  `(HasActL A B) : Prop :=
  two_l_r_distr : forall (a b : A) (x : B), (a + b) * x = a * x + b * x.
