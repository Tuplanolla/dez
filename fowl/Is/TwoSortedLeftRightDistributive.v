(* bad *)
From DEZ.Has Require Export
  Addition Action.
From DEZ.ShouldHave Require Import
  OneSortedArithmeticNotations TwoSortedMultiplicativeNotations.

Local Open Scope ring_scope.
Local Open Scope l_mod_scope.

Class IsTwoLDistrR (A B : Type)
  `(HasAdd A) `(HasAdd B)
  `(HasActL A B) : Prop :=
  two_l_distr_r : forall (a b : A) (x : B), (a + b) * x = a * x + b * x.
