(* bad *)
From DEZ.Has Require Export
  Addition Action.
From DEZ.ShouldHave Require Import
  OneSortedArithmeticNotations TwoSortedMultiplicativeNotations.

Local Open Scope ring_scope.
Local Open Scope r_mod_scope.

Class IsTwoRDistrL (A B : Type)
  `(HasAdd A) `(HasAdd B)
  `(HasActR A B) : Prop :=
  two_r_distr_l : forall (a b : A) (x : B), x * (a + b) = x * a + x * b.
