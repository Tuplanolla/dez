(* bad *)
From DEZ.Has Require Export
  Addition Action.
From DEZ.ShouldHave Require Import
  OneSortedArithmeticNotations TwoSortedMultiplicativeNotations.

Local Open Scope ring_scope.
Local Open Scope r_mod_scope.

Class IsTwoRDistrR (A B : Type)
  `(HasAdd B) `(HasActR A B) : Prop :=
  two_r_distr_r : forall (a : A) (x y : B), (x + y) * a = x * a + y * a.
