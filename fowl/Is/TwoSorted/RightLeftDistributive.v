(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Addition TwoSorted.RightAction.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations TwoSorted.MultiplicativeNotations.

Local Open Scope r_mod_scope.

Class IsTwoRLDistr (A B : Type)
  `(HasAdd A) `(HasAdd B)
  `(HasRAct A B) : Prop :=
  two_r_l_distr : forall (a b : A) (x : B), x * (a + b) = x * a + x * b.
