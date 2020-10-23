(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Addition TwoSorted.LeftAction.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations TwoSorted.MultiplicativeNotations.

Local Open Scope l_mod_scope.

Class IsTwoLLDistr (A B : Type)
  `(HasAdd B) `(HasLAct A B) : Prop :=
  two_l_l_distr : forall (a : A) (x y : B), a * (x + y) = a * x + a * y.
