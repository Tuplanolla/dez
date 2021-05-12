(* bad *)
From Maniunfold.Has Require Export
  OneSortedBinaryOperation TwoSortedLeftAction.
From Maniunfold.ShouldHave Require Import
  TwoSortedMultiplicativeNotations.

Local Open Scope l_mod_scope.

Class IsLCompat (A B : Type)
  `(HasBinOp A) `(HasLAct A B) : Prop :=
  l_compat : forall (a b : A) (x : B), a * (b * x) = (a * b) * x.
