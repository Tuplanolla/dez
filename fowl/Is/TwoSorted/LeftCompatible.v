(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation TwoSorted.LeftAction.
From Maniunfold.ShouldHave Require Import
  TwoSorted.MultiplicativeNotations.

Local Open Scope l_mod_scope.

Class IsLCompat (A B : Type)
  `(HasBinOp A) `(HasLAct A B) : Prop :=
  l_compat : forall (a b : A) (x : B), a * (b * x) = (a * b) * x.
