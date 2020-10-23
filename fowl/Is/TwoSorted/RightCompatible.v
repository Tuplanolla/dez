(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation TwoSorted.RightAction.
From Maniunfold.ShouldHave Require Import
  TwoSorted.MultiplicativeNotations.

Local Open Scope r_mod_scope.

Class IsRCompat (A B : Type)
  `(HasBinOp A) `(HasRAct A B) : Prop :=
  r_compat : forall (x : B) (a b : A), x * (a * b) = (x * a) * b.
