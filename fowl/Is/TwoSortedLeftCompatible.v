(* bad *)
From Maniunfold.Has Require Export
  BinaryOperation Action.
From Maniunfold.ShouldHave Require Import
  TwoSortedMultiplicativeNotations.

Local Open Scope l_mod_scope.

Class IsLCompat (A B : Type)
  `(HasBinOp A) `(HasActL A B) : Prop :=
  l_compat : forall (a b : A) (x : B), a * (b * x) = (bin_op a b) * x.
