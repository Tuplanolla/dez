(* bad *)
From DEZ.Has Require Export
  BinaryOperation Action.
From DEZ.Supports Require Import
  TwoSortedMultiplicativeNotations.

Local Open Scope r_mod_scope.

Class IsRCompat (A B : Type)
  `(HasBinOp A) `(HasActR A B) : Prop :=
  r_compat : forall (x : B) (a b : A), x * (bin_op a b) = (x * a) * b.
