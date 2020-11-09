From Coq Require Import
  NArith.NArith.
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation TwoSorted.LeftAction.
From Maniunfold.Offers Require Export
  OneSorted.PositiveOperations.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Section Context.

Context (A : Type) `(HasBinOp A) `(HasNullOp A).

Fixpoint nat_op (n : nat) (x : A) : A :=
  match n with
  | O => 0
  | S p => x + @nat_op p x
  end.

Global Arguments nat_op !_ _.

Global Instance nat_A_has_l_act : HasLAct nat A := nat_op.

Definition n_op (n : N) (x : A) : A :=
  match n with
  | N0 => 0
  | Npos p => positive_op _+_ p x
  end.

Global Instance N_A_has_l_act : HasLAct N A := n_op.

Global Arguments n_op !_ _.

End Context.
