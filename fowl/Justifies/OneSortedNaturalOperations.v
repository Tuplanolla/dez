From Coq Require Import
  NArith.NArith.
From DEZ.Has Require Export
  NullaryOperation BinaryOperation Action.
From DEZ.Is Require Export
  Monoid.
From DEZ.Justifies Require Export
  OneSortedPositiveOperations.
From DEZ.Supports Require Import
  OneSortedAdditivePositiveOperationNotations.

Section Context.

Context (A : Type) (Hx : HasNullOp A) (Hk : HasBinOp A) `(IsMon A).

Fixpoint nat_op (n : nat) (x : A) : A :=
  match n with
  | O => 0
  | S p => x + @nat_op p x
  end.

Global Instance nat_A_has_act_l : HasActL nat A := nat_op.

Definition n_op (n : N) (x : A) : A :=
  match n with
  | N0 => 0
  | Npos p => (p * x)%positive
  end.

Global Instance N_A_has_act_l : HasActL N A := n_op.

End Context.

Arguments nat_op {_} _ _ !_ _.
Arguments n_op {_} _ _ !_ _.
