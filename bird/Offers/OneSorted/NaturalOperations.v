From Coq Require Import
  NArith.NArith.
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation TwoSorted.LeftAction.
From Maniunfold.Offers Require Export
  OneSorted.PositiveOperations.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Section Context.

Context {A : Type} {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}.

Fixpoint nat_op (n : nat) (x : A) : A :=
  match n with
  | O => 0
  | S p => x + nat_op p x
  end.

Global Instance nat_A_has_l_act : HasLAct nat A := nat_op.

Definition n_op (n : N) (x : A) : A :=
  match n with
  | N0 => 0
  | Npos p => positive_op p x
  end.

Global Instance N_A_has_l_act : HasLAct N A := n_op.

End Context.
