From Coq Require Import
  NArith.
From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation LeftAction.
From Maniunfold.Offers Require Import
  PositivePowers.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Section Context.

Context {A : Type} `{has_bin_op : HasBinOp A} `{has_un : HasNullOp A}.

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
