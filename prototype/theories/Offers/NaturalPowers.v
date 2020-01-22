From Coq Require Import
  NArith.
From Maniunfold.Has Require Export
  BinaryOperation Unit.
From Maniunfold.Offers Require Import
  PositivePowers.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Fixpoint nat_op {A : Type} {has_bin_op : HasBinOp A} {has_un : HasUn A}
  (n : nat) (x : A) : A :=
  match n with
  | O => 0
  | S p => x + nat_op p x
  end.

Definition n_op {A : Type} {has_bin_op : HasBinOp A} {has_un : HasUn A}
  (n : N) (x : A) : A :=
  match n with
  | N0 => 0
  | Npos p => positive_op p x
  end.
