From Coq Require Import
  NArith.
From Maniunfold.Has Require Export
  BinaryOperation Unit.
From Maniunfold.Offers Require Import
  PositivePowers.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Definition n_op {A : Type} {has_bin_op : HasBinOp A} {has_un : HasUn A}
  (n : N) (x : A) : A :=
  match n with
  | N0 => 0
  | Npos p => p_op p x
  end.
