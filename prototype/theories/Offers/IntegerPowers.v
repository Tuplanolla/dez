From Coq Require Import
  ZArith.
From Maniunfold.Has Require Export
  BinaryOperation Unit UnaryOperation.
From Maniunfold.Offers Require Import
  PositivePowers.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Definition z_op {A : Type} {has_bin_op : HasBinOp A}
  {has_un : HasUn A} {has_un_op : HasUnOp A}
  (n : Z) (x : A) : A :=
  match n with
  | Z0 => 0
  | Zpos p => positive_op p x
  | Zneg p => - positive_op p x
  end.
