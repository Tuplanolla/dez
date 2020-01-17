From Coq Require Import
  ZArith.
From Maniunfold.Has Require Export
  BinaryOperation Unit.
From Maniunfold.Offers Require Import
  PositivePowers.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Definition nop {A : Type} {has_bi_op : HasBinOp A}
  {has_un : HasUn A} (n : N) (x : A) : A :=
  match n with
  | N0 => 0
  | Npos p => pop p x
  end.
