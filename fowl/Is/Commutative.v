(* * Commutativity of a Binary Operation *)

From Maniunfold.Has Require Export
  BinaryOperation.
From Maniunfold.ShouldHave Require Import
  MultiplicativeNotations.

(** This has the same shape as [mul_comm]. *)

Class IsComm (A : Type) (Hk : HasBinOp A) : Prop :=
  comm (x y : A) : x * y = y * x.
