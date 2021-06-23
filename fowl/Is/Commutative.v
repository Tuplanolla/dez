(* * Commutativity of a Binary Operation *)

From Maniunfold.Has Require Export
  BinaryOperation.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Class IsComm (A : Type) (Hk : HasBinOp A) : Prop :=
  comm (x y : A) : x + y = y + x.
