(* bad *)
From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation
  UnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

Class IsRInv (A : Type) `(HasBinOp A)
  `(HasNullOp A) `(HasUnOp A) : Prop :=
  r_inv : forall x : A, x + (- x) = 0.
