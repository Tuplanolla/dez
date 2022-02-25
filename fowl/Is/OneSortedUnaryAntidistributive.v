(* bad *)
From DEZ.Has Require Export
  BinaryOperation UnaryOperation.
From DEZ.Supports Require Import
  OneSortedAdditiveNotations.

Class IsUnAntidistr (A : Type)
  `(HasBinOp A) `(HasUnOp A) : Prop :=
  un_antidistr : forall x y : A, - (x + y) = - y + - x.
