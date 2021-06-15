(* bad *)
From Maniunfold.Has Require Export
  BinaryOperation UnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

Class IsUnDistr (A : Type)
  `(HasBinOp A) `(HasUnOp A) : Prop :=
  un_distr : forall x y : A, - (x + y) = - x + - y.
