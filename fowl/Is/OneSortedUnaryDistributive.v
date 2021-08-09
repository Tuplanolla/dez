(* bad *)
From DEZ.Has Require Export
  BinaryOperation UnaryOperation.
From DEZ.ShouldHave Require Import
  OneSortedAdditiveNotations.

Class IsUnDistr (A : Type)
  `(HasBinOp A) `(HasUnOp A) : Prop :=
  un_distr : forall x y : A, - (x + y) = - x + - y.
