(* bad *)
From Maniunfold.Has Require Export
  OneSortedBinaryOperation OneSortedUnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

Class IsUnAntidistr (A : Type)
  `(HasBinOp A) `(HasUnOp A) : Prop :=
  un_antidistr : forall x y : A, - (x + y) = - y + - x.
