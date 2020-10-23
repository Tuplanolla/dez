(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.UnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class IsUnDistr (A : Type)
  `(HasBinOp A) `(HasUnOp A) : Prop :=
  un_distr : forall x y : A, - (x + y) = - x + - y.
