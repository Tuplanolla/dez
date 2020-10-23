(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.UnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class IsUnAntidistr (A : Type)
  `(HasBinOp A) `(HasUnOp A) : Prop :=
  un_antidistr : forall x y : A, - (x + y) = - y + - x.
