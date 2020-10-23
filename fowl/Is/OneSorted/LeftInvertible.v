(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  OneSorted.UnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class IsLInv (A : Type) `(HasBinOp A)
  `(HasNullOp A) `(HasUnOp A) : Prop :=
  l_inv : forall x : A, (- x) + x = 0.
