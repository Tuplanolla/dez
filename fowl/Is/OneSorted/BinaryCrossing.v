(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Negation OneSorted.Multiplication.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsBinCrs (A : Type)
  `(HasNeg A) `(HasMul A) : Prop :=
  bin_crs : forall x y : A, (- x) * y = x * (- y).
