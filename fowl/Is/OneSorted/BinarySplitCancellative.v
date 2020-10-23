(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Negation OneSorted.Multiplication.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsBinSptCancel (A : Type)
  `(HasNeg A) `(HasMul A) : Prop :=
  bin_spt_cancel : forall x y : A, (- x) * (- y) = x * y.
