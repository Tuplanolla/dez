(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Negation OneSorted.Multiplication.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsBinCrs {A : Type}
  (A_has_neg : HasNeg A) (A_has_mul : HasMul A) : Prop :=
  bin_crs : forall x y : A, (- x) * y = x * (- y).
