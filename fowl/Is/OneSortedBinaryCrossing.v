(* bad *)
From DEZ.Has Require Export
  Negation Multiplication.
From DEZ.Supports Require Import
  OneSortedArithmeticNotations.

Class IsBinCrs (A : Type)
  `(HasNeg A) `(HasMul A) : Prop :=
  bin_crs : forall x y : A, (- x) * y = x * (- y).
