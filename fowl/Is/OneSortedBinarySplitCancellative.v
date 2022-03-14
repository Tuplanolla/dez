(* bad *)
From DEZ.Has Require Export
  ArithmeticOperations.
From DEZ.Supports Require Import
  OneSortedArithmeticNotations.

Class IsBinSptCancel (A : Type)
  `(HasNeg A) `(HasMul A) : Prop :=
  bin_spt_cancel : forall x y : A, (- x) * (- y) = x * y.
