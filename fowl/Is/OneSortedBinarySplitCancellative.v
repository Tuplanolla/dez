(* bad *)
From Maniunfold.Has Require Export
  Negation Multiplication.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations.

Class IsBinSptCancel (A : Type)
  `(HasNeg A) `(HasMul A) : Prop :=
  bin_spt_cancel : forall x y : A, (- x) * (- y) = x * y.
