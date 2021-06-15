(* bad *)
From Maniunfold.Has Require Export
  Zero Multiplication.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations.

Class IsRAbsorb (A : Type)
  `(HasZero A) `(HasMul A) : Prop :=
  r_absorb : forall x : A, x * 0 = 0.
