(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Zero OneSorted.Multiplication.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsRAbsorb (A : Type)
  `(HasZero A) `(HasMul A) : Prop :=
  r_absorb : forall x : A, x * 0 = 0.
