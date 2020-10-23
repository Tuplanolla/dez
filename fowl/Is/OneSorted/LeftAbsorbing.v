(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Zero OneSorted.Multiplication.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsLAbsorb (A : Type)
  `(HasZero A) `(HasMul A) : Prop :=
  l_absorb : forall x : A, 0 * x = 0.
