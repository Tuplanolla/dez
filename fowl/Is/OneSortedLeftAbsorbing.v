(* bad *)
From Maniunfold.Has Require Export
  OneSortedZero OneSortedMultiplication.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations.

Class IsLAbsorb (A : Type)
  `(HasZero A) `(HasMul A) : Prop :=
  l_absorb : forall x : A, 0 * x = 0.
