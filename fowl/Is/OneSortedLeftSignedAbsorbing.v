(* bad *)
From Maniunfold.Has Require Export
  OneSortedNegation OneSortedMultiplication OneSortedOne.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations.

Class IsLSgnAbsorb (A : Type)
  `(HasNeg A) `(HasMul A)
  `(HasOne A) : Prop :=
  l_sgn_absorb : forall x : A, (- (1)) * x = - x.
