(* bad *)
From Maniunfold.Has Require Export
  OneSortedNegation OneSortedMultiplication OneSortedOne.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations.

Class IsRSgnAbsorb (A : Type)
  `(HasNeg A) `(HasMul A)
  `(HasOne A) : Prop :=
  r_sgn_absorb : forall x : A, x * (- (1)) = - x.
