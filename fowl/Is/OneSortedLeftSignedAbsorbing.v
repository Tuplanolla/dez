(* bad *)
From Maniunfold.Has Require Export
  Negation Multiplication One.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations.

Class IsLSgnAbsorb (A : Type)
  `(HasNeg A) `(HasMul A)
  `(HasOne A) : Prop :=
  l_sgn_absorb : forall x : A, (- (1)) * x = - x.
