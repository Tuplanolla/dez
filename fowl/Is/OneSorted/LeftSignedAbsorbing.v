(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Negation OneSorted.Multiplication OneSorted.One.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsLSgnAbsorb (A : Type)
  `(HasNeg A) `(HasMul A)
  `(HasOne A) : Prop :=
  l_sgn_absorb : forall x : A, (- (1)) * x = - x.
