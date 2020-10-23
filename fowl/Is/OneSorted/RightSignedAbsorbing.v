(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Negation OneSorted.Multiplication OneSorted.One.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsRSgnAbsorb (A : Type)
  `(HasNeg A) `(HasMul A)
  `(HasOne A) : Prop :=
  r_sgn_absorb : forall x : A, x * (- (1)) = - x.
