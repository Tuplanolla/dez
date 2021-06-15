(* bad *)
From Maniunfold.Has Require Export
  Negation Multiplication One.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations.

Class IsRSgnAbsorb (A : Type)
  `(HasNeg A) `(HasMul A)
  `(HasOne A) : Prop :=
  r_sgn_absorb : forall x : A, x * (- (1)) = - x.
