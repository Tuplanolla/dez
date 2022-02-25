(* bad *)
From DEZ.Has Require Export
  Negation Multiplication One.
From DEZ.Supports Require Import
  OneSortedArithmeticNotations.

Class IsLSgnAbsorb (A : Type)
  `(HasNeg A) `(HasMul A)
  `(HasOne A) : Prop :=
  l_sgn_absorb : forall x : A, (- (1)) * x = - x.
