(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Negation OneSorted.Multiplication OneSorted.One.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsRSgnAbsorb (A : Type)
  (A_has_neg : HasNeg A) (A_has_mul : HasMul A)
  (A_has_one : HasOne A) : Prop :=
  r_sgn_absorb : forall x : A, x * (- (1)) = - x.
