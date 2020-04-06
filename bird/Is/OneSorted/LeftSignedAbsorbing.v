(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Negation OneSorted.Multiplication OneSorted.One.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsLSgnAbsorb {A : Type}
  (A_has_neg : HasNeg A) (A_has_mul : HasMul A)
  (A_has_one : HasOne A) : Prop :=
  l_sgn_absorb : forall x : A, (- (1)) * x = - x.
