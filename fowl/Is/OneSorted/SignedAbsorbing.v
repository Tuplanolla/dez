From Maniunfold.Has Require Export
  OneSorted.Negation OneSorted.Multiplication OneSorted.One.
From Maniunfold.Is Require Export
  OneSorted.LeftSignedAbsorbing OneSorted.RightSignedAbsorbing.

Class IsSgnAbsorb (A : Type) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A) : Prop := {
  A_neg_mul_one_is_l_sgn_absorb :> IsLSgnAbsorb A neg mul one;
  A_neg_mul_one_is_r_sgn_absorb :> IsRSgnAbsorb A neg mul one;
}.