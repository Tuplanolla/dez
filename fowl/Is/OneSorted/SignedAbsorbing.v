From Maniunfold.Has Require Export
  OneSorted.Negation OneSorted.Multiplication OneSorted.One.
From Maniunfold.Is Require Export
  OneSorted.LeftSignedAbsorbing OneSorted.RightSignedAbsorbing.

Class IsSgnAbsorb (A : Type) `(HasNeg A)
  `(HasMul A) `(HasOne A) : Prop := {
  A_neg_mul_one_is_l_sgn_absorb :> IsLSgnAbsorb neg mul one;
  A_neg_mul_one_is_r_sgn_absorb :> IsRSgnAbsorb neg mul one;
}.
