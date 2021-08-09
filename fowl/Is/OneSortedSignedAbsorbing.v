From DEZ.Has Require Export
  Negation Multiplication One.
From DEZ.Is Require Export
  OneSortedLeftSignedAbsorbing OneSortedRightSignedAbsorbing.

Class IsSgnAbsorb (A : Type) `(HasNeg A)
  `(HasMul A) `(HasOne A) : Prop := {
  A_neg_mul_one_is_l_sgn_absorb :> IsLSgnAbsorb neg mul one;
  A_neg_mul_one_is_r_sgn_absorb :> IsRSgnAbsorb neg mul one;
}.
