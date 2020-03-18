From Maniunfold.Has Require Export
  OneSorted.Negation OneSorted.Multiplication OneSorted.One.
From Maniunfold.Is Require Export
  OneSortedly.LeftSignedAbsorbing OneSortedly.RightSignedAbsorbing.

Class IsSgnAbsorb {A : Type}
  (has_neg : HasNeg A) (has_mul : HasMul A) (has_one : HasOne A) : Prop := {
  neg_mul_one_is_l_sgn_absorb :> IsLSgnAbsorb neg mul one;
  neg_mul_one_is_r_sgn_absorb :> IsRSgnAbsorb neg mul one;
}.
