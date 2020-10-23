From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Multiplication.
From Maniunfold.Is Require Export
  OneSorted.LeftDistributive OneSorted.RightDistributive.

Class IsDistr (A : Type)
  `(HasAdd A) `(HasMul A) : Prop := {
  A_add_mul_is_l_distr :> IsLDistr add mul;
  A_add_mul_is_r_distr :> IsRDistr add mul;
}.
