From Maniunfold.Has Require Export
  OneSortedAddition OneSortedMultiplication.
From Maniunfold.Is Require Export
  OneSortedLeftDistributive OneSortedRightDistributive.

Class IsDistr (A : Type)
  `(HasAdd A) `(HasMul A) : Prop := {
  A_add_mul_is_l_distr :> IsLDistr add mul;
  A_add_mul_is_r_distr :> IsRDistr add mul;
}.
