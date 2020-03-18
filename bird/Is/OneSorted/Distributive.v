From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Multiplication.
From Maniunfold.Is Require Export
  OneSorted.LeftDistributive OneSorted.RightDistributive.

Class IsDistr {A : Type}
  (A_has_add : HasAdd A) (has_mul : HasMul A) : Prop := {
  add_mul_is_l_distr :> IsLDistr add mul;
  add_mul_is_r_distr :> IsRDistr add mul;
}.
