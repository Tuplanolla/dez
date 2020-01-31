From Maniunfold.Has Require Export
  EquivalenceRelation Addition Multiplication.
From Maniunfold.Is Require Export
  LeftDistributive RightDistributive.

Class IsDistr {A : Type} {has_eq_rel : HasEqRel A}
  (has_add : HasAdd A) (has_mul : HasMul A) : Prop := {
  add_mul_is_l_distr :> IsLDistr add mul;
  add_mul_is_r_distr :> IsRDistr add mul;
}.
